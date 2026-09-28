package checker

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"

	"fluent/bound"
)

// none — «нет терма» (например, нет self для specTerm вне close).
const none term = -1

// ---- конструкторы термов ----

// field — терм поля f значения base.
func (fc *funcChecker) field(base term, f *types.Var) term {
	return fc.bank.App("."+f.Name(), base)
}

// idx — терм индексного параметра p значения base.
func (fc *funcChecker) idx(base term, p *bound.Param) term {
	return fc.bank.App(p.Owner.Pkg().Path()+"."+p.Owner.Name()+"<"+p.Name+">", base)
}

// deref — терм значения *p.
func (fc *funcChecker) deref(p term) term {
	return fc.bank.App("*", p)
}

func (fc *funcChecker) constant(v constant.Value) term {
	return fc.bank.Const(v.ExactString())
}

func (fc *funcChecker) nilTerm() term { return fc.bank.Const("nil") }

// ---- выражения ----

// expr вычисляет терм значения выражения (и проверяет вызовы внутри него).
func (fc *funcChecker) expr(e ast.Expr) term {
	if tv, ok := fc.info.Types[e]; ok && tv.Value != nil {
		return fc.constant(tv.Value)
	}
	switch e := e.(type) {
	case *ast.ParenExpr:
		return fc.expr(e.X)
	case *ast.Ident:
		switch obj := fc.info.Uses[e].(type) {
		case *types.Nil:
			return fc.nilTerm()
		case *types.Var:
			if t, ok := fc.fl.cur[obj]; ok {
				return t
			}
		}
		return fc.fresh(e.Name) // глобальные и захваченные переменные, функции
	case *ast.SelectorExpr:
		return fc.selector(e)
	case *ast.CallExpr:
		if rs := fc.call(e); len(rs) > 0 {
			return rs[0]
		}
		return fc.fresh("void")
	case *ast.CompositeLit:
		return fc.compositeLit(e)
	case *ast.UnaryExpr:
		switch e.Op {
		case token.AND:
			// &x: *p ≈ x. Индексы x стабильны, поэтому это верно и дальше.
			x := fc.expr(e.X)
			p := fc.fresh("&" + types.ExprString(e.X))
			fc.fl.st.AssertEqual(fc.deref(p), x)
			return p
		}
		fc.expr(e.X)
	case *ast.StarExpr:
		return fc.deref(fc.expr(e.X))
	case *ast.FuncLit:
		fc.checkFunc(fc.info.TypeOf(e).(*types.Signature), e.Body, nil)
	case *ast.BinaryExpr:
		fc.expr(e.X)
		fc.expr(e.Y)
	case *ast.IndexExpr:
		fc.expr(e.X)
		fc.expr(e.Index)
	case *ast.IndexListExpr:
		fc.expr(e.X)
	case *ast.SliceExpr:
		for _, x := range []ast.Expr{e.X, e.Low, e.High, e.Max} {
			if x != nil {
				fc.expr(x)
			}
		}
	case *ast.TypeAssertExpr:
		fc.expr(e.X)
	case *ast.KeyValueExpr:
		fc.expr(e.Value)
	}
	return fc.fresh("expr")
}

func (fc *funcChecker) selector(e *ast.SelectorExpr) term {
	sel := fc.info.Selections[e]
	if sel == nil || sel.Kind() != types.FieldVal || len(sel.Index()) != 1 {
		// pkg.X, method value, поле встроенной структуры — значение неизвестно.
		if sel != nil {
			fc.expr(e.X)
		}
		return fc.fresh(types.ExprString(e))
	}
	xt := fc.info.TypeOf(e.X)
	viaPtr := isPointer(xt)
	base := fc.expr(e.X)
	if viaPtr {
		base = fc.deref(base)
	}
	stable := !viaPtr
	if root := fc.rootVar(e.X); root == nil || fc.addrTaken[root] {
		stable = false
	}
	return fc.fieldRead(base, derefType(xt), sel.Obj().(*types.Var), stable)
}

// fieldRead — терм поля f значения base типа st. Индексы стабильны всегда;
// обычное поле стабильно, только если значение не может измениться через
// указатель (stable), иначе каждое чтение даёт свежий терм.
// Инварианты equals/close становятся фактами при чтении.
func (fc *funcChecker) fieldRead(base term, st types.Type, f *types.Var, stable bool) term {
	var fa *bound.Field
	if s := fc.specs.StructOf(st); s != nil {
		for _, x := range s.Fields {
			if x.Var == f {
				fa = x
			}
		}
	}
	if fa != nil && fa.Equals != nil {
		return fc.idx(base, fa.Equals)
	}
	ft := fc.field(base, f)
	if !stable {
		ft = fc.fresh(f.Name())
	}
	if fa != nil && fa.Close != nil {
		target := fc.specs.Bounded(f.Type())
		for i, arg := range fa.Close {
			fc.fl.st.AssertEqual(fc.idx(ft, target.Params[i]), fc.specTerm(arg, nil, base))
		}
	}
	return ft
}

// specTerm переводит терм спецификации в терм состояния. vars — значения
// параметров функции, self — значение структуры (для параметров внутри close).
func (fc *funcChecker) specTerm(e bound.Expr, vars map[*types.Var]term, self term) term {
	switch e := e.(type) {
	case *bound.Var:
		if t, ok := vars[e.Obj]; ok {
			return t
		}
		return fc.fresh(e.Obj.Name())
	case *bound.Const:
		if e.Val == nil {
			return fc.nilTerm()
		}
		return fc.constant(e.Val)
	case *bound.FieldOf:
		x := fc.specTerm(e.X, vars, self)
		t := e.X.Type()
		if isPointer(t) {
			return fc.fieldRead(fc.deref(x), derefType(t), e.Field, false)
		}
		return fc.fieldRead(x, t, e.Field, true)
	case *bound.ParamOf:
		x := fc.specTerm(e.X, vars, self)
		if isPointer(e.X.Type()) {
			x = fc.deref(x)
		}
		return fc.idx(x, e.Param)
	case *bound.SelfParam:
		return fc.idx(self, e.Param)
	}
	panic("unreachable")
}

// ---- вызовы ----

// call вычисляет вызов, проверяет requires и возвращает термы результатов
// с фактами из returns.
func (fc *funcChecker) call(call *ast.CallExpr) []term {
	fun := ast.Unparen(call.Fun)
	tv := fc.info.Types[fun]
	if tv.IsType() && len(call.Args) == 1 {
		return []term{fc.expr(call.Args[0])} // конверсия не меняет значение
	}

	var fn *types.Func
	var recvExpr ast.Expr
	args := call.Args
	switch f := fun.(type) {
	case *ast.Ident:
		fn, _ = fc.info.Uses[f].(*types.Func)
	case *ast.SelectorExpr:
		if sel := fc.info.Selections[f]; sel != nil {
			switch {
			case sel.Kind() == types.MethodVal && len(sel.Index()) == 1:
				fn, recvExpr = sel.Obj().(*types.Func), f.X
			case sel.Kind() == types.MethodExpr && len(sel.Index()) == 1 && len(args) > 0:
				fn, recvExpr, args = sel.Obj().(*types.Func), args[0], args[1:]
			default:
				fc.expr(f.X)
			}
		} else {
			fn, _ = fc.info.Uses[f.Sel].(*types.Func)
		}
	default:
		fc.expr(fun)
	}

	var sig *types.Signature
	if fn != nil {
		sig = fn.Type().(*types.Signature)
	} else if s, ok := tv.Type.(*types.Signature); ok {
		sig = s // вызов значения-функции: контракта нет
	}

	vars := map[*types.Var]term{}
	names := map[*types.Var]string{}
	if recvExpr != nil {
		recv := sig.Recv()
		t := fc.expr(recvExpr)
		have, want := isPointer(fc.info.TypeOf(recvExpr)), isPointer(recv.Type())
		switch {
		case want && !have: // неявный &x
			p := fc.fresh("&" + types.ExprString(recvExpr))
			fc.fl.st.AssertEqual(fc.deref(p), t)
			t = p
		case !want && have: // неявный *p
			t = fc.deref(t)
		}
		vars[recv], names[recv] = t, types.ExprString(recvExpr)
	}

	argTerms := fc.values(args, tupleLen(sig))
	if sig != nil {
		params := sig.Params()
		for i, t := range argTerms {
			if i >= params.Len() || (sig.Variadic() && i >= params.Len()-1) {
				break // вариативные аргументы в контракт не попадают
			}
			v := params.At(i)
			vars[v] = t
			if i < len(args) && len(args) == len(argTerms) {
				names[v] = types.ExprString(args[i])
			} else {
				names[v] = v.Name()
			}
		}
	}

	var spec *bound.Func
	if fn != nil {
		spec = fc.specs.Funcs[fn.Origin()]
	}
	if spec != nil {
		for _, eq := range spec.Requires {
			l, r := fc.specTerm(eq.Left, vars, none), fc.specTerm(eq.Right, vars, none)
			fc.prove(call.Lparen, l, r, render(eq.Left, names)+" == "+render(eq.Right, names))
		}
	}

	if sig == nil {
		return []term{fc.fresh("call")}
	}
	results := make([]term, sig.Results().Len())
	for i := range results {
		results[i] = fc.fresh("result")
	}
	if spec != nil && spec.Returns != nil {
		for i, r := range spec.Returns {
			if r.Args == nil {
				continue
			}
			target := fc.specs.Bounded(r.Type)
			for j, arg := range r.Args {
				fc.fl.st.AssertEqual(fc.idx(results[i], target.Params[j]), fc.specTerm(arg, vars, none))
			}
		}
	}
	return results
}

// tupleLen — сколько значений ждёт вызов: для f(g()) с многозначным g.
func tupleLen(sig *types.Signature) int {
	if sig == nil {
		return 0
	}
	return sig.Params().Len()
}

// render печатает терм спецификации в терминах места вызова: a<c> → a4<c>.
func render(e bound.Expr, names map[*types.Var]string) string {
	switch e := e.(type) {
	case *bound.Var:
		if n, ok := names[e.Obj]; ok {
			return n
		}
	case *bound.FieldOf:
		return render(e.X, names) + "." + e.Field.Name()
	case *bound.ParamOf:
		return render(e.X, names) + "<" + e.Param.Name + ">"
	}
	return e.String()
}

// ---- литералы и нулевые значения ----

func (fc *funcChecker) compositeLit(e *ast.CompositeLit) term {
	t := fc.info.TypeOf(e)
	st, ok := t.Underlying().(*types.Struct)
	if !ok {
		for _, el := range e.Elts {
			fc.expr(el)
		}
		return fc.fresh("lit")
	}
	vals := map[*types.Var]term{}
	for i, el := range e.Elts {
		if kv, ok := el.(*ast.KeyValueExpr); ok {
			if f, ok := fc.info.Uses[kv.Key.(*ast.Ident)].(*types.Var); ok {
				vals[f] = fc.expr(kv.Value)
			}
		} else {
			vals[st.Field(i)] = fc.expr(el)
		}
	}
	return fc.build(t, vals, e.Pos())
}

// build создаёт значение структуры t с полями vals (остальные — нулевые)
// и проверяет инварианты equals/close.
func (fc *funcChecker) build(t types.Type, vals map[*types.Var]term, pos token.Pos) term {
	st := t.Underlying().(*types.Struct)
	name := types.TypeString(t, types.RelativeTo(fc.pkg.Types))
	r := fc.fresh(name)
	fields := map[*types.Var]term{}
	for f := range st.Fields() {
		v, ok := vals[f]
		if !ok {
			v = fc.zero(f.Type(), pos)
		}
		fields[f] = v
		fc.fl.st.AssertEqual(fc.field(r, f), v)
	}
	s := fc.specs.StructOf(t)
	if s == nil {
		return r
	}
	// Параметр определяется первым полем, которое его упоминает;
	// остальные упоминания проверяются.
	defined := map[*bound.Param]bool{}
	ok := true
	for _, fa := range s.Fields {
		v := fields[fa.Var]
		if p := fa.Equals; p != nil {
			if !defined[p] {
				defined[p] = true
				fc.fl.st.AssertEqual(fc.idx(r, p), v)
			} else {
				ok = fc.prove(pos, v, fc.idx(r, p), fmt.Sprintf("%s literal: %s equals %s", name, fa.Var.Name(), p.Name)) && ok
			}
			continue
		}
		target := fc.specs.Bounded(fa.Var.Type())
		for i, arg := range fa.Close {
			got := fc.idx(v, target.Params[i])
			if sp, isSelf := arg.(*bound.SelfParam); isSelf && !defined[sp.Param] {
				defined[sp.Param] = true
				fc.fl.st.AssertEqual(fc.idx(r, sp.Param), got)
				continue
			}
			ok = fc.prove(pos, got, fc.specTerm(arg, nil, r),
				fmt.Sprintf("%s literal: %s<%s> == %s", name, fa.Var.Name(), target.Params[i].Name, arg)) && ok
		}
	}
	if !ok {
		// Инвариант нарушен (уже сообщили): индексы значения неизвестны.
		return fc.fresh(name)
	}
	return r
}

// zero — терм нулевого значения типа t.
func (fc *funcChecker) zero(t types.Type, pos token.Pos) term {
	switch u := t.Underlying().(type) {
	case *types.Basic:
		switch {
		case u.Info()&types.IsString != 0:
			return fc.constant(constant.MakeString(""))
		case u.Info()&types.IsBoolean != 0:
			return fc.constant(constant.MakeBool(false))
		case u.Info()&types.IsNumeric != 0:
			return fc.constant(constant.MakeInt64(0))
		}
		return fc.nilTerm() // unsafe.Pointer
	case *types.Struct:
		return fc.build(t, nil, pos)
	case *types.Pointer, *types.Slice, *types.Map, *types.Chan, *types.Signature, *types.Interface:
		return fc.nilTerm()
	}
	return fc.fresh("zero")
}

func isPointer(t types.Type) bool {
	_, ok := t.Underlying().(*types.Pointer)
	return ok
}

func derefType(t types.Type) types.Type {
	if p, ok := t.Underlying().(*types.Pointer); ok {
		return p.Elem()
	}
	return t
}

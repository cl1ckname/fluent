package checker

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"

	"fluent/bound"
	"fluent/congruence"
)

type term = congruence.Term

// flow — знание в точке программы: равенства и текущие термы переменных.
type flow struct {
	st   *congruence.State
	cur  map[*types.Var]term
	dead bool // точка недостижима (после return, panic, break, ...)
}

func (f *flow) clone() *flow {
	return &flow{st: f.st.Clone(), cur: maps.Clone(f.cur), dead: f.dead}
}

// funcChecker проверяет одно тело функции.
type funcChecker struct {
	*checker
	bank  *congruence.Bank
	fl    *flow
	sig   *types.Signature
	spec  *bound.Func         // контракт проверяемой функции или nil
	entry map[*types.Var]term // значения параметров на входе (для returns)

	addrTaken  map[*types.Var]bool // адрес взят или переменная захвачена замыканием
	gotoLabels map[string]bool
	nfresh     int
}

func (c *checker) checkFunc(sig *types.Signature, body *ast.BlockStmt, spec *bound.Func) {
	bank := congruence.NewBank()
	fc := &funcChecker{
		checker: c,
		bank:    bank,
		fl:      &flow{st: congruence.NewState(bank), cur: map[*types.Var]term{}},
		sig:     sig,
		spec:    spec,
		entry:   map[*types.Var]term{},
	}
	fc.prescan(body)
	params := []*types.Var{sig.Recv()}
	for v := range sig.Params().Variables() {
		params = append(params, v)
	}
	for _, v := range params {
		if v != nil && v.Name() != "" && v.Name() != "_" {
			t := fc.fresh(v.Name())
			fc.entry[v], fc.fl.cur[v] = t, t
		}
	}
	for v := range sig.Results().Variables() {
		if v.Name() != "" && v.Name() != "_" {
			fc.fl.cur[v] = fc.zero(v.Type(), body.Pos())
		}
	}
	// Внутри функции её предусловие считается верным.
	if spec != nil {
		for _, eq := range spec.Requires {
			fc.fl.st.AssertEqual(fc.specTerm(eq.Left, fc.entry, none), fc.specTerm(eq.Right, fc.entry, none))
		}
	}
	fc.stmts(body.List)
}

func (fc *funcChecker) fresh(hint string) term {
	fc.nfresh++
	return fc.bank.Atom(fmt.Sprintf("%s#%d", hint, fc.nfresh))
}

// errorf сообщает об ошибке, если точка достижима.
func (fc *funcChecker) errorf(pos token.Pos, format string, args ...any) {
	if fc.fl.dead || fc.fl.st.Inconsistent() {
		return
	}
	fc.report(Diagnostic{Pos: pos, Message: fmt.Sprintf(format, args...)})
}

// prove проверяет a ≈ b; если не выводится, сообщает «cannot prove what».
func (fc *funcChecker) prove(pos token.Pos, a, b term, what string) bool {
	if fc.fl.st.AreEqual(a, b) {
		return true
	}
	fc.errorf(pos, "cannot prove %s%s", what, fc.explain(a, b))
	return false
}

// explain добавляет к сообщению известные значения: ("usd" vs "rub").
func (fc *funcChecker) explain(a, b term) string {
	ca, oka := fc.fl.st.ConstOf(a)
	cb, okb := fc.fl.st.ConstOf(b)
	if oka && okb {
		return fmt.Sprintf(" (%s vs %s)", fc.bank.String(ca), fc.bank.String(cb))
	}
	return ""
}

// ---- предварительный проход ----

func (fc *funcChecker) prescan(body *ast.BlockStmt) {
	fc.addrTaken = map[*types.Var]bool{}
	fc.gotoLabels = map[string]bool{}
	ast.Inspect(body, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.UnaryExpr:
			if n.Op == token.AND {
				fc.markAddr(n.X)
			}
		case *ast.SelectorExpr:
			// x.m() с pointer-receiver на адресуемом значении — неявный &x.
			if sel := fc.info.Selections[n]; sel != nil && sel.Kind() == types.MethodVal {
				recv := sel.Obj().(*types.Func).Type().(*types.Signature).Recv()
				if isPointer(recv.Type()) && !isPointer(fc.info.TypeOf(n.X)) {
					fc.markAddr(n.X)
				}
			}
		case *ast.FuncLit:
			// Замыкание может менять захваченные переменные когда угодно.
			ast.Inspect(n.Body, func(m ast.Node) bool {
				if id, ok := m.(*ast.Ident); ok {
					if v, ok := fc.info.Uses[id].(*types.Var); ok {
						fc.addrTaken[v] = true
					}
				}
				return true
			})
		case *ast.BranchStmt:
			if n.Tok == token.GOTO {
				fc.gotoLabels[n.Label.Name] = true
			}
		}
		return true
	})
}

func (fc *funcChecker) markAddr(e ast.Expr) {
	if v := fc.rootVar(e); v != nil {
		fc.addrTaken[v] = true
	}
}

// rootVar — переменная, в которой хранится значение e (x, x.f, x[i] для массива).
// nil, если значение лежит за указателем, в срезе, в map и т.п.
func (fc *funcChecker) rootVar(e ast.Expr) *types.Var {
	switch e := ast.Unparen(e).(type) {
	case *ast.Ident:
		return fc.varOf(e)
	case *ast.SelectorExpr:
		if sel := fc.info.Selections[e]; sel != nil && sel.Kind() == types.FieldVal && !isPointer(fc.info.TypeOf(e.X)) {
			return fc.rootVar(e.X)
		}
	case *ast.IndexExpr:
		if _, ok := fc.info.TypeOf(e.X).Underlying().(*types.Array); ok {
			return fc.rootVar(e.X)
		}
	}
	return nil
}

func (fc *funcChecker) varOf(id *ast.Ident) *types.Var {
	if v, ok := fc.info.Defs[id].(*types.Var); ok {
		return v
	}
	v, _ := fc.info.Uses[id].(*types.Var)
	return v
}

// assigned — локальные переменные, которым что-то присваивается внутри n.
func (fc *funcChecker) assigned(n ast.Node) []*types.Var {
	var out []*types.Var
	seen := map[*types.Var]bool{}
	add := func(e ast.Expr) {
		if e == nil {
			return
		}
		if v := fc.rootVar(e); v != nil && !seen[v] {
			seen[v] = true
			out = append(out, v)
		}
	}
	ast.Inspect(n, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.AssignStmt:
			for _, l := range n.Lhs {
				add(l)
			}
		case *ast.IncDecStmt:
			add(n.X)
		case *ast.RangeStmt:
			add(n.Key)
			add(n.Value)
		case *ast.FuncLit:
			return false
		}
		return true
	})
	return out
}

// havoc забывает всё о значениях переменных vs.
func (fc *funcChecker) havoc(vs []*types.Var) {
	for _, v := range vs {
		if _, ok := fc.fl.cur[v]; ok {
			fc.fl.cur[v] = fc.fresh(v.Name())
		}
	}
}

// ---- операторы ----

func (fc *funcChecker) stmts(list []ast.Stmt) {
	for _, s := range list {
		fc.stmt(s)
	}
}

func (fc *funcChecker) stmt(s ast.Stmt) {
	switch s := s.(type) {
	case *ast.BlockStmt:
		fc.stmts(s.List)
	case *ast.ExprStmt:
		fc.expr(s.X)
		if call, ok := ast.Unparen(s.X).(*ast.CallExpr); ok && fc.isPanic(call) {
			fc.fl.dead = true
		}
	case *ast.AssignStmt:
		fc.assignStmt(s)
	case *ast.IncDecStmt:
		fc.expr(s.X)
		fc.assign(s.X, fc.fresh("incdec"), true)
	case *ast.DeclStmt:
		fc.declStmt(s)
	case *ast.ReturnStmt:
		fc.returnStmt(s)
	case *ast.IfStmt:
		fc.ifStmt(s)
	case *ast.ForStmt:
		fc.loop(s, s.Init, s.Cond, s.Post, s.Body)
	case *ast.RangeStmt:
		fc.expr(s.X)
		fc.loop(s, nil, nil, nil, s.Body)
	case *ast.SwitchStmt:
		if s.Init != nil {
			fc.stmt(s.Init)
		}
		if s.Tag != nil {
			fc.expr(s.Tag)
		}
		fc.clauses(s, s.Body)
	case *ast.TypeSwitchStmt:
		if s.Init != nil {
			fc.stmt(s.Init)
		}
		fc.stmt(s.Assign)
		fc.clauses(s, s.Body)
	case *ast.SelectStmt:
		fc.clauses(s, s.Body)
	case *ast.LabeledStmt:
		if fc.gotoLabels[s.Label.Name] {
			// Сюда можно прийти по goto откуда угодно: забываем всё, что меняется в функции.
			fc.fl.dead = false
			fc.havoc(slicesOfMap(fc.fl.cur))
		}
		fc.stmt(s.Stmt)
	case *ast.BranchStmt:
		fc.fl.dead = true
	case *ast.GoStmt:
		fc.expr(s.Call)
	case *ast.DeferStmt:
		fc.expr(s.Call)
	case *ast.SendStmt:
		fc.expr(s.Chan)
		fc.expr(s.Value)
	case *ast.EmptyStmt:
	default:
		// CaseClause и CommClause обрабатываются в clauses.
	}
}

func slicesOfMap(m map[*types.Var]term) []*types.Var {
	out := make([]*types.Var, 0, len(m))
	for v := range m {
		out = append(out, v)
	}
	return out
}

func (fc *funcChecker) isPanic(call *ast.CallExpr) bool {
	id, ok := ast.Unparen(call.Fun).(*ast.Ident)
	if !ok {
		return false
	}
	b, ok := fc.info.Uses[id].(*types.Builtin)
	return ok && b.Name() == "panic"
}

func (fc *funcChecker) assignStmt(s *ast.AssignStmt) {
	if s.Tok != token.ASSIGN && s.Tok != token.DEFINE {
		// x op= e: новое значение неизвестно.
		fc.expr(s.Rhs[0])
		fc.expr(s.Lhs[0])
		fc.assign(s.Lhs[0], fc.fresh("opassign"), true)
		return
	}
	rhs := fc.values(s.Rhs, len(s.Lhs))
	for i, l := range s.Lhs {
		fc.assign(l, rhs[i], true)
	}
}

// values вычисляет правые части присваивания; n — сколько значений нужно.
func (fc *funcChecker) values(exprs []ast.Expr, n int) []term {
	if len(exprs) == 1 && n > 1 {
		if call, ok := ast.Unparen(exprs[0]).(*ast.CallExpr); ok {
			return fc.call(call)
		}
		// v, ok := m[k] / x.(T) / <-ch
		fc.expr(exprs[0])
		out := make([]term, n)
		for i := range out {
			out[i] = fc.fresh("commaok")
		}
		return out
	}
	out := make([]term, len(exprs))
	for i, e := range exprs {
		out[i] = fc.expr(e)
	}
	return out
}

func (fc *funcChecker) declStmt(s *ast.DeclStmt) {
	gd, ok := s.Decl.(*ast.GenDecl)
	if !ok || gd.Tok != token.VAR {
		return
	}
	for _, sp := range gd.Specs {
		vs := sp.(*ast.ValueSpec)
		var vals []term
		if len(vs.Values) > 0 {
			vals = fc.values(vs.Values, len(vs.Names))
		}
		for i, name := range vs.Names {
			v := fc.varOf(name)
			if v == nil || name.Name == "_" {
				continue
			}
			if vals != nil {
				fc.fl.cur[v] = vals[i]
			} else {
				fc.fl.cur[v] = fc.zero(v.Type(), name.Pos())
			}
		}
	}
}

// assign записывает значение val в lhs. check — проверять ли сохранение индексов
// (false при перестройке родителя после уже сообщённой ошибки).
func (fc *funcChecker) assign(lhs ast.Expr, val term, check bool) {
	switch l := ast.Unparen(lhs).(type) {
	case *ast.Ident:
		v := fc.varOf(l)
		if v == nil || l.Name == "_" || !fc.isLocal(v) {
			return
		}
		// Переменная, на которую может указывать указатель, — это объект:
		// его индексы менять нельзя.
		if old, ok := fc.fl.cur[v]; ok && fc.addrTaken[v] && check {
			fc.preserve(l.Pos(), old, val, v.Type(), l.Name)
		}
		fc.fl.cur[v] = val
	case *ast.SelectorExpr:
		sel := fc.info.Selections[l]
		if sel == nil || sel.Kind() != types.FieldVal || len(sel.Index()) != 1 {
			fc.expr(l.X)
			return
		}
		fc.assignField(l, sel.Obj().(*types.Var), val, check)
	case *ast.StarExpr:
		p := fc.expr(l.X)
		if check {
			fc.preserve(l.Pos(), fc.deref(p), val, fc.info.TypeOf(l), types.ExprString(l))
		}
	case *ast.IndexExpr:
		fc.expr(l.X)
		fc.expr(l.Index)
	}
}

// assignField — x.f = val.
func (fc *funcChecker) assignField(l *ast.SelectorExpr, f *types.Var, val term, check bool) {
	xt := fc.info.TypeOf(l.X)
	viaPtr := isPointer(xt)
	base := fc.expr(l.X)
	if viaPtr {
		base = fc.deref(base)
	}
	st := derefType(xt)
	ok := true
	if s := fc.specs.StructOf(st); s != nil && check {
		for _, fa := range s.Fields {
			if fa.Var != f {
				continue
			}
			if fa.Equals != nil {
				ok = fc.prove(l.Sel.Pos(), val, fc.idx(base, fa.Equals),
					fmt.Sprintf("assignment to %s preserves %s<%s>", types.ExprString(l), types.ExprString(l.X), fa.Equals.Name))
			}
			if fa.Close != nil {
				target := fc.specs.Bounded(f.Type())
				for i, arg := range fa.Close {
					p := target.Params[i]
					ok = fc.prove(l.Sel.Pos(), fc.idx(val, p), fc.specTerm(arg, nil, base),
						fmt.Sprintf("assignment to %s preserves %s<%s> == %s", types.ExprString(l), types.ExprString(l), p.Name, arg)) && ok
				}
			}
		}
	}
	// Ошибочное присваивание не применяем: об ошибке уже сообщили, дальше
	// рассуждаем о прежнем объекте (иначе ошибки посыплются каскадом).
	// Через указатель или у переменной с взятым адресом обычные поля и так
	// читаются как свежие термы — обновлять нечего.
	root := fc.rootVar(l.X)
	if !ok || viaPtr || root == nil || fc.addrTaken[root] {
		return
	}
	// Значение-структура: строим новое значение x с изменённым полем f.
	nb := fc.fresh(types.ExprString(l.X))
	for g := range st.Underlying().(*types.Struct).Fields() {
		if g == f {
			fc.fl.st.AssertEqual(fc.field(nb, g), val)
		} else {
			fc.fl.st.AssertEqual(fc.field(nb, g), fc.field(base, g))
		}
	}
	if s := fc.specs.Bounded(st); s != nil {
		for _, p := range s.Params {
			fc.fl.st.AssertEqual(fc.idx(nb, p), fc.idx(base, p))
		}
	}
	fc.assign(l.X, nb, check)
}

// preserve проверяет, что новое значение объекта имеет те же индексы, что и старое.
func (fc *funcChecker) preserve(pos token.Pos, old, val term, t types.Type, what string) {
	s := fc.specs.Bounded(t)
	if s == nil {
		return
	}
	for _, p := range s.Params {
		fc.prove(pos, fc.idx(val, p), fc.idx(old, p), fmt.Sprintf("assignment to %s preserves %s<%s>", what, what, p.Name))
	}
}

func (fc *funcChecker) isLocal(v *types.Var) bool {
	return v.Pkg() == nil || v.Parent() != v.Pkg().Scope()
}

func (fc *funcChecker) returnStmt(s *ast.ReturnStmt) {
	var vals []term
	switch {
	case len(s.Results) == 0:
		for v := range fc.sig.Results().Variables() {
			t, ok := fc.fl.cur[v]
			if !ok {
				t = fc.fresh("result")
			}
			vals = append(vals, t)
		}
	default:
		vals = fc.values(s.Results, fc.sig.Results().Len())
	}
	if fc.spec != nil && fc.spec.Returns != nil && len(vals) == len(fc.spec.Returns) {
		for i, r := range fc.spec.Returns {
			if r.Args == nil {
				continue
			}
			target := fc.specs.Bounded(r.Type)
			for j, arg := range r.Args {
				p := target.Params[j]
				fc.prove(s.Pos(), fc.idx(vals[i], p), fc.specTerm(arg, fc.entry, none),
					fmt.Sprintf("result %d satisfies returns: result<%s> == %s", i+1, p.Name, arg))
			}
		}
	}
	fc.fl.dead = true
}

func (fc *funcChecker) ifStmt(s *ast.IfStmt) {
	if s.Init != nil {
		fc.stmt(s.Init)
	}
	pos, neg := fc.cond(s.Cond)
	before := fc.fl

	fc.fl = before.clone()
	fc.assume(pos)
	fc.stmt(s.Body)
	thenFl := fc.fl

	fc.fl = before.clone()
	fc.assume(neg)
	if s.Else != nil {
		fc.stmt(s.Else)
	}
	fc.fl = fc.join(thenFl, fc.fl)
}

func (fc *funcChecker) assume(eqs [][2]term) {
	for _, e := range eqs {
		fc.fl.st.AssertEqual(e[0], e[1])
	}
}

// cond вычисляет условие и возвращает равенства, верные, когда оно истинно (pos)
// и когда ложно (neg).
func (fc *funcChecker) cond(e ast.Expr) (pos, neg [][2]term) {
	switch e := ast.Unparen(e).(type) {
	case *ast.BinaryExpr:
		switch e.Op {
		case token.EQL:
			return [][2]term{{fc.expr(e.X), fc.expr(e.Y)}}, nil
		case token.NEQ:
			return nil, [][2]term{{fc.expr(e.X), fc.expr(e.Y)}}
		case token.LAND:
			p1, _ := fc.cond(e.X)
			// Правая часть вычисляется, только если левая истинна.
			saved := fc.fl
			fc.fl = saved.clone()
			fc.assume(p1)
			p2, _ := fc.cond(e.Y)
			fc.fl = saved
			return append(p1, p2...), nil
		case token.LOR:
			_, n1 := fc.cond(e.X)
			saved := fc.fl
			fc.fl = saved.clone()
			fc.assume(n1)
			_, n2 := fc.cond(e.Y)
			fc.fl = saved
			return nil, append(n1, n2...)
		}
	case *ast.UnaryExpr:
		if e.Op == token.NOT {
			p, n := fc.cond(e.X)
			return n, p
		}
	}
	fc.expr(e)
	return nil, nil
}

// join сливает два потока: остаются равенства, верные в обоих.
func (fc *funcChecker) join(a, b *flow) *flow {
	switch {
	case a.dead:
		return b
	case b.dead:
		return a
	}
	cur := map[*types.Var]term{}
	for v, ta := range a.cur {
		tb, ok := b.cur[v]
		if !ok {
			continue // переменная объявлена только в одной ветке
		}
		if ta == tb {
			cur[v] = ta
			continue
		}
		m := fc.fresh(v.Name())
		a.st.AssertEqual(m, ta)
		b.st.AssertEqual(m, tb)
		// Join видит только термы, которые уже есть в банке: заводим индексы
		// и поля m сейчас, иначе факты о них потеряются.
		fc.materialize(m, v.Type(), 2)
		cur[v] = m
	}
	return &flow{st: congruence.Join(a.st, b.st), cur: cur}
}

// materialize создаёт в банке термы индексов и полей значения t типа typ
// (на глубину depth), чтобы Join мог сохранить факты о них.
func (fc *funcChecker) materialize(t term, typ types.Type, depth int) {
	if isPointer(typ) {
		t, typ = fc.deref(t), derefType(typ)
	}
	if s := fc.specs.Bounded(typ); s != nil {
		for _, p := range s.Params {
			fc.idx(t, p)
		}
	}
	st, ok := typ.Underlying().(*types.Struct)
	if !ok || depth == 0 {
		return
	}
	for f := range st.Fields() {
		fc.materialize(fc.field(t, f), f.Type(), depth-1)
	}
}

// loop — консервативно: переменные, которые меняются в цикле, забываются;
// тело проверяется один раз, а после цикла известно только то, что было до него.
func (fc *funcChecker) loop(s ast.Stmt, init ast.Stmt, cond ast.Expr, post ast.Stmt, body *ast.BlockStmt) {
	if init != nil {
		fc.stmt(init)
	}
	fc.havoc(fc.assigned(s))
	after := fc.fl
	fc.fl = after.clone()
	if r, ok := s.(*ast.RangeStmt); ok {
		for _, e := range []ast.Expr{r.Key, r.Value} {
			if e != nil {
				fc.assign(e, fc.fresh("range"), false)
			}
		}
	}
	if cond != nil {
		pos, _ := fc.cond(cond)
		fc.assume(pos)
	}
	fc.stmt(body)
	fc.fl.dead = false
	if post != nil {
		fc.stmt(post)
	}
	fc.fl = after
}

// clauses — switch/select: каждая ветка проверяется от состояния до switch,
// после switch переменные, меняющиеся в ветках, забываются.
func (fc *funcChecker) clauses(s ast.Stmt, body *ast.BlockStmt) {
	before := fc.fl
	for _, cl := range body.List {
		fc.fl = before.clone()
		switch cl := cl.(type) {
		case *ast.CaseClause:
			for _, e := range cl.List {
				fc.expr(e)
			}
			if obj, ok := fc.info.Implicits[cl].(*types.Var); ok {
				fc.fl.cur[obj] = fc.fresh(obj.Name())
			}
			fc.stmts(cl.Body)
		case *ast.CommClause:
			if cl.Comm != nil {
				fc.stmt(cl.Comm)
			}
			fc.stmts(cl.Body)
		}
	}
	fc.fl = before
	fc.havoc(fc.assigned(s))
}

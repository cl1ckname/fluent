package bound

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"

	"fluent/spec"
)

// Resolve разбирает спецификации пакета, связывает их с go/types и проверяет.
// Все ошибки (синтаксис и смысл) передаются в report; ошибочные инструкции
// в Info не попадают.
//
// TODO: bounded-типы из других пакетов (через analysis.Fact). Сейчас они
// считаются типами без параметров.
func Resolve(files []*ast.File, pkg *types.Package, info *types.Info, report func(token.Pos, string)) *Info {
	r := &resolver{
		pkg:    pkg,
		info:   info,
		report: report,
		out: &Info{
			Structs: map[*types.TypeName]*Struct{},
			Funcs:   map[*types.Func]*Func{},
		},
	}
	for _, f := range files {
		r.collect(f)
	}
	for _, d := range r.types {
		r.resolveBound(d)
	}
	for _, d := range r.types {
		r.resolveFields(d)
	}
	for _, d := range r.funcs {
		r.resolveFunc(d)
	}
	return r.out
}

type resolver struct {
	pkg    *types.Package
	info   *types.Info
	report func(token.Pos, string)
	out    *Info

	types []*typeDecl
	funcs []*funcDecl
}

type typeDecl struct {
	file    *ast.File
	obj     *types.TypeName
	st      *ast.StructType // nil, если тип не структура
	clauses []spec.Clause
	fields  []fieldDecl
	used    map[*Param]bool
}

type fieldDecl struct {
	field   *ast.Field
	clauses []spec.Clause
}

type funcDecl struct {
	file    *ast.File
	obj     *types.Func
	clauses []spec.Clause
}

func (r *resolver) errorf(pos token.Pos, format string, args ...any) {
	r.report(pos, fmt.Sprintf(format, args...))
}

func (r *resolver) parse(doc *ast.CommentGroup) []spec.Clause {
	clauses, errs := spec.ParseDoc(doc)
	for _, e := range errs {
		r.report(e.Pos, e.Msg)
	}
	return clauses
}

// collect находит все спецификации файла и раскладывает их по объявлениям.
func (r *resolver) collect(file *ast.File) {
	for _, decl := range file.Decls {
		switch d := decl.(type) {
		case *ast.FuncDecl:
			obj, _ := r.info.Defs[d.Name].(*types.Func)
			if cs := r.parse(d.Doc); len(cs) > 0 && obj != nil {
				r.funcs = append(r.funcs, &funcDecl{file: file, obj: obj, clauses: cs})
			}
		case *ast.GenDecl:
			if d.Tok != token.TYPE {
				r.notAllowed(r.parse(d.Doc), "here")
				continue
			}
			for _, s := range d.Specs {
				r.collectType(file, d, s.(*ast.TypeSpec))
			}
		}
	}
}

func (r *resolver) collectType(file *ast.File, gd *ast.GenDecl, ts *ast.TypeSpec) {
	doc := ts.Doc
	if !gd.Lparen.IsValid() {
		doc = gd.Doc
	}
	obj, _ := r.info.Defs[ts.Name].(*types.TypeName)
	d := &typeDecl{file: file, obj: obj, clauses: r.parse(doc), used: map[*Param]bool{}}
	if st, ok := ts.Type.(*ast.StructType); ok {
		d.st = st
		for _, f := range st.Fields.List {
			if cs := r.parse(f.Doc); len(cs) > 0 {
				d.fields = append(d.fields, fieldDecl{field: f, clauses: cs})
			}
		}
	}
	if obj != nil && (len(d.clauses) > 0 || len(d.fields) > 0) {
		r.types = append(r.types, d)
	}
}

func (r *resolver) notAllowed(cs []spec.Clause, where string) {
	for _, c := range cs {
		r.errorf(c.Pos(), "%s is not allowed %s", keyword(c), where)
	}
}

func keyword(c spec.Clause) string {
	switch c.(type) {
	case *spec.Bound:
		return "bound"
	case *spec.Equals:
		return "equals"
	case *spec.Close:
		return "close"
	case *spec.Requires:
		return "requires"
	case *spec.Returns:
		return "returns"
	}
	panic("unreachable")
}

// structFor возвращает (создавая при необходимости) запись Struct для объявления.
func (r *resolver) structFor(d *typeDecl) *Struct {
	s := r.out.Structs[d.obj]
	if s == nil {
		s = &Struct{Obj: d.obj}
		r.out.Structs[d.obj] = s
	}
	return s
}

// ---- фаза 1: bound ----

func (r *resolver) resolveBound(d *typeDecl) {
	var bound *spec.Bound
	for _, c := range d.clauses {
		b, ok := c.(*spec.Bound)
		switch {
		case !ok:
			r.errorf(c.Pos(), "%s is not allowed on a type declaration", keyword(c))
		case bound != nil:
			r.errorf(c.Pos(), "duplicate bound for %s", d.obj.Name())
		default:
			bound = b
		}
	}
	if d.st == nil {
		if bound != nil {
			r.errorf(bound.Pos(), "bound is only allowed on struct types, %s is not a struct", d.obj.Name())
		}
		return
	}
	s := r.structFor(d)
	if bound == nil {
		return
	}
	if named, ok := d.obj.Type().(*types.Named); ok && named.TypeParams().Len() > 0 {
		r.errorf(bound.Pos(), "bound on generic types is not supported")
		return
	}
	for _, bp := range bound.Params {
		if s.Param(bp.Name.Name) != nil {
			r.errorf(bp.Name.At, "duplicate parameter %s", bp.Name.Name)
			continue
		}
		t := r.typeOf(d.file, bp.Type)
		if t == nil {
			continue
		}
		if !types.Comparable(t) {
			r.errorf(bp.Type.Name.At, "parameter %s: type %s is not comparable", bp.Name.Name, r.typeString(t))
			continue
		}
		s.Params = append(s.Params, &Param{
			Owner: d.obj,
			Index: len(s.Params),
			Name:  bp.Name.Name,
			Type:  t,
			Pos:   bp.Name.At,
		})
	}
}

// ---- фаза 2: equals / close ----

func (r *resolver) resolveFields(d *typeDecl) {
	s := r.out.Structs[d.obj]
	if s == nil {
		return
	}
	for _, fd := range d.fields {
		if len(fd.field.Names) == 0 {
			r.errorf(fd.clauses[0].Pos(), "annotations on embedded fields are not supported")
			continue
		}
		var ann spec.Clause
		for _, c := range fd.clauses {
			switch c.(type) {
			case *spec.Equals, *spec.Close:
				if ann != nil {
					r.errorf(c.Pos(), "field already has %s annotation", keyword(ann))
					continue
				}
				ann = c
			default:
				r.errorf(c.Pos(), "%s is not allowed on a field", keyword(c))
			}
		}
		if ann == nil {
			continue
		}
		for _, name := range fd.field.Names {
			v, _ := r.info.Defs[name].(*types.Var)
			if v == nil {
				continue
			}
			var f *Field
			switch c := ann.(type) {
			case *spec.Equals:
				f = r.resolveEquals(d, s, v, c)
			case *spec.Close:
				f = r.resolveClose(d, s, v, c)
			}
			if f != nil {
				s.Fields = append(s.Fields, f)
			}
		}
	}
	for _, p := range s.Params {
		if !d.used[p] {
			r.errorf(p.Pos, "parameter %s is not used by any equals or close", p.Name)
		}
	}
}

func (r *resolver) resolveEquals(d *typeDecl, s *Struct, v *types.Var, c *spec.Equals) *Field {
	p := s.Param(c.Param.Name)
	if p == nil {
		r.errorf(c.Param.At, "%s has no bound parameter %s", s.Obj.Name(), c.Param.Name)
		return nil
	}
	d.used[p] = true
	if !types.Identical(v.Type(), p.Type) {
		r.errorf(c.Param.At, "field %s has type %s, parameter %s has type %s",
			v.Name(), r.typeString(v.Type()), p.Name, r.typeString(p.Type))
		return nil
	}
	return &Field{Var: v, Equals: p}
}

func (r *resolver) resolveClose(d *typeDecl, s *Struct, v *types.Var, c *spec.Close) *Field {
	target := r.out.Bounded(v.Type())
	if target == nil {
		r.errorf(c.Pos(), "close on field %s: type %s has no bound parameters", v.Name(), r.typeString(v.Type()))
		return nil
	}
	sc := &scope{file: d.file, self: s, used: d.used}
	args := r.args(sc, target, c.Args, c.Pos())
	if args == nil {
		return nil
	}
	return &Field{Var: v, Close: args}
}

// ---- фаза 3: requires / returns ----

func (r *resolver) resolveFunc(d *funcDecl) {
	sig := d.obj.Type().(*types.Signature)
	sc := &scope{file: d.file, vars: map[string]*types.Var{}}
	if recv := sig.Recv(); recv != nil {
		sc.vars[recv.Name()] = recv
	}
	for v := range sig.Params().Variables() {
		sc.vars[v.Name()] = v
	}

	fn := &Func{Obj: d.obj}
	var returns *spec.Returns
	for _, c := range d.clauses {
		switch c := c.(type) {
		case *spec.Requires:
			for _, eq := range c.Eqs {
				if e, ok := r.equality(sc, eq); ok {
					fn.Requires = append(fn.Requires, e)
				}
			}
		case *spec.Returns:
			if returns != nil {
				r.errorf(c.Pos(), "duplicate returns")
				continue
			}
			returns = c
			fn.Returns = r.returns(sc, sig, c)
		default:
			r.errorf(c.Pos(), "%s is not allowed on a function", keyword(c))
		}
	}
	if len(fn.Requires) > 0 || fn.Returns != nil {
		r.out.Funcs[d.obj] = fn
	}
}

// equality разрешает равенство из requires. В v0 сравниваются только индексы:
// каждая сторона — `x<p>` или константа, и хотя бы одна сторона — индекс.
// Индексы comparable по построению, поэтому отдельная проверка не нужна.
func (r *resolver) equality(sc *scope, eq spec.Equality) (Equality, bool) {
	l, rr := r.term(sc, eq.Left), r.term(sc, eq.Right)
	if l == nil || rr == nil {
		return Equality{}, false
	}
	_, lIdx := l.(*ParamOf)
	_, rIdx := rr.(*ParamOf)
	for _, e := range []Expr{l, rr} {
		switch e.(type) {
		case *ParamOf, *Const:
		default:
			r.errorf(e.Pos(), "requires compares only bound parameters: %s is not x<p> or a constant", e)
			return Equality{}, false
		}
	}
	if !lIdx && !rIdx {
		r.errorf(eq.Left.Pos(), "requires compares only bound parameters: %s == %s has none", l, rr)
		return Equality{}, false
	}
	lt, rt := l.Type(), rr.Type()
	if !types.AssignableTo(lt, rt) && !types.AssignableTo(rt, lt) {
		r.errorf(eq.Left.Pos(), "mismatched types %s and %s in %s == %s", r.typeString(lt), r.typeString(rt), l, rr)
		return Equality{}, false
	}
	return Equality{Left: l, Right: rr}, true
}

func (r *resolver) returns(sc *scope, sig *types.Signature, c *spec.Returns) []Result {
	if len(c.Results) != sig.Results().Len() {
		r.errorf(c.Pos(), "returns lists %d types, function has %d results", len(c.Results), sig.Results().Len())
		return nil
	}
	out := make([]Result, len(c.Results))
	for i, rt := range c.Results {
		want := sig.Results().At(i).Type()
		out[i] = Result{Type: want}
		// `_` — тип из сигнатуры без уточнения (для типов, не выразимых в спецификации).
		if rt.Type.Pkg == nil && rt.Type.Name.Name == "_" {
			if rt.Args != nil {
				r.errorf(rt.Type.Name.At, "_ cannot have arguments")
				return nil
			}
			continue
		}
		t := r.typeOf(sc.file, rt.Type)
		if t == nil {
			return nil
		}
		if !types.Identical(t, want) {
			r.errorf(rt.Type.Name.At, "result %d has type %s, returns says %s", i+1, r.typeString(want), r.typeString(t))
			return nil
		}
		if rt.Args == nil {
			continue
		}
		target := r.out.Bounded(t)
		if target == nil {
			r.errorf(rt.Type.Name.At, "type %s has no bound parameters", r.typeString(t))
			return nil
		}
		if out[i].Args = r.args(sc, target, rt.Args, rt.Type.Name.At); out[i].Args == nil {
			return nil
		}
	}
	return out
}

// args разрешает аргументы `T<e1..ek>` и сверяет их с параметрами target.
func (r *resolver) args(sc *scope, target *Struct, terms []spec.Term, pos token.Pos) []Expr {
	if len(terms) != len(target.Params) {
		r.errorf(pos, "%s has %d bound parameters, got %d arguments", target.Obj.Name(), len(target.Params), len(terms))
		return nil
	}
	out := make([]Expr, len(terms))
	for i, t := range terms {
		e := r.term(sc, t)
		if e == nil {
			return nil
		}
		p := target.Params[i]
		if !types.AssignableTo(e.Type(), p.Type) {
			r.errorf(t.Pos(), "cannot use %s (type %s) as parameter %s of %s (type %s)",
				e, r.typeString(e.Type()), p.Name, target.Obj.Name(), r.typeString(p.Type))
			return nil
		}
		out[i] = e
	}
	return out
}

// ---- термы и типы ----

// scope — имена, видимые в терме: параметры функции (vars) или
// параметры своей структуры (self, внутри close). Константы пакета видны всегда.
type scope struct {
	file *ast.File
	vars map[string]*types.Var
	self *Struct
	used map[*Param]bool
}

func (r *resolver) term(sc *scope, t spec.Term) Expr {
	switch t := t.(type) {
	case *spec.Lit:
		return &Const{Val: constant.MakeFromLiteral(t.Value, t.Kind, 0), Typ: untypedOf(t.Kind), Text: t.Value, At: t.At}
	case *spec.Path:
		x, steps := r.root(sc, t)
		if x == nil {
			return nil
		}
		for _, st := range steps {
			if x = r.step(x, st); x == nil {
				return nil
			}
		}
		return x
	}
	panic("unreachable")
}

// root разрешает начало пути и возвращает оставшиеся шаги.
func (r *resolver) root(sc *scope, t *spec.Path) (Expr, []spec.Step) {
	name, at := t.Root.Name, t.Root.At
	if v := sc.vars[name]; v != nil {
		return &Var{Obj: v, At: at}, t.Steps
	}
	if sc.self != nil {
		if p := sc.self.Param(name); p != nil {
			sc.used[p] = true
			return &SelfParam{Param: p, At: at}, t.Steps
		}
	}
	obj := r.lookup(sc.file, name)
	// pkg.Const
	if pn, ok := obj.(*types.PkgName); ok && len(t.Steps) > 0 && !t.Steps[0].Index {
		sel := t.Steps[0].Name
		obj = pn.Imported().Scope().Lookup(sel.Name)
		if obj == nil || !obj.Exported() {
			r.errorf(sel.At, "undefined: %s.%s", name, sel.Name)
			return nil, nil
		}
		name, at = name+"."+sel.Name, sel.At
		t = &spec.Path{Root: t.Root, Steps: t.Steps[1:]}
	}
	var c *Const
	switch o := obj.(type) {
	case nil:
		r.errorf(at, "undefined: %s", name)
		return nil, nil
	case *types.Const:
		c = &Const{Val: o.Val(), Typ: o.Type(), Text: name, At: at}
	case *types.Nil:
		c = &Const{Typ: types.Typ[types.UntypedNil], Text: "nil", At: at}
	default:
		r.errorf(at, "%s is not a parameter or constant", name)
		return nil, nil
	}
	if len(t.Steps) > 0 {
		r.errorf(t.Steps[0].Name.At, "cannot select from constant %s", name)
		return nil, nil
	}
	return c, nil
}

func (r *resolver) step(x Expr, st spec.Step) Expr {
	t := x.Type()
	if p, ok := t.Underlying().(*types.Pointer); ok {
		t = p.Elem()
	}
	if st.Index {
		s := r.out.Bounded(t)
		if s == nil {
			r.errorf(st.Name.At, "%s: type %s has no bound parameters", x, r.typeString(t))
			return nil
		}
		p := s.Param(st.Name.Name)
		if p == nil {
			r.errorf(st.Name.At, "%s: type %s has no bound parameter %s", x, r.typeString(t), st.Name.Name)
			return nil
		}
		return &ParamOf{X: x, Param: p, At: st.Name.At}
	}
	if s, ok := t.Underlying().(*types.Struct); ok {
		for f := range s.Fields() {
			if f.Name() == st.Name.Name {
				return &FieldOf{X: x, Field: f, At: st.Name.At}
			}
		}
	}
	r.errorf(st.Name.At, "%s: type %s has no field %s", x, r.typeString(t), st.Name.Name)
	return nil
}

func (r *resolver) typeOf(file *ast.File, tn spec.TypeName) types.Type {
	var obj types.Object
	name := tn.Name.Name
	if tn.Pkg != nil {
		pn, ok := r.lookup(file, tn.Pkg.Name).(*types.PkgName)
		if !ok {
			r.errorf(tn.Pkg.At, "undefined package: %s", tn.Pkg.Name)
			return nil
		}
		obj = pn.Imported().Scope().Lookup(name)
		name = tn.Pkg.Name + "." + name
	} else {
		obj = r.lookup(file, name)
	}
	tobj, ok := obj.(*types.TypeName)
	if !ok {
		r.errorf(tn.Name.At, "%s is not a type", name)
		return nil
	}
	return tobj.Type()
}

// lookup ищет имя на уровне пакета: объявления пакета, импорты файла, universe.
func (r *resolver) lookup(file *ast.File, name string) types.Object {
	if obj := r.pkg.Scope().Lookup(name); obj != nil {
		return obj
	}
	if fs := r.info.Scopes[file]; fs != nil {
		if obj := fs.Lookup(name); obj != nil {
			return obj
		}
	}
	return types.Universe.Lookup(name)
}

func untypedOf(k token.Token) types.Type {
	switch k {
	case token.INT:
		return types.Typ[types.UntypedInt]
	case token.FLOAT:
		return types.Typ[types.UntypedFloat]
	case token.IMAG:
		return types.Typ[types.UntypedComplex]
	case token.CHAR:
		return types.Typ[types.UntypedRune]
	}
	return types.Typ[types.UntypedString]
}

func (r *resolver) typeString(t types.Type) string { return typeString(t, r.pkg) }

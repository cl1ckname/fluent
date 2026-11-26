package checker

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"slices"

	"fluent/bound"
	"fluent/spec"
)

// Индексы относятся к типу элементов, а не к позициям backing array.
// none в args означает отдельный скрытый индекс у каждого элемента.
// Все значения args неизменяемы; копии слайса сохраняют ту же форму.
type sliceInfo struct{ args []term }

func (fc *funcChecker) builtinCall(fun ast.Expr) bool {
	id, ok := ast.Unparen(fun).(*ast.Ident)
	if !ok {
		return false
	}
	_, ok = fc.info.Uses[id].(*types.Builtin)
	return ok
}

func (fc *funcChecker) containsIndexedSlice(t types.Type, seen map[types.Type]bool) bool {
	if t == nil || seen[t] {
		return false
	}
	seen[t] = true
	if fc.sliceType(t) != nil {
		return true
	}
	switch u := t.Underlying().(type) {
	case *types.Pointer:
		return fc.containsIndexedSlice(u.Elem(), seen)
	case *types.Slice:
		return fc.containsIndexedSlice(u.Elem(), seen)
	case *types.Array:
		return fc.containsIndexedSlice(u.Elem(), seen)
	case *types.Map:
		return fc.containsIndexedSlice(u.Elem(), seen)
	case *types.Chan:
		return fc.containsIndexedSlice(u.Elem(), seen)
	case *types.Struct:
		for f := range u.Fields() {
			if fc.containsIndexedSlice(f.Type(), seen) {
				return true
			}
		}
	}
	return false
}

func (fc *funcChecker) sliceType(t types.Type) *types.Slice {
	if t == nil {
		return nil
	}
	s, ok := t.Underlying().(*types.Slice)
	if !ok || fc.specs.Bounded(t) == nil {
		return nil
	}
	return s
}

func (fc *funcChecker) sliceShape(t term, typ types.Type) sliceInfo {
	if s, ok := fc.fl.slices[t]; ok {
		fc.putSlice(t, typ, s.args)
		return s
	}
	for x, s := range fc.fl.slices {
		if fc.fl.st.AreEqual(t, x) {
			return s
		}
	}
	s := sliceInfo{}
	if target := fc.specs.Bounded(typ); target != nil {
		for _, p := range target.Params {
			s.args = append(s.args, fc.idx(t, p))
		}
	}
	fc.fl.slices[t] = s
	return s
}

func (fc *funcChecker) closeArgs(args []bound.Expr, vars map[*types.Var]term, self term) []term {
	out := make([]term, len(args))
	for i, arg := range args {
		if _, ok := arg.(*bound.Wildcard); ok {
			out[i] = none
		} else {
			out[i] = fc.specTerm(arg, vars, self)
		}
	}
	return out
}

func (fc *funcChecker) setSliceClose(t term, typ types.Type, args []bound.Expr, vars map[*types.Var]term, self term) {
	a := fc.closeArgs(args, vars, self)
	fc.putSlice(t, typ, a)
}

func (fc *funcChecker) putSlice(t term, typ types.Type, a []term) {
	fc.fl.slices[t] = sliceInfo{args: a}
	for i, p := range fc.specs.Bounded(typ).Params {
		if a[i] != none {
			fc.fl.st.AssertEqual(fc.idx(t, p), a[i])
		}
	}
}

func (fc *funcChecker) compatibleSlice(pos token.Pos, got, want []term, what string) bool {
	if len(got) != len(want) {
		return false
	}
	ok := true
	for i := range want {
		if (got[i] == none) != (want[i] == none) {
			fc.errorf(pos, "cannot use %s: slice indices are invariant (existential and fixed indices differ)", what)
			ok = false
		} else if got[i] != none {
			ok = fc.prove(pos, got[i], want[i], what+": slice indices match") && ok
		}
	}
	return ok
}

func (fc *funcChecker) sliceElement(pos token.Pos, s term, typ types.Type) term {
	sl := fc.sliceType(typ)
	shape := fc.sliceShape(s, typ)
	v := fc.fresh("slice element")
	value := v
	if isPointer(sl.Elem()) {
		b := fc.newBlock("slice element", derefType(sl.Elem()), fc.fresh("slice element contents"))
		fc.fl.ptrs[v] = ptrInfo{blocks: []blockID{b}, dependent: true}
		fc.fl.pinned[b] = true
		value = fc.content(b)
	}
	for i, p := range fc.specs.Bounded(typ).Params {
		if shape.args[i] != none {
			fc.fl.st.AssertEqual(fc.idx(value, p), shape.args[i])
		}
	}
	return v
}

// pinValue запрещает смену индексов через все уже известные алиасы.
// Закрепление необратимо: замена слота или сокращение слайса его не снимают.
func (fc *funcChecker) pinValue(pos token.Pos, t term, typ types.Type) {
	if isPointer(typ) {
		if fc.fl.st.AreEqual(t, fc.nilTerm()) {
			return
		}
		info := fc.pointsTo(t)
		if !info.exact {
			fc.errorf(pos, "cannot store pointer in a slice: it does not point to a known object")
			return
		}
		fc.record(info.blocks, false)
		for _, b := range fc.roots(info.blocks) {
			if !fc.permOf(b).readable() {
				fc.errorf(pos, "cannot store pointer in a slice: no access: %s", fc.permOf(b).why)
				continue
			}
			fc.fl.pinned[b] = true
		}
		return
	}
	if st, ok := typ.Underlying().(*types.Struct); ok {
		for f := range st.Fields() {
			if hasPointers(f.Type()) {
				fc.pinValue(pos, fc.field(t, f), f.Type())
			}
		}
	}
}

func (fc *funcChecker) indicesPinned(b blockID) bool {
	return fc.fl.pinned[b] || fc.fl.pinned[fc.root(b)]
}

func (fc *funcChecker) copyPins(to, from *flow) {
	for b, pinned := range from.pinned {
		if pinned {
			to.pinned[rootIn(to, b)] = true
		}
	}
}

func (fc *funcChecker) storeSliceElement(pos token.Pos, val term, elem types.Type, args []term) {
	v := val
	if isPointer(elem) {
		if fc.fl.st.AreEqual(val, fc.nilTerm()) {
			return
		}
		v = fc.deref(val)
	}
	for i, p := range fc.specs.Bounded(derefType(elem)).Params {
		if args[i] != none {
			fc.prove(pos, fc.idx(v, p), args[i], fmt.Sprintf("slice element<%s> matches slice index", p.Name))
		}
	}
	fc.pinValue(pos, val, elem)
}

func (fc *funcChecker) sliceLiteral(e *ast.CompositeLit) term {
	typ := fc.info.TypeOf(e)
	sl := fc.sliceType(typ)
	r := fc.fresh("slice literal")
	a := slices.Clone(fc.sliceWant)
	fc.sliceWant = nil
	values := make([]term, len(e.Elts))
	positions := make([]token.Pos, len(e.Elts))
	for i, el := range e.Elts {
		if kv, ok := el.(*ast.KeyValueExpr); ok {
			fc.expr(kv.Key)
			el = kv.Value
		}
		values[i], positions[i] = fc.expr(el), el.Pos()
	}
	if a == nil {
		a = fc.sliceShape(r, typ).args
		for _, first := range values {
			if isPointer(sl.Elem()) && fc.fl.st.AreEqual(first, fc.nilTerm()) {
				continue
			}
			v := first
			if isPointer(sl.Elem()) {
				v = fc.deref(v)
			}
			a = make([]term, len(a))
			for i, p := range fc.specs.Bounded(typ).Params {
				a[i] = fc.idx(v, p)
			}
			break
		}
	}
	fc.putSlice(r, typ, a)
	for i, v := range values {
		fc.storeSliceElement(positions[i], v, sl.Elem(), a)
	}
	// Пропуски в литералах []T{2: x} заполнены нулевыми значениями.
	next, size := int64(0), int64(0)
	for _, el := range e.Elts {
		if kv, ok := el.(*ast.KeyValueExpr); ok {
			next, _ = constant.Int64Val(fc.info.Types[kv.Key].Value)
		}
		next++
		if next > size {
			size = next
		}
	}
	if size > int64(len(values)) && !isPointer(sl.Elem()) {
		fc.storeSliceElement(e.Pos(), fc.zero(sl.Elem(), e.Pos()), sl.Elem(), a)
	}
	return r
}

func (fc *funcChecker) sliceBuiltin(call *ast.CallExpr) ([]term, bool) {
	if fc.isBuiltin(call.Fun, "make") && fc.sliceType(fc.info.TypeOf(call)) != nil {
		typ := fc.info.TypeOf(call)
		r := fc.fresh("make slice")
		a := slices.Clone(fc.sliceWant)
		annotated := a != nil
		fc.sliceWant = nil
		for _, arg := range call.Args[1:] {
			fc.expr(arg)
		}
		if a == nil {
			a = fc.sliceShape(r, typ).args
		}
		// Без доказательства нулевой длины возможны нулевые элементы.
		length := fc.info.Types[call.Args[1]].Value
		if length == nil || constant.Sign(length) != 0 {
			elem := fc.sliceType(typ).Elem()
			if !isPointer(elem) {
				z := fc.zero(elem, call.Pos())
				if !annotated {
					for i, p := range fc.specs.Bounded(typ).Params {
						a[i] = fc.idx(z, p)
					}
				}
				fc.storeSliceElement(call.Pos(), z, elem, a)
			}
		}
		fc.putSlice(r, typ, a)
		return []term{r}, true
	}
	if fc.isBuiltin(call.Fun, "append") && len(call.Args) > 0 && fc.sliceType(fc.info.TypeOf(call.Args[0])) != nil {
		typ := fc.info.TypeOf(call.Args[0])
		s := fc.expr(call.Args[0])
		a := fc.sliceShape(s, typ).args
		for _, arg := range call.Args[1:] {
			v := fc.expr(arg)
			if call.Ellipsis.IsValid() {
				fc.compatibleSlice(arg.Pos(), fc.sliceShape(v, fc.info.TypeOf(arg)).args, a, "append")
			} else {
				fc.storeSliceElement(arg.Pos(), v, fc.sliceType(typ).Elem(), a)
			}
		}
		r := fc.fresh("append")
		fc.putSlice(r, typ, a)
		return []term{r}, true
	}
	if fc.isBuiltin(call.Fun, "copy") && len(call.Args) == 2 && fc.sliceType(fc.info.TypeOf(call.Args[0])) != nil {
		d, s := fc.expr(call.Args[0]), fc.expr(call.Args[1])
		fc.compatibleSlice(call.Pos(), fc.sliceShape(s, fc.info.TypeOf(call.Args[1])).args, fc.sliceShape(d, fc.info.TypeOf(call.Args[0])).args, "copy")
		return []term{fc.fresh("copy count")}, true
	}
	if fc.isBuiltin(call.Fun, "clear") && len(call.Args) == 1 && fc.sliceType(fc.info.TypeOf(call.Args[0])) != nil {
		typ := fc.info.TypeOf(call.Args[0])
		s := fc.expr(call.Args[0])
		elem := fc.sliceType(typ).Elem()
		fc.storeSliceElement(call.Pos(), fc.zero(elem, call.Pos()), elem, fc.sliceShape(s, typ).args)
		return nil, true
	}
	return nil, false
}

func (fc *funcChecker) localClose(node ast.Node, doc *ast.CommentGroup, typ types.Type) []bound.Expr {
	groups := fc.localComments[node]
	if doc != nil {
		groups = []*ast.CommentGroup{doc}
	}
	var result []bound.Expr
	for _, group := range groups {
		cs, errs := spec.ParseDoc(group)
		for _, err := range errs {
			fc.errorf(err.Pos, "%s", err.Msg)
		}
		for _, c := range cs {
			cl, ok := c.(*spec.Close)
			if !ok {
				fc.errorf(c.Pos(), "only close is allowed on a local declaration")
				continue
			}
			if result != nil {
				fc.errorf(c.Pos(), "duplicate close")
				continue
			}
			vars := map[string]*types.Var{}
			for v := range fc.fl.cur {
				vars[v.Name()] = v
			}
			// Выбираем ближайший объект с данным именем в области объявления.
			var inner *types.Scope
			for _, scope := range fc.info.Scopes {
				if scope.Contains(node.Pos()) && (inner == nil || scope.Pos() >= inner.Pos()) {
					inner = scope
				}
			}
			if inner != nil {
				for name := range vars {
					_, obj := inner.LookupParent(name, node.Pos())
					if v, ok := obj.(*types.Var); ok {
						vars[name] = v
					}
				}
			}
			for _, file := range fc.pkg.Files {
				if file.Pos() <= node.Pos() && node.End() <= file.End() {
					result = bound.ResolveSliceClose(file, fc.pkg.Types, fc.info, fc.specs, vars, typ, cl, func(p token.Pos, msg string) { fc.errorf(p, "%s", msg) })
				}
			}
		}
	}
	return result
}

func (fc *funcChecker) sliceExpr(e ast.Expr, want []term) term {
	previous := fc.sliceWant
	fc.sliceWant = nil
	switch x := ast.Unparen(e).(type) {
	case *ast.CompositeLit:
		fc.sliceWant = want
	case *ast.CallExpr:
		if fc.isBuiltin(x.Fun, "make") {
			fc.sliceWant = want
		}
	}
	t := fc.expr(e)
	if want != nil && fc.fl.st.AreEqual(t, fc.nilTerm()) {
		t = fc.fresh("nil slice")
		fc.fl.slices[t] = sliceInfo{args: want}
	}
	fc.sliceWant = previous
	return t
}

func (fc *funcChecker) checkSliceClose(pos token.Pos, t term, typ types.Type, args []bound.Expr, vars map[*types.Var]term, self term, what string) {
	fc.compatibleSlice(pos, fc.sliceShape(t, typ).args, fc.closeArgs(args, vars, self), what)
}

// При создании значения поля close задаёт контекст литералу/make.
// Индексы владельца, выводимые из поля, остаются задачей build.
func (fc *funcChecker) fieldExpr(e ast.Expr, owner types.Type, f *types.Var) term {
	fa := fc.specs.FieldSpec(owner, f)
	if fa != nil && fa.Close != nil && fc.sliceType(f.Type()) != nil {
		for _, a := range fa.Close {
			if _, ok := a.(*bound.SelfParam); ok {
				return fc.expr(e)
			}
		}
		return fc.sliceExpr(e, fc.closeArgs(fa.Close, nil, none))
	}
	return fc.expr(e)
}

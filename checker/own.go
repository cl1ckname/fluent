package checker

import (
	"fmt"
	"go/token"
	"go/types"
	"slices"
	"strings"
)

// Владеющие поля и регионы (ALIASING_DESIGN.md, §11.10).
//
// Запись адреса в владеющее поле блока переносит право на объект в регион
// этого блока: объект становится дочерним блоком, права хранятся только
// у корня региона. Слот — место владеющего поля: блок и путь внутри него.

// ownerRef — владелец дочернего блока: родитель и путь к слоту в нём.
type ownerRef struct {
	parent blockID
	path   []*types.Var
}

// slotKey — ключ слота для карты flow.children.
type slotKey struct {
	block blockID
	path  string
}

func pathKey(path []*types.Var) string {
	names := make([]string, len(path))
	for i, f := range path {
		names[i] = f.Name()
	}
	return strings.Join(names, ".")
}

// rootIn — корень региона блока b в состоянии f.
func rootIn(f *flow, b blockID) blockID {
	for range 64 {
		o, ok := f.owner[b]
		if !ok {
			return b
		}
		b = o.parent
	}
	return b
}

func (fc *funcChecker) root(b blockID) blockID { return rootIn(fc.fl, b) }

// roots — корни регионов блоков.
func (fc *funcChecker) roots(blocks []blockID) []blockID {
	var out []blockID
	for _, b := range blocks {
		if r := fc.root(b); !slices.Contains(out, r) {
			out = append(out, r)
		}
	}
	slices.Sort(out)
	return out
}

// permOf — права кадра на блок: права корня его региона.
func (fc *funcChecker) permOf(b blockID) perm {
	if p, ok := fc.fl.perms[fc.root(b)]; ok {
		return p
	}
	return perm{why: "access was lost"}
}

// slotName — как назвать слот в сообщениях: o.Acc.
func (fc *funcChecker) slotName(o ownerRef) string {
	return fc.blocks[o.parent] + "." + pathKey(o.path)
}

// childAt — дочерний блок в слоте (b, path). Если неизвестно, что там лежит,
// заводится символический дочерний блок (OWNLOAD).
func (fc *funcChecker) childAt(b blockID, path []*types.Var, elem types.Type) blockID {
	key := slotKey{b, pathKey(path)}
	if c, ok := fc.fl.children[key]; ok {
		return c
	}
	name := fc.blocks[b] + "." + pathKey(path)
	fc.blocks = append(fc.blocks, name)
	c := blockID(len(fc.blocks) - 1)
	fc.blockType[c] = elem
	fc.fl.content[c] = fc.fresh(name)
	fc.fl.owner[c] = ownerRef{parent: b, path: slices.Clone(path)}
	fc.fl.children[key] = c
	return c
}

// ownLoad — t = x.f для владеющего поля f в терме спецификации: указатель
// на дочерний блок слота (OWNLOAD), если x указывает в известное место.
func (fc *funcChecker) ownLoad(x term, f *types.Var, t term) {
	if fc.atEntry {
		return
	}
	if info := fc.pointsTo(x); info.exact {
		c := fc.childAt(info.blocks[0], append(slices.Clone(info.path), f), derefType(f.Type()))
		fc.fl.ptrs[t] = ptrInfo{blocks: []blockID{c}, dependent: true}
	}
}

// detachChildren — дочерние блоки b в состоянии f отсоединяются: что лежит
// в слотах b, больше неизвестно, а у отсоединённых блоков нет прав.
func (fc *funcChecker) detachChildren(f *flow, b blockID) {
	for key, c := range f.children {
		if key.block == b {
			delete(f.children, key)
			if o, ok := f.owner[c]; ok {
				delete(f.owner, c)
				f.perms[c] = perm{why: fc.slotName(o) + " may have been replaced"}
			}
		}
	}
}

// ownStore — запись указателя q (терм t) в слот (b, path) владеющего поля
// (OWNSTORE). Право на запись в регион b проверено вызывающим.
func (fc *funcChecker) ownStore(pos token.Pos, b blockID, path []*types.Var, t term, what, slot string) {
	key := slotKey{b, pathKey(path)}
	if old, ok := fc.fl.children[key]; ok {
		delete(fc.fl.children, key)
		delete(fc.fl.owner, old)
		fc.fl.perms[old] = perm{why: fmt.Sprintf("replaced in %s at line %d", slot, fc.line(pos))}
	}
	fc.writes = append(fc.writes, b)
	if fc.fl.st.AreEqual(t, fc.nilTerm()) {
		return
	}
	info := fc.pointsTo(t)
	cannot := func(format string, args ...any) {
		fc.errorf(pos, "cannot store %s in %s: %s", what, slot, fmt.Sprintf(format, args...))
	}
	switch {
	case !info.exact:
		cannot("%s does not point to a known object", what)
		return
	case len(info.path) > 0:
		cannot("%s points inside another object", what)
		return
	}
	q := info.blocks[0]
	if o, ok := fc.fl.owner[q]; ok {
		cannot("%s already belongs to %s", what, fc.slotName(o))
		return
	}
	if q == fc.root(b) {
		cannot("an object cannot own itself")
		return
	}
	p := fc.permOf(q)
	switch {
	case !p.readable():
		cannot("no access to %s: %s", what, p.why)
		return
	case !p.writable():
		cannot("only read access to %s: %s", what, p.why)
		return
	}
	delete(fc.fl.perms, q)
	fc.losses = append(fc.losses, loss{q, fmt.Sprintf("moved into %s at line %d", slot, fc.line(pos))})
	fc.fl.owner[q] = ownerRef{parent: b, path: slices.Clone(path)}
	fc.fl.children[key] = q
}

// ownPaths — пути к владеющим полям внутри значения типа t (через вложенные
// по значению структуры).
func (fc *funcChecker) ownPaths(t types.Type, depth int) [][]*types.Var {
	st, ok := t.Underlying().(*types.Struct)
	if !ok || depth == 0 {
		return nil
	}
	var out [][]*types.Var
	for f := range st.Fields() {
		switch {
		case fc.specs.Owning(f):
			out = append(out, []*types.Var{f})
		case !isPointer(f.Type()):
			for _, p := range fc.ownPaths(f.Type(), depth-1) {
				out = append(out, append([]*types.Var{f}, p...))
			}
		}
	}
	return out
}

// storeValue — значение val типа typ записывается в место (b, path) блока:
// владеющие поля значения переносят права в регион, остальные указатели
// утекают.
func (fc *funcChecker) storeValue(pos token.Pos, b blockID, path []*types.Var, val term, typ types.Type, what string) {
	if isPointer(typ) {
		return
	}
	for _, op := range fc.ownPaths(typ, 3) {
		t := val
		for _, f := range op {
			t = fc.field(t, f)
		}
		slot := slices.Concat(path, op)
		fc.ownStore(pos, b, slot, t, what+"."+pathKey(op), fc.blocks[b]+"."+pathKey(slot))
	}
	fc.escapeExcept(val, typ, fmt.Sprintf("stored in %s at line %d", what, fc.line(pos)), 2)
}

// escapeExcept — escape для значения, которое кладётся в блок: владеющие
// поля обработаны ownStore.
func (fc *funcChecker) escapeExcept(t term, typ types.Type, why string, depth int) {
	st, ok := typ.Underlying().(*types.Struct)
	if !ok {
		fc.escape(t, typ, why, depth)
		return
	}
	if depth == 0 {
		return
	}
	for f := range st.Fields() {
		if !fc.specs.Owning(f) && hasPointers(f.Type()) {
			fc.escapeExcept(fc.field(t, f), f.Type(), why, depth-1)
		}
	}
}

// joinOwners — владельцы и слоты, одинаковые в обеих ветках.
func joinOwners(a, b, out *flow) {
	for c, oa := range a.owner {
		if ob, ok := b.owner[c]; ok && oa.parent == ob.parent && slices.Equal(oa.path, ob.path) {
			out.owner[c] = oa
		}
	}
	for k, ca := range a.children {
		if cb, ok := b.children[k]; ok && ca == cb {
			out.children[k] = ca
		}
	}
}

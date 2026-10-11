package checker

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"slices"
)

// Слой прав доступа к зависимым полям (ALIASING_DESIGN.md, §11).
//
// Память, в которой лежат зависимые поля, разбита на блоки: объект за
// указателем или локальная переменная с взятым адресом. Права на блок держит
// кадр функции. Указатели связаны с блоками через термы congruence: указатель
// указывает в блок, если его терм равен терму, зарегистрированному в ptrs.
//
// Этап 2а: сводок функций ещё нет, поэтому любой вызов, получающий указатель
// в блок, считается неизвестным, и права на блок теряются. То же при утечке
// указателя в срез, map, кучу, глобальную переменную, канал или замыкание.

type blockID int

type permKind uint8

const (
	permNone   permKind = iota // доступа нет
	permSource                 // источник: Source(debt)
	permFrozen                 // источник с фантомным долгом: только чтение
	permRead                   // reads читательских токенов
)

// perm — ресурс кадра на блок (§5, §11.2). Держатели выданных токенов (H)
// появятся вместе со сводками функций.
type perm struct {
	kind  permKind
	debt  int
	reads int
	why   string // почему доступ потерян или ограничен — для диагностики
}

func (p perm) readable() bool {
	return p.kind == permSource || p.kind == permFrozen || p.kind == permRead && p.reads > 0
}

func (p perm) writable() bool { return p.kind == permSource && p.debt == 0 }

// meetPerm — ресурс после слияния ветвей (§11.5): удерживаемые токены
// по минимуму, долг не меньше максимума.
func meetPerm(a, b perm) perm {
	switch {
	case a.kind == permNone:
		return a
	case b.kind == permNone:
		return b
	case a.kind == permRead && b.kind == permRead:
		return perm{kind: permRead, reads: min(a.reads, b.reads)}
	case a.kind == permRead || b.kind == permRead:
		return perm{kind: permNone, why: "access differs between branches"}
	case a.kind == permSource && b.kind == permSource && a.debt == b.debt:
		return a
	}
	why := a.why
	if why == "" {
		why = b.why
	}
	return perm{kind: permFrozen, why: why}
}

// ptrInfo — куда указывает указатель: в какие блоки, по какому пути полей
// внутри блока и может ли через него быть доступ к зависимым полям
// (&x.value — не может).
type ptrInfo struct {
	blocks    []blockID
	path      []*types.Var // nil — на весь блок
	dependent bool
	exact     bool // в pointsTo: один блок и один путь, содержимое известно
}

// loss — потеря прав на блок, для переноса на состояния, которые
// восстанавливаются после цикла, switch или правой части && / ||.
type loss struct {
	block blockID
	why   string
}

type rootKind uint8

const (
	rootValue   rootKind = iota // значение, а не память: права не нужны
	rootBlocks                  // память блоков
	rootUnknown                 // память, о которой ничего не известно
)

// root — где лежит значение выражения.
type root struct {
	kind   rootKind
	blocks []blockID
	why    string // для rootUnknown
}

func (fc *funcChecker) line(pos token.Pos) int { return fc.pkg.Fset.Position(pos).Line }

// newBlock заводит блок типа typ с полным правом кадра и содержимым content.
// Для памяти переменной content = none: содержимое — её текущее значение.
func (fc *funcChecker) newBlock(name string, typ types.Type, content term) blockID {
	fc.blocks = append(fc.blocks, name)
	id := blockID(len(fc.blocks) - 1)
	fc.blockType[id] = typ
	fc.fl.perms[id] = perm{kind: permSource}
	if content != none {
		fc.fl.content[id] = content
	}
	return id
}

// content — текущая версия содержимого блока (§11.2, mem(ℓ)#v). При проверке
// returns (atEntry) — содержимое на входе в функцию.
func (fc *funcChecker) content(b blockID) term {
	if fc.atEntry {
		if t, ok := fc.entryContent[b]; ok {
			return t
		}
	}
	if v, ok := fc.blockVar[b]; ok {
		if t, ok := fc.fl.cur[v]; ok {
			return t
		}
		return fc.fresh(v.Name())
	}
	if t, ok := fc.fl.content[b]; ok {
		return t
	}
	return fc.fresh(fc.blocks[b])
}

// setContent — новая версия содержимого блока.
func (fc *funcChecker) setContent(b blockID, t term) {
	if v, ok := fc.blockVar[b]; ok {
		fc.fl.cur[v] = t
	} else {
		fc.fl.content[b] = t
	}
	fc.writes = append(fc.writes, b)
}

// havocBlocks — содержимое блоков, записанных после mark, в состоянии f
// неизвестно (после цикла или switch, где записи были не на всех путях).
func (fc *funcChecker) havocBlocks(f *flow, mark int) {
	seen := map[blockID]bool{}
	for _, b := range fc.writes[mark:] {
		if seen[b] {
			continue
		}
		seen[b] = true
		fc.forget(f, b)
	}
}

// derefBlock — значение *p, если p указывает в известное место известного блока.
func (fc *funcChecker) derefBlock(p term) (term, bool) {
	info := fc.pointsTo(p)
	if !info.exact {
		return none, false
	}
	b := info.blocks[0]
	t, typ := fc.content(b), fc.blockType[b]
	for _, f := range info.path {
		t = fc.fieldRead(t, typ, f, true)
		typ = f.Type()
	}
	return t, true
}

// writeAt записывает val по пути path внутри блока b: на каждом уровне
// строится новая версия родителя (rebuild проверяет инварианты).
func (fc *funcChecker) writeAt(pos token.Pos, b blockID, path []*types.Var, val term, what string) {
	if len(path) == 0 {
		fc.setContent(b, val)
		return
	}
	parent, typ := fc.content(b), fc.blockType[b]
	for _, f := range path[:len(path)-1] {
		parent = fc.fieldRead(parent, typ, f, true)
		typ = f.Type()
	}
	nb, ok := fc.rebuild(pos, parent, typ, path[len(path)-1], val, true, true, what, what)
	if ok {
		fc.writeAt(pos, b, path[:len(path)-1], nb, what)
	}
}

// pointsTo — блоки, в которые может указывать указатель t, и есть ли
// через него доступ к зависимым полям. Пусто, если t ни с чем не связан.
// Несколько блоков бывает, если равенство указателей предположено условием.
func (fc *funcChecker) pointsTo(t term) ptrInfo {
	var out ptrInfo
	matches := 0
	for k, info := range fc.fl.ptrs {
		if fc.fl.st.AreEqual(t, k) {
			matches++
			for _, b := range info.blocks {
				if !slices.Contains(out.blocks, b) {
					out.blocks = append(out.blocks, b)
				}
			}
			out.dependent = out.dependent || info.dependent
			if matches == 1 {
				out.path, out.exact = info.path, len(info.blocks) == 1
			} else if !slices.Equal(out.path, info.path) {
				out.exact = false
			}
		}
	}
	slices.Sort(out.blocks)
	out.exact = out.exact && len(out.blocks) == 1 && !slices.Contains(out.path, nil)
	return out
}

func (fc *funcChecker) suppressed(e ast.Expr) bool { return fc.suppress[ast.Unparen(e)] }

// noAccess — выражение e вычисляется не как чтение значения из памяти
// (база x.f, операнд &x, неявный &x у receiver-а).
func (fc *funcChecker) noAccess(e ast.Expr) { fc.suppress[ast.Unparen(e)] = true }

// memRoot — память, в которой лежит значение выражения e. Термы указателей
// внутри e уже вычислены и лежат в fc.terms.
func (fc *funcChecker) memRoot(e ast.Expr) root {
	switch e := ast.Unparen(e).(type) {
	case *ast.Ident:
		v := fc.varOf(e)
		if v == nil {
			return root{}
		}
		if !fc.isLocal(v) {
			return root{kind: rootUnknown, why: e.Name + " is a global variable"}
		}
		if b, ok := fc.fl.varBlk[v]; ok {
			return root{kind: rootBlocks, blocks: []blockID{b}}
		}
		if _, ok := fc.fl.cur[v]; !ok && fc.specs.Dependent(v.Type()) {
			return root{kind: rootUnknown, why: e.Name + " is captured from the enclosing function"}
		}
		return root{}
	case *ast.SelectorExpr:
		sel := fc.info.Selections[e]
		if sel == nil || sel.Kind() != types.FieldVal {
			return root{}
		}
		if len(sel.Index()) != 1 {
			// Поле встроенной структуры: та же память, что у e.X, если по пути
			// нет встроенных указателей.
			if embeddedPointer(sel) {
				return root{kind: rootUnknown, why: "fields promoted through embedded pointers are not supported"}
			}
		}
		if isPointer(fc.info.TypeOf(e.X)) {
			return fc.ptrRoot(e.X)
		}
		return fc.memRoot(e.X)
	case *ast.StarExpr:
		return fc.ptrRoot(e.X)
	case *ast.IndexExpr:
		if _, ok := fc.info.TypeOf(e.X).Underlying().(*types.Array); ok {
			return fc.memRoot(e.X)
		}
		return root{kind: rootUnknown, why: "elements of slices, maps and arrays behind pointers are not tracked"}
	}
	return root{}
}

// ptrRoot — память, на которую указывает уже вычисленный указатель x.
func (fc *funcChecker) ptrRoot(x ast.Expr) root {
	t, ok := fc.terms[ast.Unparen(x)]
	if !ok {
		return root{kind: rootUnknown, why: types.ExprString(x) + " does not point to a known object"}
	}
	info := fc.pointsTo(t)
	if len(info.blocks) == 0 {
		return root{kind: rootUnknown, why: types.ExprString(x) + " does not point to a known object"}
	}
	return root{kind: rootBlocks, blocks: info.blocks}
}

// checkRoot проверяет право на чтение или запись e, лежащего в памяти r.
func (fc *funcChecker) checkRoot(pos token.Pos, e ast.Expr, r root, write bool) bool {
	verb := "read"
	if write {
		verb = "write"
	}
	switch r.kind {
	case rootUnknown:
		fc.errorf(pos, "cannot %s %s: %s", verb, types.ExprString(e), r.why)
		return false
	case rootBlocks:
		fc.record(r.blocks, write)
		for _, b := range r.blocks {
			p := fc.permOf(b)
			switch {
			case !p.readable():
				fc.errorf(pos, "cannot %s %s: no access: %s", verb, types.ExprString(e), p.why)
				return false
			case write && !p.writable():
				fc.errorf(pos, "cannot %s %s: read-only access: %s", verb, types.ExprString(e), p.why)
				return false
			}
		}
	}
	return true
}

// checkPtr проверяет доступ к *p через уже вычисленный указатель pt.
func (fc *funcChecker) checkPtr(pos token.Pos, e *ast.StarExpr, pt term, write bool) bool {
	info := fc.pointsTo(pt)
	if !info.dependent && !fc.specs.Dependent(fc.info.TypeOf(e)) {
		return true
	}
	r := root{kind: rootBlocks, blocks: info.blocks}
	if len(info.blocks) == 0 {
		r = root{kind: rootUnknown, why: types.ExprString(e.X) + " does not point to a known object"}
	}
	return fc.checkRoot(pos, e, r, write)
}

// dependentField — защищено ли правами поле f структуры st.
func (fc *funcChecker) dependentField(st types.Type, f *types.Var) bool {
	return fc.specs.FieldSpec(st, f) != nil || fc.specs.Dependent(f.Type())
}

// addrOf связывает указатель p = &x с памятью x (правила NEW, ADDR, FADDR).
func (fc *funcChecker) addrOf(p term, x ast.Expr) {
	x = ast.Unparen(x)
	typ := fc.info.TypeOf(x)
	if lit, ok := x.(*ast.CompositeLit); ok {
		// &T{...}: новый блок. Владеющие поля переносят права в него,
		// остальные указатели из полей литерала утекают в кучу.
		content, _ := fc.terms[lit]
		b := blockID(-1)
		if fc.specs.Tracked(typ) {
			b = fc.newBlock(fmt.Sprintf("(&%s at line %d)", types.TypeString(typ, types.RelativeTo(fc.pkg.Types)), fc.line(x.Pos())), typ, content)
			fc.fl.ptrs[p] = ptrInfo{blocks: []blockID{b}, dependent: true}
		}
		st, _ := typ.Underlying().(*types.Struct)
		for i, el := range lit.Elts {
			var f *types.Var
			if kv, ok := el.(*ast.KeyValueExpr); ok {
				if id, ok := kv.Key.(*ast.Ident); ok {
					f, _ = fc.info.Uses[id].(*types.Var)
				}
				el = kv.Value
			} else if st != nil && i < st.NumFields() {
				f = st.Field(i)
			}
			t, ok := fc.terms[ast.Unparen(el)]
			if !ok {
				continue
			}
			if b >= 0 && f != nil && fc.specs.Owning(f) {
				fc.ownStore(el.Pos(), b, []*types.Var{f}, t, types.ExprString(el), fc.blocks[b]+"."+f.Name())
				continue
			}
			fc.escape(t, fc.info.TypeOf(el), fmt.Sprintf("stored in a new object at line %d", fc.line(el.Pos())), 2)
		}
		return
	}
	dep := fc.specs.Tracked(typ)
	if sel, ok := x.(*ast.SelectorExpr); ok {
		if s := fc.info.Selections[sel]; s != nil && s.Kind() == types.FieldVal {
			dep = dep || fc.specs.FieldSpec(derefType(fc.info.TypeOf(sel.X)), s.Obj().(*types.Var)) != nil
		}
	}
	if !dep {
		return
	}
	if b, path, ok := fc.place(x); ok {
		fc.fl.ptrs[p] = ptrInfo{blocks: []blockID{b}, path: path, dependent: true}
	} else if r := fc.memRoot(x); r.kind == rootBlocks {
		// Блок известен, место внутри — нет: права проверяются, содержимое
		// через такой указатель неизвестно.
		fc.fl.ptrs[p] = ptrInfo{blocks: r.blocks, path: []*types.Var{nil}, dependent: true}
	}
}

// place — точное место значения e: блок и путь полей внутри него.
func (fc *funcChecker) place(e ast.Expr) (blockID, []*types.Var, bool) {
	switch e := ast.Unparen(e).(type) {
	case *ast.Ident:
		if v := fc.varOf(e); v != nil {
			if b, ok := fc.fl.varBlk[v]; ok {
				return b, nil, true
			}
		}
	case *ast.StarExpr:
		if t, ok := fc.terms[ast.Unparen(e.X)]; ok {
			if info := fc.pointsTo(t); info.exact {
				return info.blocks[0], info.path, true
			}
		}
	case *ast.SelectorExpr:
		sel := fc.info.Selections[e]
		if sel == nil || sel.Kind() != types.FieldVal || embeddedPointer(sel) {
			return 0, nil, false
		}
		var b blockID
		var path []*types.Var
		if isPointer(fc.info.TypeOf(e.X)) {
			t, ok := fc.terms[ast.Unparen(e.X)]
			if !ok {
				return 0, nil, false
			}
			info := fc.pointsTo(t)
			if !info.exact {
				return 0, nil, false
			}
			b, path = info.blocks[0], info.path
		} else {
			var ok bool
			if b, path, ok = fc.place(e.X); !ok {
				return 0, nil, false
			}
		}
		path = slices.Clone(path)
		t := derefType(sel.Recv())
		for _, j := range sel.Index() {
			f := t.Underlying().(*types.Struct).Field(j)
			path = append(path, f)
			t = f.Type()
		}
		return b, path, true
	}
	return 0, nil, false
}

// lose отбирает у кадра права на блоки, в которые может указывать t.
// Без прав содержимое блока неизвестно: в него может писать кто угодно.
func (fc *funcChecker) lose(blocks []blockID, why string) {
	for _, b := range fc.roots(blocks) {
		if p, ok := fc.fl.perms[b]; ok && p.kind != permNone {
			fc.fl.perms[b] = perm{why: why}
			fc.losses = append(fc.losses, loss{b, why})
			fc.forget(fc.fl, b)
		}
	}
}

// forget — содержимое блока b в состоянии f становится неизвестным.
func (fc *funcChecker) forget(f *flow, b blockID) {
	t := fc.fresh(fc.blocks[b])
	if v, ok := fc.blockVar[b]; ok {
		if _, ok := f.cur[v]; ok {
			f.cur[v] = t
		}
	} else if _, ok := f.content[b]; ok {
		f.content[b] = t
	}
	fc.detachChildren(f, b)
}

// escape — значение t типа typ уходит туда, где анализ его не видит:
// права на все блоки, достижимые из него, теряются.
func (fc *funcChecker) escape(t term, typ types.Type, why string, depth int) {
	if typ == nil {
		return
	}
	switch u := typ.Underlying().(type) {
	case *types.Pointer, *types.Interface:
		fc.lose(fc.pointsTo(t).blocks, why)
	case *types.Struct:
		if depth == 0 {
			return
		}
		for f := range u.Fields() {
			if hasPointers(f.Type()) {
				fc.escape(fc.field(t, f), f.Type(), why, depth-1)
			}
		}
	}
}

// hasPointers — может ли значение типа t содержать указатель на блок.
func hasPointers(t types.Type) bool {
	switch u := t.Underlying().(type) {
	case *types.Pointer, *types.Interface:
		return true
	case *types.Struct:
		for f := range u.Fields() {
			if hasPointers(f.Type()) {
				return true
			}
		}
	}
	return false
}

// escapeCall — аргументы и receiver вызова без сводки (этап 2а: любого).
func (fc *funcChecker) escapeCall(call *ast.CallExpr, fn *types.Func, name string, recv term, recvType types.Type, args []ast.Expr, argTerms []term) {
	if readsOnly(fn) {
		return
	}
	if id, ok := ast.Unparen(call.Fun).(*ast.Ident); ok {
		if b, ok := fc.info.Uses[id].(*types.Builtin); ok {
			switch b.Name() {
			case "len", "cap", "delete", "close", "clear", "min", "max", "complex", "real", "imag", "new", "panic":
				return
			}
		}
	}
	why := fmt.Sprintf("passed to %s at line %d", name, fc.line(call.Lparen))
	if recv != none {
		fc.escape(recv, recvType, why, 2)
	}
	if len(args) != len(argTerms) {
		return // f(g()): результаты g — свежие термы
	}
	for i, a := range args {
		fc.escape(argTerms[i], fc.info.TypeOf(a), why, 2)
	}
}

// escapeCaptures — замыкание захватывает переменные по ссылке: права на их
// память и на то, куда указывают их значения, уходят в замыкание.
func (fc *funcChecker) escapeCaptures(lit *ast.FuncLit) {
	why := fmt.Sprintf("captured by a closure at line %d", fc.line(lit.Pos()))
	seen := map[*types.Var]bool{}
	ast.Inspect(lit.Body, func(n ast.Node) bool {
		id, ok := n.(*ast.Ident)
		if !ok {
			return true
		}
		v, ok := fc.info.Uses[id].(*types.Var)
		if !ok || seen[v] || !fc.isLocal(v) || (v.Pos() >= lit.Pos() && v.Pos() < lit.End()) {
			return true
		}
		seen[v] = true
		if b, ok := fc.fl.varBlk[v]; ok {
			fc.lose([]blockID{b}, why)
		}
		if t, ok := fc.fl.cur[v]; ok {
			fc.escape(t, v.Type(), why, 2)
		}
		return true
	})
}

// applyLosses переносит потери прав, случившиеся после mark, на состояние f
// (которое восстанавливается вместо текущего).
func (fc *funcChecker) applyLosses(f *flow, mark int) {
	for _, l := range fc.losses[mark:] {
		b := rootIn(f, l.block)
		if p, ok := f.perms[b]; ok && p.kind != permNone {
			f.perms[b] = perm{why: l.why}
			fc.forget(f, b)
		}
	}
}

// joinAlias сливает права и связи указателей двух ветвей.
func joinAlias(a, b, out *flow) {
	for k, ia := range a.ptrs {
		if ib, ok := b.ptrs[k]; ok && slices.Equal(ia.blocks, ib.blocks) && slices.Equal(ia.path, ib.path) {
			out.ptrs[k] = ptrInfo{blocks: ia.blocks, path: ia.path, dependent: ia.dependent || ib.dependent}
		}
	}
	for id, pa := range a.perms {
		if pb, ok := b.perms[id]; ok {
			out.perms[id] = meetPerm(pa, pb)
		}
	}
	for v, ba := range a.varBlk {
		if bb, ok := b.varBlk[v]; ok && ba == bb {
			out.varBlk[v] = ba
		}
	}
	joinOwners(a, b, out)
}

// embeddedPointer — есть ли на пути к полю встроенный указатель.
func embeddedPointer(sel *types.Selection) bool {
	t := sel.Recv()
	idx := sel.Index()
	for _, j := range idx[:len(idx)-1] {
		st, ok := derefType(t).Underlying().(*types.Struct)
		if !ok {
			return true
		}
		t = st.Field(j).Type()
		if isPointer(t) {
			return true
		}
	}
	return false
}

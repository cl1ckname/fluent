package checker

import (
	"fmt"
	"go/ast"
	"go/types"
	"maps"
	"slices"
	"strings"
)

// Сводки функций пакета (ALIASING_DESIGN.md, §11.4, §11.8). Выводятся из тел
// функций снизу вверх по графу вызовов; рекурсия — неподвижной точкой.

type access uint8

const (
	accNone access = iota
	accRead
	accWrite
)

// summary — что функция делает с памятью, переданной через параметры-указатели.
// Параметры по позициям: receiver (если есть) первым, затем параметры.
type summary struct {
	params  []paramSum
	results []resultSum
}

type paramSum struct {
	access access // Pre: какое право нужно на память, куда указывает параметр
	kept   string // не "" — права не возвращаются (Keep), почему
	// Объект параметра перенесён во владеющий слот: ownTo >= 0 — параметра
	// с этим номером, ownTo <= -2 — результата номер -2-ownTo; -1 — нет.
	ownTo   int
	ownPath []*types.Var
	wrote   bool // функция сама писала в объект (для перенесённых)
}

type resultSum struct {
	fresh bool         // указатель на новый объект с полным правом (Fresh)
	alias int          // >= 0 — указатель в память параметра с этим номером
	slot  []*types.Var // не nil — во владеющий слот параметра по этому пути
	path  []*types.Var // путь внутри памяти (параметра или объекта в слоте)
}

func (s *summary) equal(o *summary) bool {
	return slices.EqualFunc(s.params, o.params, func(a, b paramSum) bool {
		return a.access == b.access && a.kept == b.kept && a.ownTo == b.ownTo && slices.Equal(a.ownPath, b.ownPath) && a.wrote == b.wrote
	}) && slices.EqualFunc(s.results, o.results, func(a, b resultSum) bool {
		return a.fresh == b.fresh && a.alias == b.alias && slices.Equal(a.slot, b.slot) && slices.Equal(a.path, b.path)
	})
}

// sigParams — параметры по позициям сводки.
func sigParams(sig *types.Signature) []*types.Var {
	var out []*types.Var
	if sig.Recv() != nil {
		out = append(out, sig.Recv())
	}
	for v := range sig.Params().Variables() {
		out = append(out, v)
	}
	return out
}

// emptySummary — начальная сводка для неподвижной точки: ничего не нужно,
// всё возвращается, результаты неизвестны.
func emptySummary(sig *types.Signature) *summary {
	s := &summary{params: make([]paramSum, len(sigParams(sig))), results: make([]resultSum, sig.Results().Len())}
	for i := range s.params {
		s.params[i].ownTo = -1
	}
	for i := range s.results {
		s.results[i].alias = -1
	}
	return s
}

// topSummary — сводка, верная для любого тела: всё нужно на запись и
// не возвращается.
func topSummary(sig *types.Signature) *summary {
	s := emptySummary(sig)
	for i, v := range sigParams(sig) {
		if isPointer(v.Type()) {
			s.params[i] = paramSum{access: accWrite, kept: "recursion is too deep to summarize", ownTo: -1}
		}
	}
	return s
}

// ---- граф вызовов ----

type funcDecl struct {
	obj  *types.Func
	decl *ast.FuncDecl
}

// callees — функции пакета, которые decl вызывает статически.
func (c *checker) callees(decl *ast.FuncDecl, local map[*types.Func]bool) []*types.Func {
	var out []*types.Func
	ast.Inspect(decl.Body, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		var fn *types.Func
		switch f := ast.Unparen(call.Fun).(type) {
		case *ast.Ident:
			fn, _ = c.info.Uses[f].(*types.Func)
		case *ast.SelectorExpr:
			if sel := c.info.Selections[f]; sel != nil {
				fn, _ = sel.Obj().(*types.Func)
			} else {
				fn, _ = c.info.Uses[f.Sel].(*types.Func)
			}
		}
		if fn != nil && local[fn.Origin()] && !slices.Contains(out, fn.Origin()) {
			out = append(out, fn.Origin())
		}
		return true
	})
	return out
}

// sccs — компоненты сильной связности (Тарьян) в порядке «вызываемые раньше».
func (c *checker) sccs(funcs []funcDecl) [][]funcDecl {
	byObj := map[*types.Func]funcDecl{}
	local := map[*types.Func]bool{}
	for _, f := range funcs {
		byObj[f.obj], local[f.obj] = f, true
	}
	index, low := map[*types.Func]int{}, map[*types.Func]int{}
	onStack := map[*types.Func]bool{}
	var stack []*types.Func
	var out [][]funcDecl
	next := 0
	var visit func(f *types.Func)
	visit = func(f *types.Func) {
		index[f], low[f] = next, next
		next++
		stack = append(stack, f)
		onStack[f] = true
		for _, g := range c.callees(byObj[f].decl, local) {
			if _, seen := index[g]; !seen {
				visit(g)
				low[f] = min(low[f], low[g])
			} else if onStack[g] {
				low[f] = min(low[f], index[g])
			}
		}
		if low[f] == index[f] {
			var comp []funcDecl
			for {
				g := stack[len(stack)-1]
				stack = stack[:len(stack)-1]
				onStack[g] = false
				comp = append(comp, byObj[g])
				if g == f {
					break
				}
			}
			out = append(out, comp)
		}
	}
	for _, f := range funcs {
		if _, seen := index[f.obj]; !seen {
			visit(f.obj)
		}
	}
	return out
}

// recursive — вызывает ли функция компоненты саму себя.
func (c *checker) recursive(comp []funcDecl) bool {
	if len(comp) > 1 {
		return true
	}
	return slices.Contains(c.callees(comp[0].decl, map[*types.Func]bool{comp[0].obj: true}), comp[0].obj)
}

// summarize выводит сводки всех функций пакета (молча).
func (c *checker) summarize(funcs []funcDecl) {
	c.summaries = map[*types.Func]*summary{}
	if c.pkg.Imports != nil {
		maps.Copy(c.summaries, c.pkg.Imports.summaries)
	}
	c.silent++
	defer func() { c.silent-- }()
	for _, comp := range c.sccs(funcs) {
		check := func(f funcDecl) *summary {
			return c.checkFunc(f.obj.Type().(*types.Signature), f.decl.Body, c.specs.Funcs[f.obj])
		}
		if !c.recursive(comp) {
			c.summaries[comp[0].obj] = check(comp[0])
			continue
		}
		for _, f := range comp {
			c.summaries[f.obj] = emptySummary(f.obj.Type().(*types.Signature))
		}
		stable := false
		for range 10 {
			stable = true
			for _, f := range comp {
				if s := check(f); !s.equal(c.summaries[f.obj]) {
					c.summaries[f.obj], stable = s, false
				}
			}
			if stable {
				break
			}
		}
		if !stable {
			for _, f := range comp {
				c.summaries[f.obj] = topSummary(f.obj.Type().(*types.Signature))
			}
		}
	}
}

// ---- сторона вызываемой функции: сбор сводки ----

// record — доступ к блокам (для вывода Pre).
func (fc *funcChecker) record(blocks []blockID, write bool) {
	a := accRead
	if write {
		a = accWrite
	}
	for _, b := range fc.roots(blocks) {
		fc.acc[b] = max(fc.acc[b], a)
	}
}

// exit — состояние на выходе из функции с результатами vals (nil — без результатов).
func (fc *funcChecker) exit(vals []term) {
	if fc.fl.dead || fc.fl.st.Inconsistent() || fc.sum == nil {
		return
	}
	for i, b := range fc.paramBlocks {
		ps := &fc.sum.params[i]
		if b < 0 || ps.kept != "" {
			continue
		}
		if o, ok := fc.fl.owner[b]; ok {
			to, path := fc.ownTarget(o, vals)
			switch {
			case to == -1:
				ps.kept = fmt.Sprintf("moved into %s", fc.slotName(o))
			case fc.exited && (ps.ownTo != to || !slices.Equal(ps.ownPath, path)):
				ps.kept, ps.ownTo, ps.ownPath = fmt.Sprintf("moved into %s", fc.slotName(o)), -1, nil
			default:
				ps.ownTo, ps.ownPath = to, path
			}
			continue
		}
		if fc.exited && ps.ownTo != -1 {
			ps.kept, ps.ownTo, ps.ownPath = "moved into another object on some paths", -1, nil
			continue
		}
		if p, ok := fc.fl.perms[b]; !ok || p.kind == permNone {
			ps.kept = p.why
		}
	}
	if len(vals) != len(fc.sum.results) {
		return
	}
	for i, t := range vals {
		r := fc.classify(t, vals[:i])
		switch {
		case !fc.exited:
			fc.sum.results[i] = r
		case r.alias == -2: // nil: подходит к любому
		case fc.sum.results[i].alias == -2:
			fc.sum.results[i] = r
		case r.fresh != fc.sum.results[i].fresh || r.alias != fc.sum.results[i].alias ||
			!slices.Equal(r.slot, fc.sum.results[i].slot) || !slices.Equal(r.path, fc.sum.results[i].path):
			fc.sum.results[i] = resultSum{alias: -1}
		}
	}
	fc.exited = true
}

// classify — что такое указатель t в результате: alias = -2 для nil.
func (fc *funcChecker) classify(t term, earlier []term) resultSum {
	if fc.fl.st.AreEqual(t, fc.nilTerm()) {
		return resultSum{alias: -2}
	}
	info := fc.pointsTo(t)
	if !info.exact {
		return resultSum{alias: -1}
	}
	b := info.blocks[0]
	if i := slices.Index(fc.paramBlocks, b); i >= 0 {
		if _, owned := fc.fl.owner[b]; !owned {
			return resultSum{alias: i, path: info.path}
		}
		return resultSum{alias: -1}
	}
	if o, ok := fc.fl.owner[b]; ok {
		if i := slices.Index(fc.paramBlocks, o.parent); i >= 0 {
			if _, owned := fc.fl.owner[o.parent]; !owned {
				return resultSum{alias: i, slot: o.path, path: info.path}
			}
		}
		return resultSum{alias: -1}
	}
	for _, e := range earlier {
		if fc.fl.st.AreEqual(t, e) {
			return resultSum{alias: -1} // один свежий объект в двух результатах
		}
	}
	if _, isVar := fc.blockVar[b]; !isVar && len(info.path) == 0 && fc.fl.perms[b].writable() && !fc.isParamPart(b) {
		return resultSum{fresh: true, alias: -1}
	}
	return resultSum{alias: -1}
}

// ownTarget — куда перенесён объект параметра: в слот параметра (номер)
// или свежего результата (-2-номер); -1 — в другое место.
func (fc *funcChecker) ownTarget(o ownerRef, vals []term) (int, []*types.Var) {
	if _, owned := fc.fl.owner[o.parent]; owned {
		return -1, nil
	}
	if i := slices.Index(fc.paramBlocks, o.parent); i >= 0 {
		return i, o.path
	}
	for r, t := range vals {
		if info := fc.pointsTo(t); info.exact && info.blocks[0] == o.parent && len(info.path) == 0 {
			return -2 - r, o.path
		}
	}
	return -1, nil
}

func (fc *funcChecker) isParamPart(b blockID) bool { return slices.Contains(fc.paramBlocks, b) }

// finishSummary — сводка по собранным доступам и выходам.
func (fc *funcChecker) finishSummary() *summary {
	s := fc.sum
	for i, b := range fc.paramBlocks {
		if b < 0 {
			continue
		}
		s.params[i].access = fc.acc[b]
		s.params[i].wrote = fc.acc[b] == accWrite
		if s.params[i].kept != "" || s.params[i].ownTo != -1 {
			// Удержанную или перенесённую память новый держатель может менять.
			s.params[i].access = accWrite
		}
	}
	for i := range s.results {
		if s.results[i].alias == -2 {
			s.results[i] = resultSum{alias: -1}
		}
	}
	return s
}

// ---- сторона вызывающего: правило вызова ----

// applyCall — правило вызова §11.4 для функции со сводкой s. params и
// argTerms — параметры по позициям сводки и их значения; names — тексты
// аргументов. Возвращает false, если сводки нет.
func (fc *funcChecker) applyCall(call *ast.CallExpr, fn *types.Func, params []*types.Var, argTerms []term, names []string, results []term) bool {
	if fn == nil {
		return false
	}
	s := fc.summaries[fn.Origin()]
	if s == nil {
		return false
	}
	name := fc.funcName(fn)
	type demand struct {
		write bool
		args  []string
	}
	demands := map[blockID]*demand{}
	var order []blockID
	infos := make([]ptrInfo, len(params))
	for i, v := range params {
		if i >= len(s.params) || argTerms[i] == none {
			continue
		}
		ps := s.params[i]
		if !isPointer(v.Type()) {
			fc.escape(argTerms[i], v.Type(), fmt.Sprintf("passed to %s at line %d", name, fc.line(call.Lparen)), 2)
			continue
		}
		infos[i] = fc.pointsTo(argTerms[i])
		if ps.access == accNone {
			continue
		}
		if len(infos[i].blocks) == 0 {
			if fc.specs.Tracked(derefType(v.Type())) {
				fc.errorf(call.Lparen, "cannot pass %s to %s: %s does not point to a known object", names[i], name, names[i])
			}
			continue
		}
		for _, b := range fc.roots(infos[i].blocks) {
			d := demands[b]
			if d == nil {
				d = &demand{}
				demands[b] = d
				order = append(order, b)
			}
			d.write = d.write || ps.access == accWrite
			d.args = append(d.args, names[i])
		}
	}
	for _, b := range order {
		d := demands[b]
		fc.record([]blockID{b}, d.write)
		p := fc.permOf(b)
		switch {
		case d.write && len(d.args) > 1:
			fc.errorf(call.Lparen, "cannot pass %s to %s: the same object is passed more than once and %s may write to it",
				strings.Join(d.args, " and "), name, name)
		case !p.readable():
			fc.errorf(call.Lparen, "cannot pass %s to %s: no access: %s", d.args[0], name, p.why)
		case d.write && !p.writable():
			fc.errorf(call.Lparen, "cannot pass %s to %s: %s may write to it, but access is read-only: %s", d.args[0], name, name, p.why)
		}
	}
	// После вызова: удержанное теряется, записанное — новая версия.
	for i, ps := range s.params {
		if i >= len(infos) || len(infos[i].blocks) == 0 {
			continue
		}
		switch {
		case ps.kept != "":
			fc.lose(infos[i].blocks, fmt.Sprintf("kept by %s at line %d (%s)", name, fc.line(call.Lparen), ps.kept))
		case ps.ownTo != -1:
			// Перенос — ниже, после результатов: слот может быть в новом объекте.
		case ps.access == accWrite:
			for _, b := range infos[i].blocks {
				fc.forget(fc.fl, b)
				fc.writes = append(fc.writes, b)
			}
		}
	}
	fresh := make([]blockID, len(results))
	for i, r := range s.results {
		fresh[i] = -1
		if i >= len(results) {
			break
		}
		rt := derefType(fn.Type().(*types.Signature).Results().At(i).Type())
		switch {
		case r.fresh:
			fresh[i] = fc.newBlock(fmt.Sprintf("(%s() at line %d)", name, fc.line(call.Lparen)), rt, fc.fresh(name+"()"))
			fc.fl.ptrs[results[i]] = ptrInfo{blocks: []blockID{fresh[i]}, dependent: true}
		case r.alias >= 0 && r.alias < len(infos) && len(infos[r.alias].blocks) > 0:
			info := infos[r.alias]
			switch {
			case r.slot != nil && info.exact:
				c := fc.childAt(info.blocks[0], slices.Concat(info.path, r.slot), derefType(r.slot[len(r.slot)-1].Type()))
				fc.fl.ptrs[results[i]] = ptrInfo{blocks: []blockID{c}, path: r.path, dependent: true}
			case r.slot != nil:
			case info.exact:
				fc.fl.ptrs[results[i]] = ptrInfo{blocks: info.blocks, path: slices.Concat(info.path, r.path), dependent: true}
			default:
				fc.fl.ptrs[results[i]] = ptrInfo{blocks: info.blocks, path: []*types.Var{nil}, dependent: true}
			}
		}
	}
	// Перенос объектов параметров во владеющие слоты (§11.10).
	for i, ps := range s.params {
		if ps.ownTo == -1 || i >= len(infos) || !infos[i].exact {
			continue
		}
		q := infos[i].blocks[0]
		if ps.wrote {
			fc.forget(fc.fl, q)
			fc.writes = append(fc.writes, q)
		}
		var parent blockID
		var path []*types.Var
		switch {
		case ps.ownTo >= 0 && ps.ownTo < len(infos) && infos[ps.ownTo].exact:
			parent, path = infos[ps.ownTo].blocks[0], slices.Concat(infos[ps.ownTo].path, ps.ownPath)
		case ps.ownTo <= -2 && -2-ps.ownTo < len(fresh) && fresh[-2-ps.ownTo] >= 0:
			parent, path = fresh[-2-ps.ownTo], ps.ownPath
		default:
			fc.lose([]blockID{q}, fmt.Sprintf("moved by %s at line %d", name, fc.line(call.Lparen)))
			continue
		}
		fc.ownStore(call.Lparen, parent, path, argTerms[i], names[i], fc.blocks[parent]+"."+pathKey(path))
	}
	return true
}

// readsOnly — функции других пакетов, которые только читают аргументы.
func readsOnly(fn *types.Func) bool {
	if fn == nil || fn.Pkg() == nil {
		return false
	}
	name := fn.Name()
	switch fn.Pkg().Path() {
	case "fmt":
		return strings.HasPrefix(name, "Print") || strings.HasPrefix(name, "Sprint") ||
			strings.HasPrefix(name, "Fprint") || name == "Errorf"
	case "log":
		return strings.HasPrefix(name, "Print") || strings.HasPrefix(name, "Fatal") || strings.HasPrefix(name, "Panic")
	}
	return false
}

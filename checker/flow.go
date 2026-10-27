package checker

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"slices"

	"fluent/bound"
	"fluent/congruence"
)

type term = congruence.Term

// flow — знание в точке программы: равенства и текущие термы переменных.
type flow struct {
	st   *congruence.State
	cur  map[*types.Var]term
	dead bool // точка недостижима (после return, panic, break, ...)

	// Слой прав (alias.go).
	ptrs    map[term]ptrInfo       // указатели, связанные с блоками
	perms   map[blockID]perm       // права кадра на блоки
	varBlk  map[*types.Var]blockID // память локальных переменных с взятым адресом
	content map[blockID]term       // текущие версии блоков (кроме памяти переменных)

	// Регионы (own.go).
	owner    map[blockID]ownerRef // владельцы дочерних блоков
	children map[slotKey]blockID  // что лежит во владеющих слотах

	deferred []deferredFact // условные ensures после вызовов (ensures.go)
}

func newFlow(st *congruence.State) *flow {
	return &flow{st: st, cur: map[*types.Var]term{}, ptrs: map[term]ptrInfo{}, perms: map[blockID]perm{},
		varBlk: map[*types.Var]blockID{}, content: map[blockID]term{},
		owner: map[blockID]ownerRef{}, children: map[slotKey]blockID{}}
}

func (f *flow) clone() *flow {
	return &flow{st: f.st.Clone(), cur: maps.Clone(f.cur), dead: f.dead,
		ptrs: maps.Clone(f.ptrs), perms: maps.Clone(f.perms), varBlk: maps.Clone(f.varBlk), content: maps.Clone(f.content),
		owner: maps.Clone(f.owner), children: maps.Clone(f.children), deferred: slices.Clone(f.deferred)}
}

// funcChecker проверяет одно тело функции.
type funcChecker struct {
	*checker
	bank  *congruence.Bank
	fl    *flow
	sig   *types.Signature
	spec  *bound.Func         // контракт проверяемой функции или nil
	entry map[*types.Var]term // значения параметров на входе (для returns)

	addrTaken  map[*types.Var]bool      // адрес взят или переменная захвачена замыканием
	captured   map[*types.Var]token.Pos // переменная захвачена замыканием: где
	gotoLabels map[string]bool
	nfresh     int
	targets    []*breakTarget // операторы, из которых выходит break (switch.go)
	label      string         // метка следующего оператора с break

	// Слой прав (alias.go).
	terms        map[ast.Expr]term      // последние вычисленные термы выражений
	suppress     map[ast.Expr]bool      // выражения, вычисляемые не как чтение памяти
	blocks       []string               // имена блоков
	blockType    map[blockID]types.Type // типы блоков
	blockVar     map[blockID]*types.Var // блок — память переменной
	entryContent map[blockID]term       // содержимое блоков-параметров на входе
	atEntry      bool                   // термы спецификации берутся на входе (returns)
	losses       []loss                 // журнал потерь прав
	writes       []blockID              // журнал записей в блоки

	// Сводка (summary.go).
	paramBlocks []blockID // блоки параметров по позициям сводки, -1 — нет
	acc         map[blockID]access
	sum         *summary
	exited      bool          // уже был выход: результаты сводки сливаются
	async       *ast.CallExpr // вызов в операторе go
	storing     string        // текст записываемого значения, для сообщений

	// ensures (ensures.go).
	deferCall *ast.CallExpr // вызов в операторе defer
	post      bool          // термы ensures после вызова
	ndeferred int
}

// checkFunc проверяет тело и возвращает выведенную сводку.
func (c *checker) checkFunc(sig *types.Signature, body *ast.BlockStmt, spec *bound.Func) *summary {
	bank := congruence.NewBank()
	fc := &funcChecker{
		checker: c,
		bank:    bank,
		fl:      newFlow(congruence.NewState(bank)),
		sig:     sig,
		spec:    spec,
		entry:   map[*types.Var]term{},

		terms:        map[ast.Expr]term{},
		suppress:     map[ast.Expr]bool{},
		blockType:    map[blockID]types.Type{},
		blockVar:     map[blockID]*types.Var{},
		entryContent: map[blockID]term{},
		acc:          map[blockID]access{},
		sum:          emptySummary(sig),
	}
	fc.prescan(body)
	params := sigParams(sig)
	fc.paramBlocks = make([]blockID, len(params))
	for i, v := range params {
		fc.paramBlocks[i] = -1
		if v.Name() == "" || v.Name() == "_" {
			continue
		}
		t := fc.fresh(v.Name())
		fc.entry[v], fc.fl.cur[v] = t, t
		// Параметр-указатель — отдельный блок с полным правом. Что из него
		// нужно на самом деле, записывается в сводку и проверяется в точке
		// вызова (§11.4).
		if isPointer(v.Type()) {
			in := fc.bank.App("*", t)
			b := fc.newBlock(v.Name(), derefType(v.Type()), in)
			fc.entryContent[b] = in
			fc.fl.ptrs[t] = ptrInfo{blocks: []blockID{b}, dependent: true}
			fc.paramBlocks[i] = b
		}
		fc.defineVar(v)
	}
	for v := range sig.Results().Variables() {
		if v.Name() != "" && v.Name() != "_" {
			fc.fl.cur[v] = fc.zero(v.Type(), body.Pos())
			fc.defineVar(v)
		}
	}
	// Внутри функции её предусловие считается верным.
	if spec != nil {
		for _, eq := range spec.Requires {
			fc.fl.st.AssertEqual(fc.specTerm(eq.Left, fc.entry, none), fc.specTerm(eq.Right, fc.entry, none))
		}
	}
	fc.stmts(body.List)
	if !fc.fl.dead {
		var vals []term
		for v := range sig.Results().Variables() {
			vals = append(vals, fc.fl.cur[v])
		}
		fc.checkEnsures(body.Rbrace, vals)
	}
	fc.exit(nil)
	return fc.finishSummary()
}

func (fc *funcChecker) fresh(hint string) term {
	fc.nfresh++
	return fc.bank.Atom(fmt.Sprintf("%s#%d", hint, fc.nfresh))
}

// defineVar — объявление переменной: у переменной с взятым адресом
// появляется новая память (на каждой итерации цикла — своя).
func (fc *funcChecker) defineVar(v *types.Var) {
	if fc.addrTaken[v] && fc.specs.Tracked(v.Type()) {
		b := fc.newBlock(v.Name(), v.Type(), none)
		fc.blockVar[b] = v
		fc.fl.varBlk[v] = b
	}
}

// errorf сообщает об ошибке, если точка достижима.
func (fc *funcChecker) errorf(pos token.Pos, format string, args ...any) {
	if fc.fl.dead || fc.fl.st.Inconsistent() || fc.silent > 0 {
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
	fc.captured = map[*types.Var]token.Pos{}
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
						if _, ok := fc.captured[v]; !ok {
							fc.captured[v] = n.Pos()
						}
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
	case *ast.SwitchStmt, *ast.TypeSwitchStmt, *ast.SelectStmt:
		fc.clauses(s)
	case *ast.LabeledStmt:
		if fc.gotoLabels[s.Label.Name] {
			// Сюда можно прийти по goto откуда угодно: забываем всё, что меняется в функции.
			fc.fl.dead = false
			fc.havoc(slicesOfMap(fc.fl.cur))
			for b := range fc.fl.perms {
				fc.fl.perms[b] = perm{why: "label " + s.Label.Name + " is reachable by goto"}
			}
			for b := range fc.fl.content {
				fc.fl.content[b] = fc.fresh(fc.blocks[b])
			}
		}
		if breakable(s.Stmt) {
			fc.label = s.Label.Name
		}
		fc.stmt(s.Stmt)
	case *ast.BranchStmt:
		if s.Tok == token.BREAK {
			fc.breakTo(s.Label)
		}
		fc.fl.dead = true
	case *ast.GoStmt:
		// Горутина работает параллельно: права не возвращаются (§12).
		fc.async = s.Call
		fc.expr(s.Call)
		fc.async = nil
	case *ast.DeferStmt:
		// Отложенный вызов выполнится на выходе: его ensures сейчас неверны.
		fc.deferCall = s.Call
		fc.expr(s.Call)
		fc.deferCall = nil
	case *ast.SendStmt:
		fc.expr(s.Chan)
		v := fc.expr(s.Value)
		fc.escape(v, fc.info.TypeOf(s.Value), fmt.Sprintf("sent to a channel at line %d", fc.line(s.Arrow)), 2)
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
		fc.storing = "value"
		if len(s.Rhs) == len(s.Lhs) {
			fc.storing = types.ExprString(s.Rhs[i])
		}
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
			fc.defineVar(v)
			fc.storeVar(v, name.Pos(), fc.fl.cur[v])
		}
	}
}

// assign записывает значение val в lhs. check — проверять ли сохранение индексов
// (false при перестройке родителя после уже сообщённой ошибки).
func (fc *funcChecker) assign(lhs ast.Expr, val term, check bool) {
	switch l := ast.Unparen(lhs).(type) {
	case *ast.Ident:
		v := fc.varOf(l)
		if v == nil || l.Name == "_" {
			return
		}
		stored := fc.storedIn(v, l.Pos())
		if !fc.isLocal(v) {
			fc.escape(val, v.Type(), stored, 2)
			return
		}
		if fc.info.Defs[l] != nil {
			fc.defineVar(v)
		} else if b, ok := fc.fl.varBlk[v]; ok && check {
			fc.checkRoot(l.Pos(), l, root{kind: rootBlocks, blocks: []blockID{b}}, true)
		}
		if fc.addrTaken[v] {
			if b, ok := fc.fl.varBlk[v]; ok {
				fc.storeValue(l.Pos(), b, nil, val, v.Type(), l.Name)
			} else {
				fc.escape(val, v.Type(), stored, 2)
			}
		}
		// Переменная, на которую может указывать указатель, — это объект.
		// Если у неё есть блок, право на запись проверено выше, и запись
		// переменной целиком атомарна: индексы могут измениться.
		_, hasBlock := fc.fl.varBlk[v]
		if old, ok := fc.fl.cur[v]; ok && fc.addrTaken[v] && check && !hasBlock {
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
		if check && !fc.checkPtr(l.Pos(), l, p, true) {
			return
		}
		if info := fc.pointsTo(p); info.exact {
			fc.storeValue(l.Pos(), info.blocks[0], info.path, val, fc.info.TypeOf(l), types.ExprString(l))
		} else {
			fc.escape(val, fc.info.TypeOf(l), fmt.Sprintf("stored through %s at line %d", types.ExprString(l.X), fc.line(l.Pos())), 2)
		}
		if info := fc.pointsTo(p); info.exact {
			// Запись объекта целиком при полном праве атомарна: индексы
			// могут измениться (§13, решение 4).
			fc.writeAt(l.Pos(), info.blocks[0], info.path, val, types.ExprString(l))
			return
		}
		if check {
			fc.preserve(l.Pos(), fc.deref(p), val, fc.info.TypeOf(l), types.ExprString(l))
		}
	case *ast.IndexExpr:
		fc.expr(l.X)
		fc.expr(l.Index)
		fc.escape(val, fc.info.TypeOf(l), fmt.Sprintf("stored in %s at line %d", types.ExprString(l), fc.line(l.Pos())), 2)
	}
}

// assignField — x.f = val.
func (fc *funcChecker) assignField(l *ast.SelectorExpr, f *types.Var, val term, check bool) {
	xt := fc.info.TypeOf(l.X)
	viaPtr := isPointer(xt)
	if !viaPtr {
		fc.noAccess(l.X)
	}
	ptr := fc.expr(l.X)
	base := ptr
	if viaPtr {
		base = fc.deref(ptr)
	}
	st := derefType(xt)
	lhs, x := types.ExprString(l), types.ExprString(l.X)
	r, dep := fc.memRoot(l), fc.dependentField(st, f)
	owning := fc.specs.Owning(f) || len(fc.ownPaths(f.Type(), 3)) > 0
	if check && (dep || owning) && !fc.checkRoot(l.Sel.Pos(), l, r, true) {
		return
	}
	if r.kind != rootValue {
		b, path, exact := fc.place(l)
		switch {
		case !exact && owning && r.kind == rootBlocks:
			// Во владеющем слоте может лежать только объект региона: место
			// записи должно быть известно точно.
			fc.errorf(l.Sel.Pos(), "cannot store %s in %s: %s may point to different objects", fc.storing, lhs, x)
		case exact && fc.specs.Owning(f):
			fc.ownStore(l.Sel.Pos(), b, path, val, fc.storing, lhs)
		case exact && owning:
			fc.storeValue(l.Sel.Pos(), b, path, val, f.Type(), lhs)
		default:
			fc.escape(val, f.Type(), fmt.Sprintf("stored in %s at line %d", lhs, fc.line(l.Pos())), 2)
		}
		if !dep {
			// Независимые поля в памяти и так читаются как свежие термы:
			// версию блока запись не меняет, права не нужны.
			return
		}
	}
	if viaPtr {
		// Запись в известный блок даёт новую версию содержимого (право на
		// запись проверено выше). Обычные поля через указатель и так
		// читаются как свежие термы.
		info := fc.pointsTo(ptr)
		nb, ok := fc.rebuild(l.Sel.Pos(), base, st, f, val, info.exact, check, lhs, x)
		if ok && info.exact {
			fc.writeAt(l.Sel.Pos(), info.blocks[0], info.path, nb, x)
		}
		return
	}
	nb, ok := fc.rebuild(l.Sel.Pos(), base, st, f, val, true, check, lhs, x)
	// Ошибочное присваивание не применяем: об ошибке уже сообщили, дальше
	// рассуждаем о прежнем объекте (иначе ошибки посыплются каскадом).
	if !ok {
		return
	}
	fc.assign(l.X, nb, check)
}

// rebuild строит новое значение структуры base типа st, в котором поле f
// равно val, и проверяет инварианты equals/close. mutable — запись
// исключительна (значение или блок с полным правом): тогда параметр,
// который упоминает только поле f, получает новое значение; остальные
// параметры обязаны сохраниться (§13, решение 4).
func (fc *funcChecker) rebuild(pos token.Pos, base term, st types.Type, f *types.Var, val term, mutable, check bool, lhs, x string) (term, bool) {
	ok := true
	changed := map[*bound.Param]term{}
	if s := fc.specs.StructOf(st); s != nil && check {
		for _, fa := range s.Fields {
			if fa.Var != f {
				continue
			}
			if p := fa.Equals; p != nil {
				if mutable && soleField(s, p) == f {
					changed[p] = val
				} else {
					ok = fc.prove(pos, val, fc.idx(base, p),
						fmt.Sprintf("assignment to %s preserves %s<%s>", lhs, x, p.Name)) && ok
				}
			}
			if fa.Close != nil {
				target := fc.specs.Bounded(f.Type())
				for i, arg := range fa.Close {
					q := target.Params[i]
					if sp, self := arg.(*bound.SelfParam); self && mutable && soleField(s, sp.Param) == f {
						changed[sp.Param] = fc.idx(val, q)
						continue
					}
					ok = fc.prove(pos, fc.idx(val, q), fc.specTerm(arg, nil, base),
						fmt.Sprintf("assignment to %s preserves %s<%s> == %s", lhs, lhs, q.Name, arg)) && ok
				}
			}
		}
	}
	if !ok {
		return none, false
	}
	nb := fc.fresh(x)
	for g := range st.Underlying().(*types.Struct).Fields() {
		if g == f {
			fc.fl.st.AssertEqual(fc.field(nb, g), val)
		} else {
			fc.fl.st.AssertEqual(fc.field(nb, g), fc.field(base, g))
		}
	}
	if s := fc.specs.Bounded(st); s != nil {
		for _, p := range s.Params {
			if t, ok := changed[p]; ok {
				fc.fl.st.AssertEqual(fc.idx(nb, p), t)
			} else {
				fc.fl.st.AssertEqual(fc.idx(nb, p), fc.idx(base, p))
			}
		}
	}
	return nb, true
}

// soleField — единственное поле структуры s, упоминающее параметр p
// в equals/close, или nil.
func soleField(s *bound.Struct, p *bound.Param) *types.Var {
	var only *types.Var
	n := 0
	for _, fa := range s.Fields {
		if fa.Equals == p {
			n, only = n+1, fa.Var
		}
		for _, a := range fa.Close {
			if sp, ok := a.(*bound.SelfParam); ok && sp.Param == p {
				n, only = n+1, fa.Var
			}
		}
	}
	if n != 1 {
		return nil
	}
	return only
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

// storeVar — начальное значение переменной: в память переменной с блоком
// оно записывается (владеющие поля переносят права), иначе утекает.
func (fc *funcChecker) storeVar(v *types.Var, pos token.Pos, val term) {
	if !fc.addrTaken[v] {
		return
	}
	if b, ok := fc.fl.varBlk[v]; ok {
		fc.storeValue(pos, b, nil, val, v.Type(), v.Name())
		return
	}
	fc.escape(val, v.Type(), fc.storedIn(v, pos), 2)
}

// storedIn — причина потери прав при записи указателя в переменную v.
func (fc *funcChecker) storedIn(v *types.Var, pos token.Pos) string {
	if at, ok := fc.captured[v]; ok {
		return fmt.Sprintf("stored in %s, which is captured by a closure at line %d", v.Name(), fc.line(at))
	}
	return fmt.Sprintf("stored in %s at line %d", v.Name(), fc.line(pos))
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
				fc.atEntry = true
				want := fc.specTerm(arg, fc.entry, none)
				fc.atEntry = false
				fc.prove(s.Pos(), fc.idx(vals[i], p), want,
					fmt.Sprintf("result %d satisfies returns: result<%s> == %s", i+1, p.Name, arg))
			}
		}
	}
	fc.checkEnsures(s.Pos(), vals)
	fc.exit(vals)
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

// facts — то, что известно из условия: равенства и пары, про которые известно,
// что они различны. Различия в состоянии хранятся, только если одна сторона —
// константа (excl: терм и константа); остальные только проверяются в момент
// assume — если пара уже выведена равной, точка недостижима.
type facts struct {
	eqs, neqs, excl [][2]term
}

func (f facts) and(g facts) facts {
	return facts{append(f.eqs, g.eqs...), append(f.neqs, g.neqs...), append(f.excl, g.excl...)}
}

func (fc *funcChecker) assume(f facts) {
	for _, e := range f.eqs {
		fc.fl.st.AssertEqual(e[0], e[1])
	}
	for _, e := range f.neqs {
		if fc.fl.st.AreEqual(e[0], e[1]) {
			fc.fl.dead = true
		}
	}
	for _, e := range f.excl {
		fc.fl.st.AssertDistinct(e[0], e[1])
	}
	fc.fire()
}

// cond вычисляет условие и возвращает факты, верные, когда оно истинно (pos)
// и когда ложно (neg).
func (fc *funcChecker) cond(e ast.Expr) (pos, neg facts) {
	switch e := ast.Unparen(e).(type) {
	case *ast.BinaryExpr:
		switch e.Op {
		case token.EQL, token.NEQ:
			f, nf := fc.eqFacts(fc.expr(e.X), fc.expr(e.Y))
			if e.Op == token.NEQ {
				return nf, f
			}
			return f, nf
		case token.LAND:
			p1, _ := fc.cond(e.X)
			// Правая часть вычисляется, только если левая истинна.
			saved, mark := fc.fl, len(fc.losses)
			fc.fl = saved.clone()
			fc.assume(p1)
			p2, _ := fc.cond(e.Y)
			fc.fl = saved
			fc.applyLosses(saved, mark)
			return p1.and(p2), facts{}
		case token.LOR:
			_, n1 := fc.cond(e.X)
			saved, mark := fc.fl, len(fc.losses)
			fc.fl = saved.clone()
			fc.assume(n1)
			_, n2 := fc.cond(e.Y)
			fc.fl = saved
			fc.applyLosses(saved, mark)
			return facts{}, n1.and(n2)
		}
	case *ast.UnaryExpr:
		if e.Op == token.NOT {
			p, n := fc.cond(e.X)
			return n, p
		}
	}
	return fc.boolFacts(e, fc.expr(e))
}

// eqFacts — факты условия x == y: когда оно истинно и когда ложно.
func (fc *funcChecker) eqFacts(x, y term) (pos, neg facts) {
	pos = facts{eqs: [][2]term{{x, y}}}
	neg = facts{neqs: pos.eqs}
	switch {
	case fc.bank.IsConst(y):
		neg.excl = [][2]term{{x, y}}
	case fc.bank.IsConst(x):
		neg.excl = [][2]term{{y, x}}
	}
	return pos, neg
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
	contents := map[blockID]term{}
	for id, ta := range a.content {
		tb, ok := b.content[id]
		switch {
		case !ok:
		case ta == tb:
			contents[id] = ta
		default:
			m := fc.fresh(fc.blocks[id])
			a.st.AssertEqual(m, ta)
			b.st.AssertEqual(m, tb)
			fc.materialize(m, fc.blockType[id], 2)
			contents[id] = m
		}
	}
	out := newFlow(congruence.Join(a.st, b.st))
	out.cur = cur
	out.content = contents
	out.deferred = joinDeferred(a.deferred, b.deferred)
	joinAlias(a, b, out)
	return out
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
	fc.pushTarget(true)
	defer fc.popTarget()
	if init != nil {
		fc.stmt(init)
	}
	fc.havoc(fc.assigned(s))
	after := fc.fl
	iteration := func() {
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
	}
	// Права, потерянные на одной итерации, недоступны на следующей и после
	// цикла; содержимое блоков, записанных в теле, неизвестно. Ни то ни
	// другое не зависит от прав, поэтому одного пробного прохода хватает,
	// чтобы найти неподвижную точку (§11.6).
	mark, wmark := len(fc.losses), len(fc.writes)
	fc.silent++
	iteration()
	fc.silent--
	fc.applyLosses(after, mark)
	fc.havocBlocks(after, wmark)
	fc.losses, fc.writes = fc.losses[:mark], fc.writes[:wmark]
	iteration()
	fc.fl = after
	fc.applyLosses(after, mark)
}

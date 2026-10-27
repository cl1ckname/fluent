package checker

import (
	"go/ast"
	"go/token"
	"go/types"
)

// switch и select (SPEC.md, §8). Ветки case проверяются как цепочка
// if-else: значения case вычисляются по порядку, ветка получает факт своего
// значения и отрицания значений предыдущих веток, default — отрицания всех.
// После switch сливаются концы веток, состояния у break и путь, где ни одна
// ветка не подошла.

// breakTarget — оператор, из которого выходит break.
type breakTarget struct {
	label string
	loop  bool    // цикл: состояние после него консервативно, break не нужен
	exits []*flow // состояния у break (switch, select)
}

func (fc *funcChecker) pushTarget(loop bool) *breakTarget {
	t := &breakTarget{label: fc.label, loop: loop}
	fc.label = ""
	fc.targets = append(fc.targets, t)
	return t
}

func (fc *funcChecker) popTarget() {
	fc.targets = fc.targets[:len(fc.targets)-1]
}

// breakTo запоминает состояние у break для оператора, из которого он выходит.
// break из вложенного цикла запоминается на обоих проходах тела (loop):
// состояние второго прохода консервативно, а слияние с первым его не усиливает.
func (fc *funcChecker) breakTo(label *ast.Ident) {
	for i := len(fc.targets) - 1; i >= 0; i-- {
		t := fc.targets[i]
		if label != nil && t.label != label.Name {
			continue
		}
		if !t.loop && !fc.fl.dead {
			t.exits = append(t.exits, fc.fl.clone())
		}
		return
	}
}

func breakable(s ast.Stmt) bool {
	switch s.(type) {
	case *ast.ForStmt, *ast.RangeStmt, *ast.SwitchStmt, *ast.TypeSwitchStmt, *ast.SelectStmt:
		return true
	}
	return false
}

func isFallthrough(s ast.Stmt) bool {
	b, ok := s.(*ast.BranchStmt)
	return ok && b.Tok == token.FALLTHROUGH
}

// clauses — switch, type switch и select.
func (fc *funcChecker) clauses(s ast.Stmt) {
	t := fc.pushTarget(false)
	defer fc.popTarget()
	var (
		body   *ast.BlockStmt
		tag    term
		hasTag bool
		valued = true // значения case дают факты (не type switch и не select)
	)
	switch s := s.(type) {
	case *ast.SwitchStmt:
		if s.Init != nil {
			fc.stmt(s.Init)
		}
		if s.Tag != nil {
			tag, hasTag = fc.expr(s.Tag), true
		}
		body = s.Body
	case *ast.TypeSwitchStmt:
		if s.Init != nil {
			fc.stmt(s.Init)
		}
		fc.stmt(s.Assign)
		body, valued = s.Body, false
	case *ast.SelectStmt:
		body, valued = s.Body, false
	}
	before := fc.fl
	_, isSelect := s.(*ast.SelectStmt)

	// Входы веток. rest — ни одна из проверенных веток не подошла.
	entries := make([]*flow, len(body.List))
	rest, def := before.clone(), -1
	for i, cl := range body.List {
		cl, ok := cl.(*ast.CaseClause)
		switch {
		case !ok:
			entries[i] = before.clone() // select: готова любая ветка
			continue
		case cl.List == nil:
			def = i
			continue
		}
		var entry *flow
		for _, e := range cl.List {
			fc.fl = rest
			var pos, neg facts
			switch {
			case !valued:
				fc.expr(e)
			case hasTag:
				pos, neg = fc.eqFacts(tag, fc.expr(e))
			default:
				pos, neg = fc.cond(e)
			}
			fc.fl = rest.clone()
			fc.assume(pos)
			entry = fc.joinInto(entry, fc.fl)
			fc.fl = rest
			fc.assume(neg)
		}
		entries[i] = entry
	}
	if def >= 0 {
		entries[def] = rest
	}

	var out, carry *flow
	for i, cl := range body.List {
		fc.fl = entries[i]
		if carry != nil {
			// fallthrough: факты значения этой ветки на пришедшем пути неверны.
			fc.fl, carry = fc.join(fc.fl, carry), nil
		}
		switch cl := cl.(type) {
		case *ast.CaseClause:
			if obj, ok := fc.info.Implicits[cl].(*types.Var); ok {
				fc.fl.cur[obj] = fc.fresh(obj.Name())
			}
			if n := len(cl.Body); n > 0 && isFallthrough(cl.Body[n-1]) {
				fc.stmts(cl.Body[:n-1])
				carry = fc.fl
				continue
			}
			fc.stmts(cl.Body)
		case *ast.CommClause:
			if cl.Comm != nil {
				fc.stmt(cl.Comm)
			}
			fc.stmts(cl.Body)
		}
		out = fc.joinInto(out, fc.fl)
	}
	if def < 0 && !isSelect {
		out = fc.joinInto(out, rest)
	}
	for _, e := range t.exits {
		out = fc.joinInto(out, e)
	}

	if out == nil {
		// select без веток не завершается.
		out = before
		out.dead = true
	}
	fc.fl = out
}

// joinInto добавляет поток b к слиянию a (nil — пустое слияние).
func (fc *funcChecker) joinInto(a, b *flow) *flow {
	if a == nil {
		return b
	}
	return fc.join(a, b)
}

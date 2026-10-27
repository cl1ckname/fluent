package checker

import (
	"go/ast"
	"go/token"
	"go/types"
	"maps"

	"fluent/bound"
)

// Постусловия ensures (SPEC.md, §6, §7). Клауза `g ==> P` проверяется на
// каждом return, где g может быть верно. В точке вызова клауза без условия
// сразу даёт факты, а условная становится отложенным фактом: P добавляется,
// когда в какой-то ветке становится известно g.

// deferredFact — отложенная клауза ensures после вызова: если result
// равен value (neq — не равен), то верны eqs. Факт верен всегда, поэтому
// после срабатывания он не удаляется: так он переживает слияние с веткой,
// где условие ещё неизвестно.
type deferredFact struct {
	id            int
	result, value term
	neq           bool
	eqs           [][2]term
}

// guardKnown — выводится ли условие result == value (!= при neq).
func (fc *funcChecker) guardKnown(result, value term, neq bool) bool {
	if neq {
		return fc.fl.st.IsDistinct(result, value)
	}
	return fc.fl.st.AreEqual(result, value)
}

// guardFalse — выводится ли отрицание условия.
func (fc *funcChecker) guardFalse(result, value term, neq bool) bool {
	return fc.guardKnown(result, value, !neq)
}

// fire добавляет правые части отложенных фактов, условия которых известны.
func (fc *funcChecker) fire() {
	for changed := true; changed; {
		changed = false
		for _, d := range fc.fl.deferred {
			if !fc.guardKnown(d.result, d.value, d.neq) {
				continue
			}
			for _, eq := range d.eqs {
				if !fc.fl.st.AreEqual(eq[0], eq[1]) {
					fc.fl.st.AssertEqual(eq[0], eq[1])
					changed = true
				}
			}
		}
	}
}

// joinDeferred — отложенные факты, которые есть на обоих путях.
func joinDeferred(a, b []deferredFact) []deferredFact {
	var out []deferredFact
	for _, d := range a {
		for _, e := range b {
			if d.id == e.id {
				out = append(out, d)
				break
			}
		}
	}
	return out
}

// checkEnsures проверяет ensures на выходе из функции; vals — возвращаемые
// значения.
func (fc *funcChecker) checkEnsures(pos token.Pos, vals []term) {
	if fc.spec == nil || len(fc.spec.Ensures) == 0 {
		return
	}
	vars := maps.Clone(fc.entry)
	for i := range fc.sig.Results().Len() {
		if i < len(vals) {
			vars[fc.sig.Results().At(i)] = vals[i]
		}
	}
	for _, e := range fc.spec.Ensures {
		if g := e.Guard; g != nil && g.Index < len(vals) && fc.guardFalse(vals[g.Index], fc.specTerm(g.Value, nil, none), g.Neq) {
			continue // на этом возврате условие ложно
		}
		for _, eq := range e.Eqs {
			fc.prove(pos, fc.specTerm(eq.Left, vars, none), fc.specTerm(eq.Right, vars, none), "ensures "+guardPrefix(e)+eq.String())
		}
	}
}

func guardPrefix(e bound.Ensure) string {
	if e.Guard == nil {
		return ""
	}
	return e.Guard.String() + " ==> "
}

// applyEnsures — факты ensures после вызова. vars — значения параметров,
// results — термы результатов.
// Память берётся в новых версиях; память, которая не известна точно, — свежими
// термами: о ней ensures ничего не говорит вызывающему.
func (fc *funcChecker) applyEnsures(spec *bound.Func, vars map[*types.Var]term, results []term) {
	vars = maps.Clone(vars)
	sig := spec.Obj.Type().(*types.Signature)
	for i := range sig.Results().Len() {
		if i < len(results) {
			vars[sig.Results().At(i)] = results[i]
		}
	}
	fc.post = true
	defer func() { fc.post = false }()
	for _, e := range spec.Ensures {
		var eqs [][2]term
		for _, eq := range e.Eqs {
			eqs = append(eqs, [2]term{fc.specTerm(eq.Left, vars, none), fc.specTerm(eq.Right, vars, none)})
		}
		g := e.Guard
		if g == nil {
			for _, eq := range eqs {
				fc.fl.st.AssertEqual(eq[0], eq[1])
			}
			continue
		}
		if g.Index >= len(results) {
			continue
		}
		fc.ndeferred++
		fc.fl.deferred = append(fc.fl.deferred, deferredFact{
			id: fc.ndeferred, result: results[g.Index], value: fc.specTerm(g.Value, nil, none), neq: g.Neq, eqs: eqs,
		})
	}
	fc.fire()
}

// specDeref — значение *x в терме спецификации. Для фактов ensures в точке
// вызова (post) память, которая не известна точно, — свежий терм.
func (fc *funcChecker) specDeref(x term) term {
	if fc.post {
		if t, ok := fc.derefBlock(x); ok {
			return t
		}
		return fc.fresh("*")
	}
	return fc.deref(x)
}

// nonNilResult — функции, которые всегда возвращают не nil.
func nonNilResult(fn *types.Func) bool {
	if fn == nil || fn.Pkg() == nil {
		return false
	}
	switch fn.Pkg().Path() + "." + fn.Name() {
	case "errors.New", "fmt.Errorf":
		return true
	}
	return false
}

// boolFacts — факты условия, которое не сравнение: e ≈ true / e ≈ false.
func (fc *funcChecker) boolFacts(e ast.Expr, t term) (pos, neg facts) {
	if b, ok := fc.info.TypeOf(e).Underlying().(*types.Basic); !ok || b.Info()&types.IsBoolean == 0 {
		return facts{}, facts{}
	}
	return facts{eqs: [][2]term{{t, fc.boolTerm(true)}}}, facts{eqs: [][2]term{{t, fc.boolTerm(false)}}}
}

package congruence

import (
	"fmt"
	"maps"
	"slices"
	"strings"
)

const none Term = -1

// State — множество известных равенств между термами, замкнутое относительно
// конгруэнтности: если a ≈ b, то f(a) ≈ f(b).
//
// Терм попадает в состояние при первом упоминании (AssertEqual, AreEqual, ...).
// Незарегистрированный терм равен только самому себе.
type State struct {
	bank         *Bank
	parent       []Term   // union-find; parent[t] == none — терм не зарегистрирован
	uses         [][]Term // для представителя: применения, у которых аргумент в этом классе
	consts       []Term   // для представителя: константа класса или none
	excl         [][]Term // для представителя: константы, которым класс не равен
	sig          map[string]Term
	inconsistent bool
}

func NewState(bank *Bank) *State {
	return &State{bank: bank, sig: map[string]Term{}}
}

// Clone возвращает независимую копию (для ветвлений).
func (s *State) Clone() *State {
	c := &State{
		bank:         s.bank,
		parent:       slices.Clone(s.parent),
		uses:         make([][]Term, len(s.uses)),
		consts:       slices.Clone(s.consts),
		excl:         make([][]Term, len(s.excl)),
		sig:          maps.Clone(s.sig),
		inconsistent: s.inconsistent,
	}
	for i, u := range s.uses {
		c.uses[i] = slices.Clone(u)
	}
	for i, x := range s.excl {
		c.excl[i] = slices.Clone(x)
	}
	return c
}

// Inconsistent сообщает, что в состоянии равны две разные константы.
// Такая точка программы недостижима.
func (s *State) Inconsistent() bool { return s.inconsistent }

// AssertEqual добавляет факт a ≈ b и все его следствия по конгруэнтности.
func (s *State) AssertEqual(a, b Term) {
	s.register(a)
	s.register(b)
	s.merge(a, b)
}

// AreEqual сообщает, выводится ли a ≈ b. В недостижимом (противоречивом)
// состоянии выводится всё.
func (s *State) AreEqual(a, b Term) bool {
	if s.inconsistent {
		return true
	}
	s.register(a)
	s.register(b)
	return s.find(a) == s.find(b)
}

// AssertDistinct добавляет факт t ≠ c, где c — константа. Других неравенств
// в состоянии нет. Если t ≈ c уже выведено, состояние противоречиво.
func (s *State) AssertDistinct(t, c Term) {
	if !s.bank.IsConst(c) {
		panic("congruence: AssertDistinct with a non-constant")
	}
	s.register(t)
	s.register(c)
	r := s.find(t)
	if r == s.find(c) {
		s.inconsistent = true
		return
	}
	if !slices.Contains(s.excl[r], c) {
		s.excl[r] = append(s.excl[r], c)
	}
}

// IsDistinct сообщает, выводится ли t ≠ c для константы c: t равен другой
// константе или t ≠ c утверждено. В противоречивом состоянии выводится всё.
func (s *State) IsDistinct(t, c Term) bool {
	if s.inconsistent {
		return true
	}
	if s.AreKnownDistinct(t, c) {
		return true
	}
	return slices.Contains(s.excl[s.find(t)], c)
}

// AreKnownDistinct сообщает, что a и b равны разным константам, то есть
// равенство a ≈ b привело бы к противоречию.
func (s *State) AreKnownDistinct(a, b Term) bool {
	ca, oka := s.ConstOf(a)
	cb, okb := s.ConstOf(b)
	return oka && okb && ca != cb
}

// ConstOf возвращает константу, которой равен t, если она известна.
func (s *State) ConstOf(t Term) (Term, bool) {
	s.register(t)
	c := s.consts[s.find(t)]
	return c, c != none
}

// Join возвращает состояние, в котором верны ровно те равенства, что верны
// и в a, и в b (над термами банка). Используется на слиянии ветвей.
// Регистрирует в a и b все термы банка.
func Join(a, b *State) *State {
	if a.bank != b.bank {
		panic("congruence: Join of states from different banks")
	}
	switch {
	case a.inconsistent:
		return b.Clone()
	case b.inconsistent:
		return a.Clone()
	}
	n := a.bank.Len()
	for t := range Term(n) {
		a.register(t)
		b.register(t)
	}
	// Термы равны в результате, если равны и в a, и в b:
	// класс результата — пара (класс в a, класс в b).
	r := NewState(a.bank)
	first := map[[2]Term]Term{}
	for t := range Term(n) {
		r.register(t)
		key := [2]Term{a.find(t), b.find(t)}
		if f, ok := first[key]; ok {
			r.merge(t, f)
		} else {
			first[key] = t
		}
	}
	// Неравенство t ≠ c остаётся, если выводится в обоих состояниях.
	for key, t := range first {
		for _, c := range slices.Concat(a.excl[key[0]], b.excl[key[1]]) {
			rt := r.find(t)
			if a.IsDistinct(t, c) && b.IsDistinct(t, c) && !slices.Contains(r.excl[rt], c) {
				r.excl[rt] = append(r.excl[rt], c)
			}
		}
	}
	return r
}

// String печатает нетривиальные классы эквивалентности (для отладки и тестов).
func (s *State) String() string {
	if s.inconsistent {
		return "⊥"
	}
	classes := map[Term][]string{}
	for t := range Term(len(s.parent)) {
		if s.parent[t] != none {
			r := s.find(t)
			classes[r] = append(classes[r], s.bank.String(t))
		}
	}
	var out []string
	for _, c := range classes {
		if len(c) > 1 {
			slices.Sort(c)
			out = append(out, "{"+strings.Join(c, ", ")+"}")
		}
	}
	slices.Sort(out)
	return strings.Join(out, " ")
}

func (s *State) find(t Term) Term {
	for s.parent[t] != t {
		s.parent[t] = s.parent[s.parent[t]]
		t = s.parent[t]
	}
	return t
}

func (s *State) register(t Term) {
	for int(t) >= len(s.parent) {
		s.parent = append(s.parent, none)
		s.uses = append(s.uses, nil)
		s.consts = append(s.consts, none)
		s.excl = append(s.excl, nil)
	}
	if s.parent[t] != none {
		return
	}
	d := s.bank.terms[t]
	for _, a := range d.args {
		s.register(a)
	}
	s.parent[t] = t
	if d.kind == kConst {
		s.consts[t] = t
	}
	if d.kind != kApp {
		return
	}
	for _, a := range d.args {
		r := s.find(a)
		s.uses[r] = append(s.uses[r], t)
	}
	key := s.signature(t)
	if other, ok := s.sig[key]; ok {
		s.merge(t, other)
	} else {
		s.sig[key] = t
	}
}

// signature — ключ применения с точностью до классов аргументов.
func (s *State) signature(t Term) string {
	d := s.bank.terms[t]
	var sb strings.Builder
	fmt.Fprintf(&sb, "%q", d.name)
	for _, a := range d.args {
		fmt.Fprintf(&sb, ",%d", s.find(a))
	}
	return sb.String()
}

func (s *State) merge(a, b Term) {
	pending := [][2]Term{{a, b}}
	for len(pending) > 0 {
		p := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		ra, rb := s.find(p[0]), s.find(p[1])
		if ra == rb {
			continue
		}
		// Меньший список применений переносим в больший.
		if len(s.uses[ra]) > len(s.uses[rb]) {
			ra, rb = rb, ra
		}
		ca, cb := s.consts[ra], s.consts[rb]
		if ca != none && cb != none {
			s.inconsistent = true
		}
		if cb == none {
			s.consts[rb] = ca
		}
		for _, c := range s.excl[ra] {
			if !slices.Contains(s.excl[rb], c) {
				s.excl[rb] = append(s.excl[rb], c)
			}
		}
		s.excl[ra] = nil
		if c := s.consts[rb]; c != none && slices.Contains(s.excl[rb], c) {
			s.inconsistent = true
		}
		s.parent[ra] = rb
		// У применений из класса ra изменилась сигнатура: перепроверяем их.
		for _, u := range s.uses[ra] {
			key := s.signature(u)
			if v, ok := s.sig[key]; ok {
				if s.find(v) != s.find(u) {
					pending = append(pending, [2]Term{u, v})
				}
			} else {
				s.sig[key] = u
			}
		}
		s.uses[rb] = append(s.uses[rb], s.uses[ra]...)
		s.uses[ra] = nil
	}
}

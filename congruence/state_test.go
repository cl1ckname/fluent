package congruence

import "testing"

func TestHashConsing(t *testing.T) {
	b := NewBank()
	x := b.Atom("x")
	if b.Atom("x") != x || b.App("f", x) != b.App("f", x) {
		t.Error("equal terms must have equal ids")
	}
	// Атом, константа и функция с одним именем — разные термы.
	if b.Atom("rub") == b.Const("rub") || b.App("f") == b.Atom("f") {
		t.Error("terms of different kinds must differ")
	}
	if got := b.String(b.App("g", x, b.Const(`"rub"`))); got != `g(x, "rub")` {
		t.Errorf("String = %s", got)
	}
}

func TestEquality(t *testing.T) {
	b := NewBank()
	x, y, z, w := b.Atom("x"), b.Atom("y"), b.Atom("z"), b.Atom("w")
	s := NewState(b)
	if !s.AreEqual(x, x) {
		t.Error("reflexivity")
	}
	if s.AreEqual(x, y) {
		t.Error("nothing is known yet")
	}
	s.AssertEqual(x, y)
	s.AssertEqual(z, y)
	if !s.AreEqual(x, z) || !s.AreEqual(z, x) {
		t.Error("transitivity/symmetry")
	}
	if s.AreEqual(x, w) {
		t.Error("w is unrelated")
	}
}

func TestCongruence(t *testing.T) {
	b := NewBank()
	a, c, d := b.Atom("a"), b.Atom("c"), b.Atom("d")
	f := func(t Term) Term { return b.App("f", t) }

	s := NewState(b)
	fa := f(a)
	s.AssertEqual(fa, fa) // f(a) зарегистрирован до слияния
	s.AssertEqual(a, c)
	if !s.AreEqual(fa, f(c)) {
		t.Error("f(c) created after a ≈ c must be congruent to f(a)")
	}
	if !s.AreEqual(f(f(a)), f(f(c))) {
		t.Error("nested congruence")
	}
	if !s.AreEqual(b.App("g", a, d), b.App("g", c, d)) {
		t.Error("n-ary congruence")
	}
	if s.AreEqual(b.App("g", a, d), b.App("g", d, c)) {
		t.Error("argument order matters")
	}
	if s.AreEqual(f(a), b.App("h", a)) {
		t.Error("different functions are not congruent")
	}
}

// f(f(f(a))) ≈ a и f(f(f(f(f(a))))) ≈ a влечёт f(a) ≈ a.
func TestCongruenceClassic(t *testing.T) {
	b := NewBank()
	a := b.Atom("a")
	fn := func(n int) Term {
		t := a
		for range n {
			t = b.App("f", t)
		}
		return t
	}
	s := NewState(b)
	s.AssertEqual(fn(3), a)
	s.AssertEqual(fn(5), a)
	if !s.AreEqual(fn(1), a) {
		t.Errorf("f(a) ≈ a must follow; state: %s", s)
	}
}

// Равенство аргументов, выведенное позже, склеивает уже существующие применения.
func TestCongruencePropagatesThroughMerges(t *testing.T) {
	b := NewBank()
	x, y, z := b.Atom("x"), b.Atom("y"), b.Atom("z")
	fx, fz := b.App("f", x), b.App("f", z)
	s := NewState(b)
	s.AssertEqual(fx, b.Const("1"))
	s.AssertEqual(fz, fz)
	s.AssertEqual(x, y)
	s.AssertEqual(y, z)
	if c, ok := s.ConstOf(fz); !ok || c != b.Const("1") {
		t.Errorf("f(z) must be 1; state: %s", s)
	}
}

func TestConstants(t *testing.T) {
	b := NewBank()
	x, y, z := b.Atom("x"), b.Atom("y"), b.Atom("z")
	rub, usd := b.Const(`"rub"`), b.Const(`"usd"`)

	s := NewState(b)
	s.AssertEqual(x, rub)
	s.AssertEqual(y, usd)
	if s.AreEqual(x, y) {
		t.Error("rub != usd")
	}
	if !s.AreKnownDistinct(x, y) {
		t.Error("x and y are known distinct")
	}
	if s.AreKnownDistinct(x, z) {
		t.Error("z is unknown")
	}
	if c, ok := s.ConstOf(x); !ok || c != rub {
		t.Error("ConstOf(x) must be rub")
	}
	if _, ok := s.ConstOf(z); ok {
		t.Error("z has no known constant")
	}
	s.AssertEqual(z, x)
	if c, _ := s.ConstOf(z); c != rub {
		t.Error("constant propagates to the merged class")
	}
	if s.Inconsistent() {
		t.Fatal("still consistent")
	}

	s.AssertEqual(x, y)
	if !s.Inconsistent() {
		t.Error(`"rub" ≈ "usd" must be a contradiction`)
	}
	if !s.AreEqual(b.Atom("p"), b.Atom("q")) {
		t.Error("everything holds in an unreachable state")
	}
}

// Противоречие, выведенное через конгруэнтность.
func TestContradictionByCongruence(t *testing.T) {
	b := NewBank()
	x, y := b.Atom("x"), b.Atom("y")
	s := NewState(b)
	s.AssertEqual(b.App("f", x), b.Const("1"))
	s.AssertEqual(b.App("f", y), b.Const("2"))
	if s.Inconsistent() {
		t.Fatal("consistent so far")
	}
	s.AssertEqual(x, y)
	if !s.Inconsistent() {
		t.Error("x ≈ y implies 1 ≈ 2")
	}
}

func TestClone(t *testing.T) {
	b := NewBank()
	x, y, z := b.Atom("x"), b.Atom("y"), b.Atom("z")
	s := NewState(b)
	s.AssertEqual(x, y)
	c := s.Clone()
	c.AssertEqual(y, z)
	c.AssertEqual(b.App("f", x), x)
	if s.AreEqual(x, z) || s.AreEqual(b.App("f", x), x) {
		t.Error("clone must not affect the original")
	}
	if !c.AreEqual(x, z) || !c.AreEqual(b.App("f", z), y) {
		t.Error("clone keeps old facts and gets new ones")
	}
}

func TestJoin(t *testing.T) {
	b := NewBank()
	x, y, z := b.Atom("x"), b.Atom("y"), b.Atom("z")
	rub, usd := b.Const(`"rub"`), b.Const(`"usd"`)

	base := NewState(b)
	base.AssertEqual(y, x)

	// if ... { x = "rub" } else { x = "usd" }; в обеих ветках z ≈ x.
	s1, s2 := base.Clone(), base.Clone()
	s1.AssertEqual(x, rub)
	s1.AssertEqual(z, x)
	s2.AssertEqual(x, usd)
	s2.AssertEqual(z, y)

	j := Join(s1, s2)
	if !j.AreEqual(x, y) || !j.AreEqual(x, z) {
		t.Errorf("facts true in both branches survive; join: %s", j)
	}
	if _, ok := j.ConstOf(x); ok {
		t.Errorf("x is rub in one branch and usd in the other; join: %s", j)
	}
	if j.AreEqual(rub, usd) || j.Inconsistent() {
		t.Error("join is consistent")
	}
}

// Равенство, которое в одной ветке задано явно, а в другой выведено
// по конгруэнтности (и терм создан только в этой ветке), переживает слияние.
func TestJoinCongruence(t *testing.T) {
	b := NewBank()
	x, y, u := b.Atom("x"), b.Atom("y"), b.Atom("u")
	s1, s2 := NewState(b), NewState(b)
	s1.AssertEqual(x, y)
	s2.AssertEqual(x, u)
	s2.AssertEqual(y, u)
	fx, fy := b.App("f", x), b.App("f", y) // созданы после ветвей
	j := Join(s1, s2)
	if !j.AreEqual(fx, fy) {
		t.Errorf("f(x) ≈ f(y) holds in both branches; join: %s", j)
	}
	if j.AreEqual(x, u) {
		t.Error("x ≈ u holds only in s2")
	}
}

func TestJoinUnreachable(t *testing.T) {
	b := NewBank()
	x, y := b.Atom("x"), b.Atom("y")
	dead, live := NewState(b), NewState(b)
	dead.AssertEqual(b.Const("1"), b.Const("2"))
	live.AssertEqual(x, y)
	for _, j := range []*State{Join(dead, live), Join(live, dead)} {
		if j.Inconsistent() || !j.AreEqual(x, y) {
			t.Errorf("unreachable branch must not weaken the other; join: %s", j)
		}
	}
}

// Канонический пример из TASK.md в терминах congruence:
// переменные — атомы с версиями, индекс — idx<c>(x).
func TestMoneyExample(t *testing.T) {
	b := NewBank()
	c := func(v string) Term { return b.App("<c>", b.Atom(v)) }
	s := NewState(b)

	s.AssertEqual(b.Atom("rub#0"), b.Const(`"rub"`))
	s.AssertEqual(b.Atom("usd#0"), b.Const(`"usd"`))
	s.AssertEqual(c("a1#0"), b.Atom("rub#0")) // a1 := newAmount(rub, 42)
	s.AssertEqual(c("a2#0"), b.Atom("rub#0")) // a2 := newAmount(rub, 12)

	// a3 := a1.sum(a2): requires a1<c> == a2<c>
	if !s.AreEqual(c("a1#0"), c("a2#0")) {
		t.Fatal("a1.sum(a2) must be accepted")
	}
	s.AssertEqual(c("a3#0"), c("a1#0")) // returns amount<a<c>>

	s.AssertEqual(c("a4#0"), b.Atom("usd#0")) // a4 := newAmount(usd, 1)

	// a5 := a4.sum(a3): requires a4<c> == a3<c>
	if s.AreEqual(c("a4#0"), c("a3#0")) {
		t.Fatal("a4.sum(a3) must be rejected")
	}
	if !s.AreKnownDistinct(c("a4#0"), c("a3#0")) {
		t.Error(`the error can name the constants: "usd" vs "rub"`)
	}

	// Символический случай: валюта из параметра, про которую ничего не известно.
	s.AssertEqual(c("p#0"), b.Atom("cur#0"))
	if s.AreEqual(c("p#0"), c("a1#0")) || s.AreKnownDistinct(c("p#0"), c("a1#0")) {
		t.Error("unknown currency: neither provable nor refuted")
	}
}

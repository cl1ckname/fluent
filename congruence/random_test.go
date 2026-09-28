package congruence

import (
	"math/rand/v2"
	"testing"
)

// naive — эталонное замыкание: матрица равенств, пересчитываемая до неподвижной точки.
type naive struct {
	b  *Bank
	eq [][]bool
}

func newNaive(b *Bank, facts [][2]Term) *naive {
	n := b.Len()
	eq := make([][]bool, n)
	for i := range eq {
		eq[i] = make([]bool, n)
		eq[i][i] = true
	}
	for _, f := range facts {
		eq[f[0]][f[1]], eq[f[1]][f[0]] = true, true
	}
	for changed := true; changed; {
		changed = false
		set := func(i, j int) {
			if !eq[i][j] {
				eq[i][j], eq[j][i] = true, true
				changed = true
			}
		}
		for i := range n {
			for j := range n {
				if !eq[i][j] {
					continue
				}
				for k := range n {
					if eq[j][k] {
						set(i, k)
					}
				}
			}
		}
		for i := range n {
			for j := range n {
				di, dj := b.terms[i], b.terms[j]
				if di.kind != kApp || dj.kind != kApp || di.name != dj.name || len(di.args) != len(dj.args) {
					continue
				}
				all := true
				for k := range di.args {
					all = all && eq[di.args[k]][dj.args[k]]
				}
				if all {
					set(i, j)
				}
			}
		}
	}
	return &naive{b: b, eq: eq}
}

func (nv *naive) inconsistent() bool {
	for i := range nv.eq {
		for j := range nv.eq {
			if i != j && nv.eq[i][j] && nv.b.terms[i].kind == kConst && nv.b.terms[j].kind == kConst {
				return true
			}
		}
	}
	return false
}

// randomBank строит небольшой банк: атомы, константы и применения f/1, g/2 глубины до 3.
func randomBank(r *rand.Rand) *Bank {
	b := NewBank()
	base := []Term{b.Atom("x"), b.Atom("y"), b.Atom("z"), b.Const("1"), b.Const("2")}
	all := append([]Term{}, base...)
	for range 12 {
		pick := func() Term { return all[r.IntN(len(all))] }
		if r.IntN(2) == 0 {
			all = append(all, b.App("f", pick()))
		} else {
			all = append(all, b.App("g", pick(), pick()))
		}
	}
	return b
}

func randomFacts(r *rand.Rand, b *Bank, k int) [][2]Term {
	facts := make([][2]Term, k)
	for i := range facts {
		facts[i] = [2]Term{Term(r.IntN(b.Len())), Term(r.IntN(b.Len()))}
	}
	return facts
}

func TestRandomAgainstNaive(t *testing.T) {
	for seed := range uint64(500) {
		r := rand.New(rand.NewPCG(seed, 1))
		b := randomBank(r)
		facts := randomFacts(r, b, 1+r.IntN(4))
		s := NewState(b)
		for _, f := range facts {
			s.AssertEqual(f[0], f[1])
		}
		nv := newNaive(b, facts)
		if s.Inconsistent() != nv.inconsistent() {
			t.Fatalf("seed %d: inconsistent = %v, naive %v", seed, s.Inconsistent(), nv.inconsistent())
		}
		if s.Inconsistent() {
			continue
		}
		for i := range Term(b.Len()) {
			for j := range Term(b.Len()) {
				if got, want := s.AreEqual(i, j), nv.eq[i][j]; got != want {
					t.Fatalf("seed %d: %s ≈ %s: got %v, want %v; state %s",
						seed, b.String(i), b.String(j), got, want, s)
				}
			}
		}
	}
}

// Join должен давать ровно пересечение замыканий веток.
func TestRandomJoinAgainstNaive(t *testing.T) {
	for seed := range uint64(500) {
		r := rand.New(rand.NewPCG(seed, 2))
		b := randomBank(r)
		f1, f2 := randomFacts(r, b, 1+r.IntN(4)), randomFacts(r, b, 1+r.IntN(4))
		s1, s2 := NewState(b), NewState(b)
		for _, f := range f1 {
			s1.AssertEqual(f[0], f[1])
		}
		for _, f := range f2 {
			s2.AssertEqual(f[0], f[1])
		}
		n1, n2 := newNaive(b, f1), newNaive(b, f2)
		j := Join(s1, s2)
		for i := range Term(b.Len()) {
			for k := range Term(b.Len()) {
				var want bool
				switch {
				case n1.inconsistent():
					want = n2.eq[i][k]
				case n2.inconsistent():
					want = n1.eq[i][k]
				default:
					want = n1.eq[i][k] && n2.eq[i][k]
				}
				if n1.inconsistent() && n2.inconsistent() {
					want = true
				}
				if got := j.AreEqual(i, k); got != want {
					t.Fatalf("seed %d: join %s ≈ %s: got %v, want %v", seed, b.String(i), b.String(k), got, want)
				}
			}
		}
	}
}

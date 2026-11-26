package sliceclient // want package:"structs \\[\\]"

import "slicelib"

func calls() {
	xs := slicelib.MixedSlice()
	slicelib.Accept(xs)
	slicelib.Accept([]slicelib.Amount{{Currency: "rub"}, {Currency: "usd"}})
	s := []slicelib.Amount{{Currency: "rub"}}
	slicelib.Accept(s) // want `slice indices are invariant`
	p := &slicelib.Amount{Currency: "rub"}
	slicelib.Pin(p)
	p.Currency = "usd" // want `cannot prove assignment .* preserves`
	q := slicelib.Pinned()
	q.Currency = "usd" // want `cannot prove assignment .* preserves`
	ps := slicelib.PointerSlice()
	a := ps[0]
	if a.Currency == "rub" {
		a.Currency = "usd" // want `cannot prove assignment .* preserves`
	}
	m := slicelib.Mixed{Items: xs}
	m.Items = []slicelib.Amount{{Currency: "rub"}} // want `slice indices are invariant`
}

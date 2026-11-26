package slicetypes // want package:"structs \\[Amount Mixed Pair Uniform\\]"

// @ bound <c string>;
type Amount struct {
	// @ equals c;
	Currency string
	Value    int
}

// @ requires a<c> == "rub";
func rub(a Amount) {}

// @ requires a<c> == "usd";
func usd(a Amount) {}

// @ requires a<c> == b<c>;
func same(a, b Amount) {}

func literals() {
	r := Amount{Currency: "rub"}
	u := Amount{Currency: "usd"}
	s := []Amount{r, r}
	rub(s[0])
	s[0] = u           // want `cannot prove slice element<c> matches slice index`
	_ = []Amount{r, u} // want `cannot prove slice element<c> matches slice index`

	// @ close <?>;
	xs := []Amount{r, u}
	a := xs[0]
	b := a
	same(a, b)
	rub(a)             // want `cannot prove a<c> == "rub"`
	same(xs[0], xs[0]) // want `cannot prove xs\[0\]<c> == xs\[0\]<c>`
	if a.Currency == "rub" {
		rub(a)
	}
	xs[0] = u
	xs = append(xs, r, u)
	xs = xs[:1]
	_ = &xs[0] // want `cannot take address of an existential slice element`
	_ = &s[0]

	s = xs // want `slice indices are invariant`
	xs = s // want `slice indices are invariant`
}

func empty() {
	// @ close <"rub">;
	var s []Amount
	s = append(s, Amount{Currency: "rub"})
	rub(s[0])
	// @ close <?>;
	var xs []Amount
	xs = append(xs, Amount{Currency: "rub"}, Amount{Currency: "usd"})
	// @ close <?>;
	buf := make([]Amount, 0, 10)
	buf = append(buf, xs...)
	copy(buf, xs)
	copy(s, xs)          // want `slice indices are invariant`
	_ = append(s, xs...) // want `slice indices are invariant`
}

func zeroElements() {
	s := make([]Amount, 2)
	if a := s[0]; a.Currency == "" {
		same(a, Amount{})
	}
	// @ close <"rub">;
	bad := make([]Amount, 2) // want `cannot prove slice element<c> matches slice index`
	_ = bad
}

type Mixed struct {
	// @ close <?>;
	Items []Amount
}

// @ bound <c string>;
type Uniform struct {
	// @ close <c>;
	Items []Amount
}

func fields() {
	m := Mixed{Items: []Amount{{Currency: "rub"}, {Currency: "usd"}}}
	a := m.Items[0]
	if a.Currency == "usd" {
		usd(a)
	}
	u := Uniform{Items: []Amount{{Currency: "rub"}}}
	rub(u.Items[0])
	u.Items = m.Items // want `slice indices are invariant`
	m.Items = u.Items // want `slice indices are invariant`
}

func acceptMixed(
	// @ close <?>;
	xs []Amount,
) {
	xs[0] = Amount{Currency: "usd"}
	a := xs[0]
	if a.Currency == "rub" {
		rub(a)
	}
}

func acceptUniform(xs []Amount) { same(xs[0], xs[1]) }

// @ returns []Amount<?>;
func mixedResult() []Amount {
	// @ close <?>;
	s := []Amount{{Currency: "rub"}, {Currency: "usd"}}
	return s
}

// @ returns []Amount<"rub">;
func uniformResult() []Amount { return []Amount{{Currency: "rub"}} }

func calls() {
	xs := mixedResult()
	s := uniformResult()
	rub(s[0])
	acceptMixed(xs)
	acceptMixed(s)    // want `slice indices are invariant`
	acceptUniform(xs) // want `slice indices are invariant`
	for _, a := range s {
		rub(a)
	}
	for _, a := range xs {
		rub(a) // want `cannot prove a<c> == "rub"`
		if a.Currency == "rub" {
			rub(a)
		}
	}
}

// @ requires a<c> == "rub";
func ptrRub(a *Amount) {}

func change(a *Amount) { a.Currency = "usd" }

func pointers(c bool) {
	p := &Amount{Currency: "rub"}
	alias := p
	s := []*Amount{p}
	ptrRub(s[0])
	p.Currency = "rub"
	p.Value = 10
	alias.Currency = "usd"       // want `cannot prove assignment .* preserves`
	*p = Amount{Currency: "usd"} // want `cannot prove assignment .* preserves`
	change(p)                    // want `index is held by a slice`
	s[0] = nil
	p.Currency = "usd" // want `cannot prove assignment .* preserves`
	q := &Amount{Currency: "rub"}
	if c {
		_ = []*Amount{q}
	}
	q.Currency = "usd" // want `cannot prove assignment .* preserves`

	// @ close <?>;
	xs := []*Amount{&Amount{Currency: "rub"}, &Amount{Currency: "usd"}}
	a := xs[0]
	if a.Currency == "rub" {
		ptrRub(a)
	}
	a.Currency = "usd" // want `cannot prove assignment .* preserves`
	xs[0] = &Amount{Currency: "usd"}
}

func pin(a *Amount) { _ = []*Amount{a} }

func pinCall() {
	a := &Amount{Currency: "rub"}
	pin(a)
	a.Currency = "usd" // want `cannot prove assignment .* preserves`
}

var escaped *Amount

func unknown(*Amount)

func pinnedEscapes() {
	a := &Amount{Currency: "rub"}
	_ = []*Amount{a}
	unknown(a) // want `cannot let pointer escape: its index is held by a slice`
	b := &Amount{Currency: "rub"}
	_ = []*Amount{b}
	escaped = b // want `cannot let pointer escape: its index is held by a slice`
}

func pinBool(a *Amount) bool { _ = []*Amount{a}; return true }

func conditionalPins(c bool) {
	a := &Amount{Currency: "rub"}
	if c && pinBool(a) {
	}
	a.Currency = "usd" // want `cannot prove assignment .* preserves`
	b := &Amount{Currency: "rub"}
	for c {
		_ = []*Amount{b}
	}
	b.Currency = "usd" // want `cannot prove assignment .* preserves`
}

type Holder struct{ Item *Amount }

func changeHolder(h *Holder) { h.Item.Currency = "usd" }

func pinnedRegion() {
	a := &Amount{Currency: "rub"}
	_ = []*Amount{a}
	h := &Holder{Item: a}
	changeHolder(h) // want `index is held by a slice`
	b := h.Item
	h.Item = nil
	b.Currency = "usd" // want `cannot prove assignment .* preserves`
}

func variadic(xs ...Amount) { same(xs[0], xs[1]) }

func mixedVariadic(
	// @ close <?>;
	xs ...Amount,
) {
	xs[0] = Amount{Currency: "usd"}
}

func variadicCalls() {
	r := Amount{Currency: "rub"}
	u := Amount{Currency: "usd"}
	variadic(r, r)
	variadic(r, u) // want `cannot prove slice element<c> matches slice index`
	mixedVariadic(r, u)
	xs := mixedResult()
	mixedVariadic(xs...)
	variadic(xs...) // want `slice indices are invariant`
}

func addressedValue() {
	a := Amount{Currency: "rub"}
	_ = []*Amount{&a}
	a.Currency = "usd"          // want `cannot prove assignment .* preserves`
	a = Amount{Currency: "usd"} // want `cannot prove assignment .* preserves`
}

func addressesAndNil() {
	// @ close <?>;
	var xs []Amount
	xs = nil
	xs = append(xs, Amount{Currency: "usd"})
	_ = len(xs)
	_ = &xs             // want `addresses of indexed slice headers are not supported`
	_ = &xs[0].Currency // want `addresses inside slice elements are not supported`
	s := []Amount{{Currency: "rub"}}
	p := &s[0]
	p.Currency = "rub"
	p.Currency = "usd" // want `cannot prove assignment .* preserves`
	clear(s)           // want `cannot prove slice element<c> matches slice index`
	clear(xs)
}

// @ bound <a, b string>;
type Pair struct {
	// @ equals a;
	A string
	// @ equals b;
	B string
}

func partialIndices() {
	// @ close <?, "fixed">;
	s := []Pair{{A: "one", B: "fixed"}, {A: "two", B: "fixed"}}
	s[0] = Pair{A: "three", B: "other"} // want `cannot prove slice element<b> matches slice index`
	a := s[0]
	if a.B != "fixed" {
		rub(Amount{Currency: "usd"})
	} // недостижимая ветка
}

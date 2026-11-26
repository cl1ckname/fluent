package slicelib // want package:"structs \\[Amount Mixed\\]"

// @ bound <c string>;
type Amount struct {
	// @ equals c;
	Currency string
}

type Mixed struct {
	// @ close <?>;
	Items []Amount
}

// @ returns []Amount<?>;
func MixedSlice() []Amount {
	return []Amount{{Currency: "rub"}, {Currency: "usd"}}
}

func Accept(
	// @ close <?>;
	xs []Amount,
) {
	xs[0] = Amount{Currency: "usd"}
}

func Pin(a *Amount) { _ = []*Amount{a} }

// @ returns []*Amount<?>;
func PointerSlice() []*Amount {
	return []*Amount{&Amount{Currency: "rub"}, &Amount{Currency: "usd"}}
}

func Pinned() *Amount {
	p := &Amount{Currency: "rub"}
	_ = []*Amount{p}
	return p
}

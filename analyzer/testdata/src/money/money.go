package money

// @ bound <c string>;
type amount struct {
	// @ equals c;
	currency string
	value    float64
}

// @ returns amount<c>;
func newAmount(c string, v float64) amount {
	return amount{currency: c, value: v}
}

/*
@ requires a<c> == b<c>;

	returns amount<a<c>>;
*/
func (a amount) sum(b amount) amount {
	return amount{currency: a.currency, value: a.value + b.value}
}

// @ bound <from, to string>;
type rate struct {
	// @ equals from;
	from string
	// @ equals to;
	to string
	k  float64
}

// @ requires a<c> == r<from>;
// @ returns amount<r<to>>;
func (r rate) convert(a amount) amount {
	return amount{currency: r.to, value: a.value * r.k}
}

// @ bound <c string>;
type wallet struct {
	// @ close <c>;
	main amount
	// @ close <c>;
	reserve amount
	name    string
}

func main() {
	rub := "rub"
	usd := "usd"
	a1 := newAmount(rub, 42)
	a2 := newAmount(rub, 12)
	a3 := a1.sum(a2)
	a4 := newAmount(usd, 1)
	a5 := a4.sum(a3) // want `cannot prove a4<c> == a3<c> \("usd" vs "rub"\)`
	_ = a5
	_ = wallet{main: a1, reserve: a3}
}

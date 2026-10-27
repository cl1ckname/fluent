package flow

type Currency string

// @ bound <c Currency>;
type amount struct {
	// @ equals c;
	currency Currency
	value    float64
}

// @ returns amount<c>;
func newAmount(c Currency, v float64) amount {
	return amount{currency: c, value: v}
}

// @ requires a<c> == b<c>;
// @ returns amount<a<c>>;
func (a amount) sum(b amount) amount {
	return amount{currency: a.currency, value: a.value + b.value}
}

// @ requires a<c> == b<c>;
func (a *amount) add(b amount) {
	a.value += b.value
}

// @ bound <c Currency>;
type wallet struct {
	// @ close <c>;
	main amount
	// @ close <c>;
	reserve amount
	name    string
}

// @ bound <from, to Currency>;
type rate struct {
	// @ equals from;
	from Currency
	// @ equals to;
	to Currency
	k  float64
}

// @ requires a<c> == r<from>;
// @ returns amount<r<to>>;
func (r rate) convert(a amount) amount {
	return amount{currency: r.to, value: a.value * r.k}
}

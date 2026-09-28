package specerrors

type Currency string

// @ bound <c Currency>;
type amount struct {
	//@ equals c;
	currency Currency
}

/*@ bound <c Currency, k float64>; */
type pair struct {
	/*@ equals c; */ // want "field value has type float64, parameter c has type Currency"
	value            float64
	/*@ equals k; */
	k float64
}

/*@ bound <c Currency>; */ // want "bound is only allowed on struct types"
type id int

type holder struct {
	/*@ close <"rub", "usd">; */ // want "amount has 1 bound parameters, got 2 arguments"
	a                            amount
	/*@ close <c>; */ // want "undefined: c"
	b                 amount
}

/*@ requires a<c> == b<d>; */ // want "type amount has no bound parameter d"
func f(a, b amount)           {}

/*@ returns amount<c>; */          // want "returns lists 1 types, function has 2 results"
func g(c Currency) (amount, error) { return amount{currency: c}, nil }

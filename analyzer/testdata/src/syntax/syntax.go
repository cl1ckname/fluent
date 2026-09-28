package syntax

/*@ bound <c>; */ // want "missing type for parameter c"
type amount struct {
	/*@ equals c */ // want "expected ';', found end of spec"
	currency string
}

/*@ ensures a == b; */ // want `unknown clause "ensures"`
func f(a, b amount)    {}

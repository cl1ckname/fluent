package syntax // want package:"structs \\[\\] contracts \\[\\]"

/*@ bound <c>; */ // want "missing type for parameter c"
type amount struct {
	/*@ equals c */ // want "expected ';', found end of spec"
	currency string
}

/*@ ensure a == b; */ // want `unknown clause "ensure"`
func f(a, b amount)   {}

/*@ ensures a != b; */ // want `'!=' is only allowed in an ensures condition`
func g(a, b amount)    {}

package crossa

// Индексы любых comparable-типов переживают экспорт.

type (
	Key    = [2]string
	AccRef = *Account
	Ints   = chan int
)

// @ bound <k any, e error, a Key, p AccRef, ch Ints>;
type Kinds struct {
	// @ equals k;
	K any
	// @ equals e;
	E error
	// @ equals a;
	A Key
	// @ equals p;
	P AccRef
	// @ equals ch;
	Ch Ints
}

// @ requires a<k> == b<k> && a<e> == b<e> && a<a> == b<a> && a<p> == b<p> && a<ch> == b<ch>;
func SameKinds(a, b Kinds) {}

package crossbad // want package:"spec errors"

// Пакет с ошибкой в спецификации: импортёр получает предупреждение.

// @ bound <c string>;
type Amount struct {
	// @ equals c;
	Currency string
}

/*@ requires a<c> == b<x>; */ // want `has no bound parameter x`
func Sum(a, b Amount)         {}

type Pair[T comparable] struct{ V T }

type IntPair = Pair[int]

// Индекс-инстанцирование generic-типа в факт не выражается: ошибка
// в пакете-источнике, импортёр предупреждается.
// @ bound <v IntPair>;
type Generic struct { // want `specification of Generic cannot be exported to other packages`
	// @ equals v;
	V IntPair
}

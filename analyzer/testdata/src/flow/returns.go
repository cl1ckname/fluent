package flow

// @ returns amount<c>;
func wrongParam(c, d Currency) amount {
	return amount{currency: d} // want `cannot prove result 1 satisfies returns: result<c> == c$`
}

// Термы returns берутся в момент входа: переприсваивание параметра не помогает.
// @ returns amount<c>;
func reassigned(c Currency) amount {
	c = "x"
	return amount{currency: c} // want `cannot prove result 1 satisfies returns`
}

// Возврат с ошибкой тоже обязан замкнуть объект.
// @ returns amount<c>, _;
func withError(c Currency, ok bool) (amount, error) {
	if !ok {
		return amount{}, nil // want `cannot prove result 1 satisfies returns`
	}
	return amount{currency: c}, nil
}

// @ returns amount<c>, _;
func withErrorOK(c Currency, ok bool) (amount, error) {
	if !ok {
		return amount{currency: c}, nil
	}
	return newAmount(c, 1), nil
}

// Именованные результаты и голый return.
// @ returns amount<a<c>>;
func named(a amount, flag bool) (res amount) {
	res = a
	if flag {
		res = a.sum(a)
	}
	return
}

// @ returns amount<a<c>>;
func namedZero(a amount) (res amount) {
	return // want `cannot prove result 1 satisfies returns`
}

// Индекс из условия.
// @ returns amount<"rub">;
func fromCond(a amount) amount {
	if a.currency == "rub" {
		return a
	}
	return newAmount("rub", a.value)
}

// @ returns wallet<a<c>>;
func makeWallet(a amount) wallet {
	return wallet{main: a, reserve: a}
}

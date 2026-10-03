package flow

// Слияние веток: переменная получает разные значения, но a и b строятся из одной и той же.
func join(flag bool) {
	var c Currency
	if flag {
		c = "rub"
	} else {
		c = "usd"
	}
	a, b := newAmount(c, 1), newAmount(c, 2)
	_ = a.sum(b)
	r := newAmount("rub", 1)
	_ = a.sum(r) // want `cannot prove a<c> == r<c>$`
}

// Факт, верный в обеих ветках, переживает слияние.
func joinKeeps(flag bool, x Currency) {
	d := x
	if flag {
		d = x
	}
	_ = newAmount(d, 1).sum(newAmount(x, 2))
}

// Ветка, которая всегда завершается, не ослабляет знание после if.
func joinDead(flag bool) {
	c := Currency("rub")
	if flag {
		c = "usd"
		return
	}
	_ = newAmount(c, 1).sum(newAmount("rub", 2))
}

// Циклы: изменённые в цикле переменные забываются, остальные — нет.
func loops(xs []Currency) {
	c := Currency("rub")
	d := Currency("rub")
	a := newAmount("rub", 1)
	for _, x := range xs {
		c = x
		_ = a.sum(newAmount(d, 1))
		_ = a.sum(newAmount(c, 1)) // want `cannot prove a<c> == newAmount\(c, 1\)<c>`
	}
	_ = a.sum(newAmount(c, 1)) // want `cannot prove a<c> == newAmount\(c, 1\)<c>`
	_ = a.sum(newAmount(d, 1))

	for i := 0; i < len(xs); i++ {
		if xs[i] == d {
			_ = a.sum(newAmount(xs[i], 1)) // want `cannot prove`
		}
	}
}

// switch: изменённые в ветках переменные забываются.
func switches(n int) {
	c := Currency("rub")
	a := newAmount("rub", 1)
	switch n {
	case 1:
		c = "usd"
	case 2:
		_ = a.sum(newAmount(c, 1))
	}
	_ = a.sum(newAmount(c, 1)) // want `cannot prove`
}

// Замыкания проверяются отдельно; захваченные переменные неизвестны.
func closures() {
	c := Currency("rub")
	f := func() {
		_ = newAmount(c, 1).sum(newAmount("rub", 1)) // want `cannot prove`
		_ = newAmount("rub", 1).sum(newAmount("rub", 1))
	}
	f()
}

// Ветка, противоречащая выведенному равенству, недостижима.
// @ requires a<c> == b<c>;
// @ returns amount<a<c>>;
func deadNeq(a, b amount) amount {
	if a.currency != b.currency {
		return newAmount("x", 0)
	}
	if a.currency == b.currency {
		return a
	}
	return newAmount("y", 0)
}

// @ requires a<c> == b<c>;
// @ returns amount<a<c>>;
func deadNeqAnd(a, b amount, ok bool) amount {
	if ok && b.currency != a.currency {
		return newAmount("x", 0)
	}
	if a.currency == "rub" && b.currency != "rub" {
		return newAmount("x", 0)
	}
	return a
}

// Без предусловия ветка достижима.
// @ returns amount<a<c>>;
func liveNeq(a, b amount) amount {
	if a.currency != b.currency {
		return b // want `cannot prove result 1 satisfies returns`
	}
	return b
}

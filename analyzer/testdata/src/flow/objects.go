package flow

// Инварианты литералов.
func literals() {
	rub := amount{currency: "rub"}
	usd := amount{currency: "usd"}
	_ = wallet{main: rub, reserve: rub}
	_ = wallet{main: rub, reserve: usd} // want `cannot prove wallet literal: reserve<c> == c \("usd" vs "rub"\)`
	_ = wallet{}
	_ = wallet{main: rub} // want `cannot prove wallet literal: reserve<c> == c \("" vs "rub"\)`
	var w wallet
	_ = w.main.sum(newAmount("", 1))
}

// Индексы полей выводятся из инвариантов close.
func fieldIndices(w wallet) {
	_ = w.main.sum(w.reserve)
	_ = makeWallet(w.main).main.sum(w.reserve)
	_ = w.main.sum(newAmount("rub", 1)) // want `cannot prove w.main<c> == newAmount\("rub", 1\)<c>`
}

// Мутации должны сохранять индексы.
func mutations() {
	rub := newAmount("rub", 1)
	usd := newAmount("usd", 1)
	w := makeWallet(rub)
	w.main = usd // want `cannot prove assignment to w.main preserves w.main<c> == c \("usd" vs "rub"\)`
	w.main = rub
	w.main.value = 42
	w.name = "x"
	_ = w.main.sum(w.reserve)
	rub.currency = "usd" // want `cannot prove assignment to rub.currency preserves rub<c> \("usd" vs "rub"\)`
	rub.currency = "rub"

	// Обычная переменная — не объект: её можно переприсвоить значением с другим индексом.
	x := rub
	x = usd
	_ = x.sum(usd)
}

// Указатели: индекс объекта за указателем стабилен.
func pointers() {
	x := newAmount("rub", 1)
	y := newAmount("rub", 2)
	z := newAmount("usd", 3)
	x.add(y)
	p := &x
	p.add(y)
	p.add(z) // want `cannot prove p<c> == z<c> \("rub" vs "usd"\)`
	*p = z   // want `cannot prove assignment to \*p preserves`
	x = z    // want `cannot prove assignment to x preserves`
	q := &amount{currency: "usd"}
	q.add(z)
	q.value = 1
	q.currency = "rub" // want `cannot prove assignment to q.currency preserves`
}

// Метод с pointer-receiver: индекс receiver-а известен из requires.
// @ requires a<c> == b<c>;
func (a *amount) addTwice(b amount) {
	a.add(b)
	a.add(a.sum(b))
	a.add(newAmount("rub", 1)) // want `cannot prove a<c> == newAmount\("rub", 1\)<c>`
}

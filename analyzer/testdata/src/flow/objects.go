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
	// Значение никто, кроме функции, не видит: индекс, который задаёт одно
	// поле, можно менять (ALIASING_DESIGN.md, §13).
	rub.currency = "usd"
	rub.currency = "rub"

	// Обычная переменная — не объект: её можно переприсвоить значением с другим индексом.
	x := rub
	x = usd
	_ = x.sum(usd)
}

// Указатели: объект за указателем — блок памяти. Запись при полном праве
// даёт новую версию и может менять индекс; она видна через все алиасы.
func pointers() {
	x := newAmount("rub", 1)
	y := newAmount("rub", 2)
	z := newAmount("usd", 3)
	p := &x
	_ = p.sum(y)
	_ = p.sum(z) // want `cannot prove p<c> == z<c> \("rub" vs "usd"\)`
	*p = z
	_ = x.sum(z)
	_ = x.sum(y) // want `cannot prove x<c> == y<c> \("usd" vs "rub"\)`
	q := &amount{currency: "usd"}
	q.value = 1
	q.currency = "rub"
	_ = q.sum(y)

	// Вызов метода с pointer-receiver по сводке возвращает права.
	x.add(z)
	x.value = 2
	x.currency = "usd"
}

// Метод с pointer-receiver: индекс receiver-а известен из requires.
// @ requires a<c> == b<c>;
func (a *amount) addTwice(b amount) {
	_ = a.sum(b)
	a.add(a.sum(b))
	a.add(newAmount("rub", 1)) // want `cannot prove a<c> == newAmount\("rub", 1\)<c>`
}

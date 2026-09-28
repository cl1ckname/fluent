package flow

// Символические индексы: равенство доказуемо, только если значения связаны.
func symbolic(x, y Currency) {
	a := newAmount(x, 1)
	b := newAmount(y, 2)
	_ = a.sum(b) // want `cannot prove a<c> == b<c>$`
	c := newAmount(x, 3)
	_ = a.sum(c)
	_ = a.sum(newAmount(x, 4)).sum(c)
}

// Равенство из условия if.
func ifEqual(x, y Currency) {
	a, b := newAmount(x, 1), newAmount(y, 2)
	if x == y {
		_ = a.sum(b)
	}
	if a.currency == b.currency {
		_ = a.sum(b)
	}
	if a.currency == b.currency && a.sum(b).value > 0 {
		_ = a.sum(b)
	}
	_ = a.sum(b) // want `cannot prove a<c> == b<c>`
}

// После if с != и ранним выходом равенство известно.
func earlyExit(a, b amount) {
	if a.currency != b.currency {
		return
	}
	_ = a.sum(b)
}

func earlyPanic(a, b amount) {
	if a.currency != b.currency || a.value < 0 {
		panic("mismatch")
	}
	_ = a.sum(b)
}

func elseBranch(a, b amount) {
	if a.currency != b.currency {
		_ = a.sum(b) // want `cannot prove a<c> == b<c>`
	} else {
		_ = a.sum(b)
	}
}

// Код в противоречивой ветке недостижим — ошибок в нём нет.
func unreachable() {
	a, b := newAmount("rub", 1), newAmount("usd", 1)
	if a.currency == b.currency {
		_ = a.sum(b)
	}
}

// Два bound-параметра.
func convert(r rate) {
	rub := newAmount("rub", 10)
	if r.from == "rub" {
		usd := r.convert(rub)
		_ = usd.sum(newAmount(r.to, 1))
		_ = usd.sum(rub) // want `cannot prove usd<c> == rub<c>`
	}
	_ = r.convert(rub) // want `cannot prove rub<c> == r<from>$`
}

// Сравнение структур целиком даёт равенство индексов.
func wholeValue(a, b amount) {
	if a == b {
		_ = a.sum(b)
	}
}

// Константы с именем и типизированные конверсии.
const RUB Currency = "rub"

func constants() {
	a := newAmount(RUB, 1)
	b := newAmount(Currency("rub"), 2)
	_ = a.sum(b)
	_ = a.sum(newAmount("usd", 1)) // want `cannot prove a<c> == newAmount\("usd", 1\)<c> \("rub" vs "usd"\)`
}

// Функции без контракта возвращают значения с неизвестным индексом.
func unknownAmount() amount { return newAmount("rub", 1) }

func noContract() {
	a := newAmount("rub", 1)
	_ = a.sum(unknownAmount()) // want `cannot prove a<c> == unknownAmount\(\)<c>`
}

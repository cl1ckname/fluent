package crossb // want package:"structs \\[Pair\\]"

import (
	"crossa"
	"crossbad" // want `package crossbad has errors in fluent specifications; some of its contracts are ignored`
	"crossmid"
	"crossplain"
)

var _ = crossbad.Sum

// Поля с close на bounded-типе другого пакета.
// @ bound <c string>;
type Pair struct {
	// @ close <c>;
	A crossa.Amount
	// @ close <c>;
	B crossa.Amount
}

func contracts() {
	r := crossa.New("rub", 1)
	u := crossa.New("usd", 1)
	_ = crossa.Sum(r, crossa.New(crossa.RUB, 2))
	_ = crossa.Sum(r, u) // want `cannot prove r<c> == u<c>`
	_ = crossa.Sum(u, crossa.USD(1))
	_ = Pair{A: r, B: r}
	_ = Pair{A: r, B: u} // want `cannot prove`
}

// @ returns crossa.Amount<c>;
func wrap(c string, v float64) crossa.Amount { return crossa.New(c, v) }

// @ returns crossa.Amount<c>;
func wrapWrong(c string, v float64) crossa.Amount { return crossa.New("rub", v) } // want `cannot prove`

func ensures() {
	a, err := crossa.Parse("rub", "1")
	_ = crossa.Sum(a, crossa.New("rub", 1)) // want `cannot prove`
	if err != nil {
		return
	}
	_ = crossa.Sum(a, crossa.New("rub", 1))
}

// Запись зависимого поля чужого типа: при исключительном доступе меняет индекс.
func fieldWrite() {
	a := crossa.New("rub", 1)
	a.Currency = "usd"
	_ = crossa.Sum(a, crossa.New("usd", 1))
	_ = crossa.Sum(a, crossa.New("rub", 1)) // want `cannot prove`
}

func typestate() {
	a := &crossa.Account{Status: crossa.StatusActive}
	crossa.Deactivate(a)
	crossa.Deactivate(a) // want `cannot prove a<s> == crossa.StatusActive|cannot prove a<s> == StatusActive`
}

// Сводки другого пакета: чтение и запись независимого поля права не забирают.
func summaries() {
	a := &crossa.Account{Status: crossa.StatusActive}
	_ = crossa.Touch(a)
	crossa.Rename(a, "x")
	_ = crossmid.Peek(a)
	crossa.Deactivate(a)
}

func kept() {
	a := &crossa.Account{Status: crossa.StatusActive}
	crossa.Keep(a)
	_ = crossa.Touch(a) // want `cannot pass a to crossa.Touch: no access: kept by crossa.Keep at line \d+ \(crossa.go: .*\)`
}

// Сводка пакета без спецификаций, транзитивно.
func keptTransitive() {
	a := crossa.NewAccount()
	crossmid.Forward(a)
	_ = a.Status // want `no access: kept by crossmid.Forward at line \d+ \(crossmid.go: kept by crossa.Keep`
}

// Пакет без факта: вызов неизвестен.
func unknown() {
	a := crossa.NewAccount()
	crossplain.Use(a)
	_ = a.Status // want `no access: passed to crossplain.Use`
}

// Перенос во владеющее поле и результат-алиас через границу пакета.
func owning() {
	o := &crossa.Order{}
	a := crossa.NewAccount()
	crossa.Attach(o, a)
	_ = a.Status
	b := o.Account()
	b.Status = crossa.StatusInactive
	o2 := &crossa.Order{}
	crossa.Attach(o2, a) // want `cannot store a in .*: a already belongs to`
}

// Инициализаторы пакетных переменных проверяются, как тела функций.
var (
	okInit  = crossa.Sum(crossa.New("rub", 1), crossa.New("rub", 2))
	badInit = crossa.Sum(crossa.New("usd", 1), crossa.New("rub", 1)) // want `cannot prove`
	closure = func() {
		crossa.Sum(crossa.New("usd", 1), crossa.New("rub", 1)) // want `cannot prove`
	}
	badLit = Pair{A: crossa.New("rub", 1), B: crossa.New("usd", 1)} // want `cannot prove`
)

func unproven() {
	_ = crossa.Sum(crossa.Wrong("a"), crossa.New("a", 1)) // want `contract of crossa.Wrong is not proven in its package: wrong.go:6: cannot prove result 1 satisfies returns`
}

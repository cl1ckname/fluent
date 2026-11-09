package alias

// @ requires a<s> == StatusActive;
func Charge(a *Account) {}

func CloseOrder(o *Order) {
	o.Acc.Status = StatusInactive
}

// Пример из §11.10: после переноса acc — путь в регион o.
func closeOrder() {
	acc := &Account{Status: StatusActive}
	o := &Order{Acc: acc}
	acc.Status = StatusActive
	Charge(acc)
	CloseOrder(o)
	_ = acc.Status // want `cannot read acc.Status: no access: \(&Order at line \d+\).Acc may have been replaced`
	Charge(o.Acc)  // want `cannot prove o.Acc<s> == StatusActive`
	o.Acc.Status = StatusActive
	Charge(o.Acc)
}

// Один объект — один владелец.
func secondOwner() {
	acc := &Account{Status: StatusActive}
	o1 := &Order{Acc: acc}
	_ = &Order{Acc: acc} // want `cannot store acc in \(&Order at line \d+\).Acc: acc already belongs to \(&Order at line \d+\).Acc`
	o2 := &Order{Acc: &Account{Status: StatusActive}}
	o1.Acc = o2.Acc // want `cannot store o2.Acc in o1.Acc: o2.Acc already belongs to`
}

// Запись в слот заменяет прежний объект: он теряет права.
func replace() {
	a1 := &Account{Status: StatusActive}
	a2 := &Account{Status: StatusActive}
	o := &Order{Acc: a1}
	o.Acc = a2
	_ = a1.Status // want `no access: replaced in o.Acc at line \d+`
	a2.Status = StatusInactive
	requireInactive(o.Acc)
	o.Acc = nil
	_ = a2.Status // want `no access: replaced in o.Acc`
}

type Node struct {
	Acc  Account
	Next *Node
}

// Объект не может владеть собой.
func cycle() {
	n := &Node{}
	n.Next = n // want `cannot store n in n.Next: an object cannot own itself`
}

// Копия структуры указывает в тот же регион.
func valueCopy() {
	o := &Order{Acc: &Account{Status: StatusActive}}
	x := *o
	x.Acc.Status = StatusInactive
	requireInactive(o.Acc)
}

func attach(o *Order, a *Account) { o.Acc = a }

func NewOrder(a *Account) *Order { return &Order{Acc: a} }

func (o *Order) Account() *Account { return o.Acc }

func peek(o *Order) Status { return o.Acc.Status }

// Перенос внутри вызываемой функции: сводка знает, в какой слот.
func ownershipCalls() {
	acc := &Account{Status: StatusActive}
	o := &Order{}
	attach(o, acc)
	acc.Status = StatusInactive
	requireInactive(o.Acc)

	b := &Account{Status: StatusActive}
	o2 := NewOrder(b)
	requireActive(o2.Acc)
	requireActive(b)

	a := o2.Account()
	a.Status = StatusInactive
	requireInactive(b)
	_ = peek(o2)
	requireInactive(o2.Acc)
}

// Требования к разным частям одного региона складываются по корню.
func regionDemands() {
	o := &Order{Acc: &Account{Status: StatusActive}}
	o2 := &Order{Acc: &Account{Status: StatusActive}}
	moveStatus(o.Acc, o2.Acc)
	moveStatus(o.Acc, o.Acc) // want `cannot pass o.Acc and o.Acc to moveStatus: the same object is passed more than once`
}

// Удержание части региона забирает права на весь регион.
func keepPart() {
	o := &Order{Acc: &Account{Status: StatusActive}}
	use(o.Acc)
	_ = o.Title
	_ = o.Acc.Status // want `no access: kept by use`
}

// Во владеющий слот нельзя писать через неточный указатель.
func inexactSlot(c bool) {
	o1 := &Order{}
	o2 := &Order{}
	r := o1
	if c {
		r = o2
	}
	r.Acc = &Account{Status: StatusActive} // want `cannot write r.Acc: r does not point to a known object`
	if r == o1 {
		r.Acc = &Account{Status: StatusActive} // здесь r — точно o1
	}
}

var globalOrder *Order

// Регион нельзя получить из неизвестной памяти.
func unknownRegion() {
	CloseOrder(globalOrder) // want `cannot pass globalOrder to CloseOrder: globalOrder does not point to a known object`
}

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

// Запись в слот возвращает прежнему объекту самостоятельное полное право.
func replace() {
	a1 := &Account{Status: StatusActive}
	a2 := &Account{Status: StatusActive}
	o := &Order{Acc: a1}
	o.Acc = a2
	requireActive(a1)
	a1.Status = StatusInactive
	requireActive(o.Acc)
	a2.Status = StatusInactive
	requireInactive(o.Acc)
	o.Acc = nil
	requireInactive(a2)
	a2.Status = StatusActive
	requireActive(a2)
}

// Символический дочерний блок также можно извлечь; все его алиасы сохраняются.
func extract(o *Order) {
	p := o.Acc
	alias := p
	p.Status = StatusActive
	o.Acc = nil
	requireActive(alias)
	p.Status = StatusInactive
	requireInactive(alias)
	use(o.Acc)
	requireInactive(p)
}

// Самоприсваивание и запись известного алиаса сохраняют регион.
func selfStore(o *Order) {
	p := o.Acc
	p.Status = StatusActive
	o.Acc = o.Acc
	requireActive(p)
	o.Acc = p
	requireActive(o.Acc)
	p.Status = StatusInactive
	requireInactive(o.Acc)
}

// При извлечении сохраняется весь подрегион, а права корней независимы.
func extractSubregion() {
	acc := &Account{Status: StatusActive}
	child := &Node{Acc: *acc, Next: &Node{}}
	grandchild := child.Next
	root := &Node{Next: child}
	p := root.Next
	root.Next = nil
	useNode(root)
	requireActive(&p.Acc)
	grandchild.Acc.Status = StatusInactive
	requireInactive(&child.Next.Acc)
	useNode(p)
	_ = grandchild.Acc.Status // want `no access: .* may have been replaced`
}

var globalNode *Node

func useNode(n *Node) { globalNode = n }

// Ошибочная вставка не освобождает прежний объект.
func failedReplacement() {
	o1 := &Order{Acc: &Account{Status: StatusActive}}
	o2 := &Order{Acc: &Account{Status: StatusActive}}
	p := o1.Acc
	o1.Acc = o2.Acc // want `cannot store o2.Acc in o1.Acc: o2.Acc already belongs to`
	use(o1.Acc)
	_ = p.Status // want `no access: .* may have been replaced`
}

// Извлечение лишь на одной ветке не выдаёт самостоятельного права после слияния.
func conditionalExtract(c bool) {
	o := &Order{Acc: &Account{Status: StatusActive}}
	p := o.Acc
	if c {
		o.Acc = nil
	}
	_ = p.Status // want `no access`
}

// После извлечения объект можно перенести к другому владельцу.
func reattach() {
	o1 := &Order{Acc: &Account{Status: StatusActive}}
	p := o1.Acc
	o1.Acc = nil
	o2 := &Order{Acc: p}
	p.Status = StatusInactive
	requireInactive(o2.Acc)
	use(o2.Acc)
	_ = p.Status // want `no access: .* may have been replaced`
}

// Потерянное право на регион нельзя восстановить очисткой поля.
func extractWithoutAccess() {
	o := &Order{Acc: &Account{Status: StatusActive}}
	p := o.Acc
	use(p)
	o.Acc = nil  // want `cannot write o.Acc: no access`
	_ = p.Status // want `no access`
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

package alias

// Термы спецификации через владеющее поле: o.Acc — дочерний блок региона o.

// @ requires o.Acc<s> == StatusActive;
// @ ensures o.Acc<s> == StatusInactive;
func closeChild(o *Order) { o.Acc.Status = StatusInactive }

// @ ensures o.Acc<s> == StatusInactive;
func badCloseChild(o *Order) {
	o.Acc.Status = StatusActive
} // want `cannot prove ensures o.Acc<s> == StatusInactive`

func childCaller() {
	o := &Order{Acc: &Account{Status: StatusActive}}
	closeChild(o)
	requireInactive(o.Acc)
	closeChild(o) // want `cannot prove o.Acc<s> == StatusActive`
}

// ensures описывает новый дочерний блок: старый указатель прав не имеет
// (§11.10, отсоединение при новой версии).
func childStale() {
	acc := &Account{Status: StatusActive}
	o := &Order{Acc: acc}
	closeChild(o)
	requireInactive(o.Acc)
	_ = acc.Status // want `cannot read acc.Status: no access: \(&Order at line \d+\).Acc may have been replaced`
}

// Слот, о котором ничего не известно: requires не доказать.
func childUnknown(o *Order) {
	closeChild(o) // want `cannot prove o.Acc<s> == StatusActive`
	o.Acc.Status = StatusActive
	closeChild(o)
	requireInactive(o.Acc)
}

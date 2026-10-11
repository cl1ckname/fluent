package alias

// Этап 2б: версии содержимого блоков. Запись при полном праве даёт новую
// версию; индексный параметр, который упоминает только записываемое поле,
// меняется, остальные обязаны сохраниться (§13, решение 4).

// @ bound <c string>;
type Amount struct {
	// @ equals c;
	Currency string
	Value    int
}

// @ bound <c string>;
type Wallet struct {
	// @ close <c>;
	Main Amount
	// @ close <c>;
	Reserve Amount
}

// @ requires a<s> == StatusActive;
func requireActive(a *Account) {}

// @ requires a<s> == StatusInactive;
func requireInactive(a *Account) {}

// @ requires a<s> == StatusInactive;
func requireInactiveV(a Account) {}

// @ requires w<c> == "usd";
func requireUSD(w *Wallet) {}

// Typestate: запись меняет индекс, требования проверяются по новой версии.
// @ requires u<s> == StatusActive;
func (u *Account) Inactivate() {
	u.Status = StatusInactive
}

func typestate() {
	p := &Account{Status: StatusActive}
	q := p
	p.Status = StatusInactive
	requireInactive(q)
}

func staleFact() {
	p := &Account{Status: StatusActive}
	p.Status = StatusInactive
	requireActive(p) // want `cannot prove p<s> == StatusActive \("inactive" vs "active"\)`
}

// Параметр c упоминают оба поля: пофилдовая смена запрещена, целиком — можно.
func atomic() {
	w := &Wallet{Main: Amount{Currency: "rub"}, Reserve: Amount{Currency: "rub"}}
	w.Main = Amount{Currency: "usd"} // want `cannot prove assignment to w.Main preserves w.Main<c> == c \("usd" vs "rub"\)`
	w.Main.Currency = "usd"          // want `cannot prove assignment to w.Main preserves w.Main<c> == c \("usd" vs "rub"\)`
	w.Main.Value = 1
	*w = Wallet{Main: Amount{Currency: "usd"}, Reserve: Amount{Currency: "usd"}}
	requireUSD(w)
}

// Значение — исключительное владение: индекс меняется так же.
func valueState() {
	a := Account{Status: StatusActive}
	a.Status = StatusInactive
	requireInactiveV(a)
}

// Переменная с взятым адресом: запись через указатель видна через имя.
func varBlock() {
	a := Account{Status: StatusActive}
	pa := &a
	pa.Status = StatusInactive
	requireInactiveV(a)
}

// Указатель на зависимое поле пишет в тот же блок.
func fieldPointer() {
	p := &Account{Status: StatusActive}
	s := &p.Status
	*s = StatusInactive
	requireInactive(p)
}

// Запись на одной ветке: после слияния статус неизвестен.
func branchWrite(c bool) {
	p := &Account{Status: StatusActive}
	if c {
		p.Status = StatusInactive
	}
	requireActive(p) // want `cannot prove p<s> == StatusActive`
}

// Запись в цикле: после цикла и на следующей итерации статус неизвестен.
func loopWrite(n int) {
	p := &Account{Status: StatusActive}
	for i := 0; i < n; i++ {
		_ = p.Status
	}
	requireActive(p)
	q := &Account{Status: StatusActive}
	for i := 0; i < n; i++ {
		q.Status = StatusInactive
	}
	requireActive(q) // want `cannot prove q<s> == StatusActive`
}

// returns говорит о значениях на входе.
// @ returns Amount<a<c>>;
func snapshot(a *Amount) Amount {
	old := *a
	a.Currency = "eur"
	return old
}

// Чужая память без прав менять нельзя.
func noRight() {
	p := &Account{Status: StatusActive}
	use(p)
	p.Status = StatusInactive // want `cannot write p.Status: no access: kept by use`
}

// @ returns Amount<a<c>>;
func snapshotWrong(a *Amount) Amount {
	a.Currency = "eur"
	return *a // want `cannot prove result 1 satisfies returns: result<c> == a<c>`
}

// После потери прав содержимое неизвестно: старые факты не используются.
func staleAfterLoss() {
	p := &Account{Status: StatusActive}
	use(p)
	requireActive(p) // want `cannot prove p<s> == StatusActive`
}

package alias

// Этап 3: сводки функций пакета и правило вызова (§11.4, §11.8).

func readStatus(a *Account) Status { return a.Status }

func setInactive(a *Account) { a.Status = StatusInactive }

// Вызов, который только читает, оставляет права и факты.
func readCall() {
	p := &Account{Status: StatusActive}
	_ = readStatus(p)
	requireActive(p)
	p.Status = StatusInactive
}

// Вызов, который пишет: права возвращаются, содержимое — новая версия.
func writeCall() {
	p := &Account{Status: StatusActive}
	setInactive(p)
	requireActive(p) // want `cannot prove p<s> == StatusActive`
	p.Status = StatusActive
	requireActive(p)
}

// Без ensures вызывающий не знает новое состояние.
func typestateCall() {
	p := &Account{Status: StatusActive}
	p.Inactivate()
	requireInactive(p) // want `cannot prove p<s> == StatusInactive`
}

func moveStatus(dst, src *Account) { dst.Status = src.Status }

func compare(a, b *Account) bool { return a.Status == b.Status }

// Одна память не передаётся дважды, если вызываемая функция в неё пишет.
func sameObject() {
	p := &Account{Status: StatusActive}
	q := &Account{Status: StatusActive}
	moveStatus(p, q)
	moveStatus(p, p) // want `cannot pass p and p to moveStatus: the same object is passed more than once and moveStatus may write to it`
	r := p
	moveStatus(r, p) // want `cannot pass r and p to moveStatus`
	_ = compare(p, p)
}

func setStatus(s *Status) { *s = StatusInactive }

func setString(s *string) { *s = "x" }

// Указатель на поле: требование относится к памяти объекта.
func fieldArg() {
	p := &Account{Status: StatusActive}
	setStatus(&p.Status)
	requireActive(p) // want `cannot prove p<s> == StatusActive`
	var title string
	setString(&title)
	setString(&p.Title)
	use(p)
	setStatus(&p.Status) // want `cannot pass &p.Status to setStatus: no access: kept by use`
}

func newAccount() *Account { return &Account{Status: StatusActive} }

func fromGlobal() *Account { return globalPtr }

// Свежий объект из конструктора — полное право у вызывающего.
func freshResult() {
	p := newAccount()
	p.Status = StatusInactive
	q := fromGlobal()
	_ = q.Status // want `cannot read q.Status: q does not point to a known object`
}

func (a *Account) Self() *Account { return a }

// Результат-алиас параметра указывает в ту же память.
func aliasResult() {
	p := &Account{Status: StatusActive}
	q := p.Self()
	q.Status = StatusInactive
	requireInactive(p)
}

func deactivateAll(a *Account, n int) {
	if n == 0 {
		return
	}
	a.Status = StatusInactive
	deactivateAll(a, n-1)
}

func keepRec(a *Account, n int) {
	if n == 0 {
		globalPtr = a
		return
	}
	keepRec(a, n-1)
}

func isEven(a *Account, n int) bool {
	if n == 0 {
		return a.Status == StatusActive
	}
	return isOdd(a, n-1)
}

func isOdd(a *Account, n int) bool {
	if n == 0 {
		return false
	}
	return isEven(a, n-1)
}

// Рекурсия: сводка — неподвижная точка.
func recursion() {
	p := &Account{Status: StatusActive}
	deactivateAll(p, 3)
	p.Status = StatusActive
	_ = isEven(p, 4)
	requireActive(p)
	keepRec(p, 1)
	_ = p.Status // want `cannot read p.Status: no access: kept by keepRec`
}

func many(as ...*Account) {}

// Вариативные аргументы попадают в срез.
func variadic() {
	p := &Account{Status: StatusActive}
	many(p)
	_ = p.Status // want `no access: passed to many`
}

func (a *Account) Get() Status { return a.Status }

// Неявный &x у метода, который только читает.
func implicitRead() {
	a := Account{Status: StatusActive}
	_ = a.Get()
	a.Status = StatusInactive
	requireInactiveV(a)
}

// Горутина работает параллельно: права не возвращаются, даже если функция
// только читает.
func goroutine() {
	p := &Account{Status: StatusActive}
	go readStatus(p)
	_ = p.Status // want `no access: passed to readStatus`
}

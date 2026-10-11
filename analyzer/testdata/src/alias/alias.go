package alias

// Слой прав (ALIASING_DESIGN.md, §11): блоки, права кадра, потери прав.
// Вспомогательные функции use, useStatus, check и Touch удерживают указатель
// (кладут его в глобальную переменную), поэтому забирают права.

type Status string

const (
	StatusActive   Status = "active"
	StatusInactive Status = "inactive"
)

// @ bound <s Status>;
type Account struct {
	// @ equals s;
	Status Status
	Title  string
}

type Order struct {
	Acc   *Account
	Title string
}

func use(a *Account)        { globalPtr = a }
func useStatus(s *Status)   { globalStatus = s }
func useTitle(s *string)    { globalTitle = s }
func useAny(v any)          {}
func check(a *Account) bool { globalPtr = a; return true }

func (a *Account) Touch() { globalPtr = a }

var global Account
var globalPtr *Account
var globalStatus *Status
var globalTitle *string

// Свежий объект: полное право у кадра.
func fresh() {
	p := &Account{Status: StatusActive}
	_ = p.Status
	p.Status = StatusActive
	q := new(Account)
	_ = q.Status
}

// Алиасы внутри функции пользуются одним правом кадра (§6).
func aliases() {
	p := &Account{Status: StatusActive}
	q := p
	_ = q.Status
	p.Status = StatusActive
	_ = q.Status
}

// Параметр-указатель: блок с полным правом.
func param(p *Account) {
	_ = p.Status
	p.Status = p.Status
}

// Вызов забирает права (этап 2а: сводок нет).
func lostToCall() {
	p := &Account{Status: StatusActive}
	use(p)
	_ = p.Status            // want `cannot read p.Status: no access: kept by use at line \d+`
	p.Status = StatusActive // want `cannot write p.Status: no access: kept by use`
	_ = p.Title             // независимое поле: права не нужны
	p.Title = "x"
}

// Права относятся к памяти, а не к имени.
func lostThroughAlias() {
	p := &Account{Status: StatusActive}
	q := p
	use(q)
	_ = p.Status // want `cannot read p.Status: no access: kept by use`
}

// Метод с pointer-receiver на переменной: неявный &x.
func implicitAddr() {
	a := Account{Status: StatusActive}
	_ = a.Status
	a.Touch()
	_ = a.Status // want `cannot read a.Status: no access: kept by Touch`
	b := a       // want `cannot read a: no access: kept by Touch`
	_ = b.Status // b — копия, значение
}

// Адрес переменной: доступ через указатель и через имя — одна память.
func addrOfVar() {
	a := Account{Status: StatusActive}
	pa := &a
	_ = pa.Status
	_ = a.Status
	use(pa)
	_ = a.Status // want `cannot read a.Status: no access: kept by use`
}

// Адрес зависимого поля ведёт в тот же блок; адрес независимого — нет.
func fieldAddr() {
	p := &Account{Status: StatusActive}
	t := &p.Title
	useTitle(t)
	_ = p.Status
	s := &p.Status
	useStatus(s)
	_ = p.Status      // want `cannot read p.Status: no access: kept by useStatus`
	*s = StatusActive // want `cannot write \*s: no access: kept by useStatus`
}

// Права, потерянные на одной ветке, после слияния недоступны.
func branches(c bool) {
	p := &Account{Status: StatusActive}
	if c {
		use(p)
	}
	_ = p.Status // want `cannot read p.Status: no access: kept by use`
}

// Условный алиас: после слияния q не указывает на известный объект (§8).
func conditionalAlias(c bool) {
	p := &Account{Status: StatusActive}
	var q *Account
	if c {
		q = p
	} else {
		q = &Account{Status: StatusActive}
	}
	_ = p.Status
	_ = q.Status // want `cannot read q.Status: q does not point to a known object`
}

// Потеря на второй итерации цикла и после него (§11.6).
func loops(n int) {
	p := &Account{Status: StatusActive}
	for i := 0; i < n; i++ {
		_ = p.Status // want `cannot read p.Status: no access: kept by use`
		use(p)       // want `cannot pass p to use: no access: kept by use at line \d+ \(stored in globalPtr at line \d+\)`
	}
	_ = p.Status // want `cannot read p.Status: no access: kept by use`
}

// Переменная, объявленная в цикле, — новая память на каждой итерации.
func loopLocal(n int) {
	for i := 0; i < n; i++ {
		a := Account{Status: StatusActive}
		_ = a.Status
		use(&a)
	}
}

// switch: потеря в любой ветке видна после него.
func switches(k int) {
	p := &Account{Status: StatusActive}
	switch k {
	case 1:
		use(p)
	}
	_ = p.Status // want `cannot read p.Status: no access: kept by use`
}

// Правая часть && вычисляется на копии состояния, но потери переносятся.
func conditions(c bool) {
	p := &Account{Status: StatusActive}
	if c && check(p) {
	}
	_ = p.Status // want `cannot read p.Status: no access: kept by check`
}

// Утечки в места, которые анализ не видит.
func escapes(ch chan *Account) {
	p1 := &Account{Status: StatusActive}
	_ = []*Account{p1}
	_ = p1.Status // want `no access: stored in a composite literal`

	p2 := &Account{Status: StatusActive}
	globalPtr = p2
	_ = p2.Status // want `no access: stored in globalPtr`

	p3 := &Account{Status: StatusActive}
	ch <- p3
	_ = p3.Status // want `no access: sent to a channel`

	p4 := &Account{Status: StatusActive}
	f := func() { _ = p4 }
	_ = p4.Status // want `no access: stored in p4, which is captured by a closure at line \d+`
	f()

	// Запись во владеющее поле — не утечка, а перенос в регион (§11.10).
	p5 := &Account{Status: StatusActive}
	_ = &Order{Acc: p5}
	_ = p5.Status

	p6 := &Account{Status: StatusActive}
	useAny(p6)
	_ = p6.Status // want `no access: passed to useAny`

	p7 := &Account{Status: StatusActive}
	defer use(p7)
	_ = p7.Status // want `no access: kept by use`

	p8 := &Account{Status: StatusActive}
	m := p8.Touch
	_ = p8.Status // want `no access: bound to method value p8.Touch`
	m()
}

// Указатель из владеющего поля ведёт в дочерний блок региона o (§11.10).
func fromField(o *Order) {
	_ = o.Acc.Title
	o.Acc.Title = "x"
	_ = o.Acc.Status
}

// Память без отслеживания.
func untracked(xs []Account, m map[string]Account) {
	_ = global.Status // want `cannot read global.Status: global is a global variable`
	_ = xs[0].Status  // want `cannot read xs\[0\].Status: elements of slices`
	_ = m["a"].Status // want `cannot read m\["a"\].Status: elements of slices`
	for _, a := range xs {
		_ = a.Status // копия элемента — значение
	}
}

// Значения не нуждаются в правах.
func values(a Account) Account {
	_ = a.Status
	return Account{Status: a.Status}
}

// Чтение и запись *p целиком.
func deref() {
	p := &Account{Status: StatusActive}
	v := *p
	*p = v
	use(p)
	_ = *p // want `cannot read \*p: no access: kept by use`
}

// Метку можно достичь по goto откуда угодно: права консервативно теряются.
func gotos(c bool) {
	p := &Account{Status: StatusActive}
	if c {
		goto end
	}
end:
	_ = p.Status // want `p does not point to a known object`
}

type Wrapped struct {
	Account
}

type WrappedPtr struct {
	*Account
}

// Поле встроенной структуры лежит в памяти внешней; через встроенный
// указатель — в неизвестной.
func promoted(w Wrapped, wp WrappedPtr) {
	_ = w.Status
	pw := &Wrapped{}
	_ = pw.Status
	use(&pw.Account)
	_ = pw.Status // want `cannot read pw.Status: no access: kept by use`
	_ = wp.Status // want `cannot read wp.Status: fields promoted through embedded pointers are not supported`
}

// Независимое поле переменной с взятым адресом пишется без прав.
func independentWrite() {
	a := Account{Status: StatusActive}
	use(&a)
	a.Title = "x"
	a.Status = StatusActive // want `cannot write a.Status: no access: kept by use`
}

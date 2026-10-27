package alias

// switch и select: значения case — факты в ветках, после switch ветки
// сливаются.

func switchCase(p *Account) {
	switch p.Status {
	case StatusActive:
		requireActive(p)
	case StatusInactive:
		requireInactive(p)
	default:
		requireActive(p) // want `cannot prove p<s> == StatusActive`
	}
}

// Несколько значений в одном case — дизъюнкция: фактов нет.
func switchMulti(p *Account) {
	switch p.Status {
	case StatusActive, StatusInactive:
		requireActive(p) // want `cannot prove p<s> == StatusActive`
	}
}

// default знает, что предыдущие значения не подошли.
func switchErr(force bool) {
	p := &Account{Status: StatusActive}
	switch err := p.Deactivate(force); err {
	case nil:
		requireInactive(p)
	default:
		requireActive(p)
	}
}

// switch без тега — цепочка if-else; путь, где ни одна ветка не подошла,
// продолжается после switch.
func switchTagless(force bool) {
	p := &Account{Status: StatusActive}
	err := p.Deactivate(force)
	switch {
	case err != nil:
		requireActive(p)
		return
	}
	requireInactive(p)
}

// После switch остаётся то, что верно во всех ветках.
func switchJoin(k int) {
	p := &Account{Status: StatusActive}
	switch k {
	case 1:
		p.Close()
	default:
		p.Status = StatusInactive
	}
	requireInactive(p)
}

func switchNoDefault(k int) {
	p := &Account{Status: StatusActive}
	switch k {
	case 1:
		p.Close()
	}
	requireInactive(p) // want `cannot prove p<s> == StatusInactive`
}

// break выходит из switch: его состояние тоже сливается.
func switchBreak(k int, c bool) {
	p := &Account{Status: StatusActive}
	switch k {
	case 1:
		if c {
			break
		}
		p.Close()
	default:
		p.Close()
	}
	requireInactive(p) // want `cannot prove p<s> == StatusInactive`
}

func switchLabeled(k int, c bool) {
	p := &Account{Status: StatusActive}
outer:
	switch k {
	case 1:
		switch {
		case c:
			break outer
		}
		p.Close()
	default:
		p.Close()
	}
	requireInactive(p) // want `cannot prove p<s> == StatusInactive`
}

// break внутри цикла выходит из цикла, а не из switch.
func switchLoopBreak(k int, xs []int) {
	p := &Account{Status: StatusActive}
	switch k {
	case 1:
		for range xs {
			break
		}
		p.Close()
	default:
		p.Close()
	}
	requireInactive(p)
}

// break из цикла наружу выходит из switch.
func switchLoopOuter(k int, xs []int) {
	p := &Account{Status: StatusActive}
outer:
	switch k {
	case 1:
		for range xs {
			break outer
		}
		p.Close()
	default:
		p.Close()
	}
	requireInactive(p) // want `cannot prove p<s> == StatusInactive`
}

// Состояние у такого break берётся с прохода, где забыто всё, что цикл
// меняет.
func switchLoopState(k int, xs []int) {
	p := &Account{Status: StatusActive}
outer:
	switch k {
	case 1:
		p.Close()
		for range xs {
			break outer
		}
	default:
		p.Close()
	}
	requireInactive(p)
	q := &Account{Status: StatusActive}
again:
	switch k {
	case 1:
		for range xs {
			requireActive(q) // want `cannot prove q<s> == StatusActive`
			if k > 2 {
				break again
			}
			q.Status = StatusInactive
		}
		q.Status = StatusActive
	}
	requireActive(q) // want `cannot prove q<s> == StatusActive`
}

// fallthrough: следующая ветка начинается и с конца предыдущей, где факт
// её значения неверен.
func switchFallthrough(p *Account) {
	switch p.Status {
	case StatusInactive:
		fallthrough
	case StatusActive:
		requireActive(p) // want `cannot prove p<s> == StatusActive`
	}
}

func switchFallState(k int) {
	p := &Account{Status: StatusActive}
	switch k {
	case 1:
		p.Close()
		fallthrough
	case 2:
		requireInactive(p) // want `cannot prove p<s> == StatusInactive`
	}
}

func typeSwitch(x any) {
	p := &Account{Status: StatusActive}
	switch v := x.(type) {
	case int:
		_ = v
		p.Close()
	default:
		p.Close()
	}
	requireInactive(p)
}

func selectJoin(ch chan int) {
	p := &Account{Status: StatusActive}
	select {
	case <-ch:
		p.Close()
	default:
		p.Close()
	}
	requireInactive(p)
}

func selectBlocks() {
	p := &Account{Status: StatusActive}
	select {}
	requireInactive(p)
}

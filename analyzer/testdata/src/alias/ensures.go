package alias

import (
	"errors"
	"fmt"
	"math/big"
)

// Постусловия ensures (SPEC.md, §6, §7).

// @ requires u<s> == StatusActive;
// @ ensures u<s> == StatusInactive;
func (u *Account) Close() { u.Status = StatusInactive }

// Typestate через вызов: ensures описывает новую версию объекта.
func typestateEnsures() {
	p := &Account{Status: StatusActive}
	p.Close()
	requireInactive(p)
	p.Close() // want `cannot prove p<s> == StatusActive`
}

// Тело обязано выполнять ensures на каждом выходе.
// @ ensures u<s> == StatusInactive;
func badClose(u *Account) {
	if u.Status == StatusActive {
		return // want `cannot prove ensures u<s> == StatusInactive`
	}
} // want `cannot prove ensures u<s> == StatusInactive`

// Either: условие — тег результата, правая часть — что известно в этой ветке.
// @ requires u<s> == StatusActive;
// @ ensures err == nil ==> u<s> == StatusInactive;
// @ ensures err != nil ==> u<s> == StatusActive;
func (u *Account) Deactivate(force bool) (err error) {
	if !force {
		return errors.New("not forced")
	}
	u.Status = StatusInactive
	return nil
}

func eitherCall(force bool) {
	p := &Account{Status: StatusActive}
	err := p.Deactivate(force)
	if err != nil {
		requireActive(p)
		return
	}
	requireInactive(p)
}

func eitherReversed(force bool) {
	p := &Account{Status: StatusActive}
	if err := p.Deactivate(force); err == nil {
		requireInactive(p)
		return
	}
	requireActive(p)
}

// Пока условие неизвестно, ничего не известно.
func eitherUnknown(force bool) {
	p := &Account{Status: StatusActive}
	_ = p.Deactivate(force)
	requireInactive(p) // want `cannot prove p<s> == StatusInactive`
}

// Отложенный факт переживает слияние веток, на которых он есть.
func eitherJoin(force bool) {
	p := &Account{Status: StatusActive}
	err := p.Deactivate(force)
	if force {
		p.Title = "forced"
	}
	if err == nil {
		requireInactive(p)
	}
}

// Отложенный факт описывает версию объекта после вызова, а не более поздние.
func eitherStale(force bool) {
	p := &Account{Status: StatusActive}
	err := p.Deactivate(force)
	p.Status = StatusActive
	if err == nil {
		requireInactive(p) // want `cannot prove p<s> == StatusInactive`
	}
}

// Возврат, на котором условие ложно, клаузу не проверяет; известно истинное
// или неизвестное условие — проверяет.
// @ ensures err == nil ==> u<s> == StatusInactive;
func badDeactivate(u *Account, force bool) (err error) {
	if !force {
		return nil // want `cannot prove ensures err == nil ==> u<s> == StatusInactive`
	}
	if u.Title == "" {
		return failure() // want `cannot prove ensures err == nil ==> u<s> == StatusInactive`
	}
	if u.Title == "x" {
		err = fmt.Errorf("title %s", u.Title)
		return
	}
	return errors.New("no")
}

func failure() error { return nil }

// ensures о результате-значении.
// @ ensures err == nil ==> res<c> == c;
func parseAmount(c string, raw string) (res Amount, err error) {
	if raw == "" {
		return Amount{}, errors.New("empty")
	}
	return Amount{Currency: c, Value: len(raw)}, nil
}

// @ requires a<c> == "usd";
func requireUSDAmount(a Amount) {}

func useParse() {
	a, err := parseAmount("usd", "1")
	if err != nil {
		return
	}
	requireUSDAmount(a)
	b, _ := parseAmount("usd", "2")
	requireUSDAmount(b) // want `cannot prove b<c> == "usd"`
}

// Условие на bool-результат.
// @ ensures ok == true ==> u<s> == StatusActive;
func isActive(u *Account) (ok bool) {
	if u.Status == StatusActive {
		return true
	}
	return false
}

func boolGuard(p *Account) {
	if isActive(p) {
		requireActive(p)
	}
	if !isActive(p) {
		return
	}
	requireActive(p)
}

// @ ensures u<s> == StatusInactive;
func (u *Account) Shut() { u.Status = StatusInactive }

// Отложенный вызов выполнится на выходе: его ensures ещё неверно.
func deferredCall() {
	p := &Account{Status: StatusActive}
	defer p.Shut()
	requireInactive(p) // want `cannot prove p<s> == StatusInactive`
}

// Объект за значением: ensures о параметре-значении — о том же значении.
// @ ensures a<s> == StatusActive;
func mustBeActive(a Account) {
	if a.Status != StatusActive {
		panic("inactive")
	}
}

func valueEnsures(a Account) {
	mustBeActive(a)
	requireInactiveV(a) // want `cannot prove a<s> == StatusInactive \("active" vs "inactive"\)`
}

// @ ensures err != nil ==> res == nil;
func todelete() (res *big.Int, err error) {
	return
}

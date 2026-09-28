// Package congruence — congruence closure над неинтерпретированными термами.
// Пакет не знает про Go: переменные, поля и индексы checker кодирует атомами
// и применениями функций.
package congruence

import (
	"fmt"
	"strings"
)

// Term — идентификатор терма в Bank. Одинаковые термы имеют одинаковый id.
type Term int32

type kind uint8

const (
	kAtom  kind = iota // переменная (версия переменной программы, свежий терм)
	kConst             // константа; разные константы различны
	kApp               // применение функции: fn(args...)
)

type termData struct {
	kind kind
	name string // имя атома, ключ константы или имя функции
	args []Term
}

// Bank хранит термы с hash-consing. Один Bank разделяют все состояния,
// которые нужно сравнивать или объединять (обычно — все состояния одной функции).
type Bank struct {
	terms []termData
	index map[string]Term
}

func NewBank() *Bank {
	return &Bank{index: map[string]Term{}}
}

// Atom возвращает атом с данным именем.
func (b *Bank) Atom(name string) Term { return b.intern(termData{kind: kAtom, name: name}) }

// Const возвращает константу. Константы с разными ключами различны.
func (b *Bank) Const(key string) Term { return b.intern(termData{kind: kConst, name: key}) }

// App возвращает применение fn к args.
func (b *Bank) App(fn string, args ...Term) Term {
	return b.intern(termData{kind: kApp, name: fn, args: args})
}

// Len — число термов в банке; id термов — от 0 до Len()-1.
func (b *Bank) Len() int { return len(b.terms) }

// IsConst сообщает, является ли t константой.
func (b *Bank) IsConst(t Term) bool { return b.terms[t].kind == kConst }

func (b *Bank) String(t Term) string {
	d := b.terms[t]
	if d.kind != kApp {
		return d.name
	}
	args := make([]string, len(d.args))
	for i, a := range d.args {
		args[i] = b.String(a)
	}
	return d.name + "(" + strings.Join(args, ", ") + ")"
}

func (b *Bank) intern(d termData) Term {
	key := b.key(d)
	if t, ok := b.index[key]; ok {
		return t
	}
	t := Term(len(b.terms))
	b.terms = append(b.terms, d)
	b.index[key] = t
	return t
}

func (b *Bank) key(d termData) string {
	var sb strings.Builder
	fmt.Fprintf(&sb, "%d:%q", d.kind, d.name)
	for _, a := range d.args {
		fmt.Fprintf(&sb, ",%d", a)
	}
	return sb.String()
}

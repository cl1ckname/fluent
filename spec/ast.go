package spec

import (
	"go/token"
	"strings"
)

// Clause — одна инструкция спецификации (заканчивается `;`).
type Clause interface {
	Pos() token.Pos
	String() string
	clause()
}

// Bound: `bound <p1 T1, p2, p3 T2>;` — у структуры.
type Bound struct {
	At     token.Pos
	Params []Param
}

// Param — индексный параметр структуры.
type Param struct {
	Name Ident
	Type TypeName
}

// Equals: `equals p;` — у поля: значение поля равно параметру p.
type Equals struct {
	At    token.Pos
	Param Ident
}

// Close: `close <e1, ...>;` — у поля bounded-типа: инстанцирование его параметров.
type Close struct {
	At   token.Pos
	Args []Term
}

// Requires: `requires e1 == e2 && ...;` — у функции.
type Requires struct {
	At  token.Pos
	Eqs []Equality
}

// Returns: `returns T1<e..>, T2;` — у функции.
type Returns struct {
	At      token.Pos
	Results []ResultType
}

// ResultType — тип результата. Args == nil означает, что индекс неизвестен.
type ResultType struct {
	Type TypeName
	Args []Term
}

type Equality struct {
	Left, Right Term
}

// TypeName — имя типа Go: `T` или `pkg.T`.
type TypeName struct {
	Pkg  *Ident
	Name Ident
}

type Ident struct {
	At   token.Pos
	Name string
}

// Term — выражение над значениями: путь или литерал.
type Term interface {
	Pos() token.Pos
	String() string
	term()
}

// Path: `x`, `x.f`, `x<p>`, `w.main<c>`.
type Path struct {
	Root  Ident
	Steps []Step
}

// Step — шаг пути: поле `.f` или индексный параметр `<p>`.
type Step struct {
	Name  Ident
	Index bool
}

// Lit — литерал Go. Kind: token.INT, FLOAT, IMAG, CHAR или STRING; Value — как в исходнике.
type Lit struct {
	At    token.Pos
	Kind  token.Token
	Value string
}

func (c *Bound) Pos() token.Pos    { return c.At }
func (c *Equals) Pos() token.Pos   { return c.At }
func (c *Close) Pos() token.Pos    { return c.At }
func (c *Requires) Pos() token.Pos { return c.At }
func (c *Returns) Pos() token.Pos  { return c.At }
func (t *Path) Pos() token.Pos     { return t.Root.At }
func (t *Lit) Pos() token.Pos      { return t.At }

func (*Bound) clause()    {}
func (*Equals) clause()   {}
func (*Close) clause()    {}
func (*Requires) clause() {}
func (*Returns) clause()  {}
func (*Path) term()       {}
func (*Lit) term()        {}

func (c *Bound) String() string {
	ps := make([]string, len(c.Params))
	for i, p := range c.Params {
		ps[i] = p.Name.Name + " " + p.Type.String()
	}
	return "bound <" + strings.Join(ps, ", ") + ">;"
}

func (c *Equals) String() string { return "equals " + c.Param.Name + ";" }

func (c *Close) String() string { return "close <" + joinTerms(c.Args) + ">;" }

func (c *Requires) String() string {
	es := make([]string, len(c.Eqs))
	for i, e := range c.Eqs {
		es[i] = e.String()
	}
	return "requires " + strings.Join(es, " && ") + ";"
}

func (c *Returns) String() string {
	rs := make([]string, len(c.Results))
	for i, r := range c.Results {
		rs[i] = r.String()
	}
	return "returns " + strings.Join(rs, ", ") + ";"
}

func (r ResultType) String() string {
	if r.Args == nil {
		return r.Type.String()
	}
	return r.Type.String() + "<" + joinTerms(r.Args) + ">"
}

func (e Equality) String() string { return e.Left.String() + " == " + e.Right.String() }

func (t TypeName) String() string {
	if t.Pkg != nil {
		return t.Pkg.Name + "." + t.Name.Name
	}
	return t.Name.Name
}

func (t *Path) String() string {
	var b strings.Builder
	b.WriteString(t.Root.Name)
	for _, s := range t.Steps {
		if s.Index {
			b.WriteString("<" + s.Name.Name + ">")
		} else {
			b.WriteString("." + s.Name.Name)
		}
	}
	return b.String()
}

func (t *Lit) String() string { return t.Value }

func joinTerms(ts []Term) string {
	ss := make([]string, len(ts))
	for i, t := range ts {
		ss[i] = t.String()
	}
	return strings.Join(ss, ", ")
}

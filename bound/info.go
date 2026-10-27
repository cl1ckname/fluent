// Package bound связывает спецификации с объектами go/types: какие у структуры
// индексные параметры, чем замкнуты её поля, что требуют и гарантируют функции.
package bound

import (
	"go/constant"
	"go/token"
	"go/types"
	"strings"
)

// Info — уточнённые типы пакета. Ключи — объекты go/types, как в types.Info.
type Info struct {
	Structs map[*types.TypeName]*Struct
	Funcs   map[*types.Func]*Func
}

// StructOf возвращает спецификацию именованного типа t, если она есть.
func (in *Info) StructOf(t types.Type) *Struct {
	n, ok := types.Unalias(t).(*types.Named)
	if !ok {
		return nil
	}
	return in.Structs[n.Origin().Obj()]
}

// Bounded возвращает спецификацию t, если у t есть индексные параметры.
func (in *Info) Bounded(t types.Type) *Struct {
	if s := in.StructOf(t); s != nil && len(s.Params) > 0 {
		return s
	}
	return nil
}

// FieldSpec возвращает аннотацию equals/close поля f структуры t или nil.
func (in *Info) FieldSpec(t types.Type, f *types.Var) *Field {
	if s := in.StructOf(t); s != nil {
		for _, fa := range s.Fields {
			if fa.Var == f {
				return fa
			}
		}
	}
	return nil
}

// Dependent сообщает, есть ли в значении типа t зависимые поля — поля
// с equals/close, в том числе во вложенных по значению структурах и массивах.
// Только такие поля защищаются правами доступа (ALIASING_DESIGN.md, §11.1).
func (in *Info) Dependent(t types.Type) bool {
	if s := in.StructOf(t); s != nil && len(s.Fields) > 0 {
		return true
	}
	switch u := t.Underlying().(type) {
	case *types.Struct:
		for f := range u.Fields() {
			if in.Dependent(f.Type()) {
				return true
			}
		}
	case *types.Array:
		return in.Dependent(u.Elem())
	}
	return false
}

// Tracked сообщает, нужны ли права на память со значением типа t: в нём есть
// зависимые или владеющие поля.
func (in *Info) Tracked(t types.Type) bool { return in.tracked(t, map[types.Type]bool{}) }

func (in *Info) tracked(t types.Type, seen map[types.Type]bool) bool {
	if in.Dependent(t) {
		return true
	}
	if seen[t] {
		return false
	}
	seen[t] = true
	switch u := t.Underlying().(type) {
	case *types.Struct:
		for f := range u.Fields() {
			if p, ok := f.Type().Underlying().(*types.Pointer); ok && in.tracked(p.Elem(), seen) ||
				!ok && in.tracked(f.Type(), seen) {
				return true
			}
		}
	case *types.Array:
		return in.tracked(u.Elem(), seen)
	}
	return false
}

// Owning сообщает, владеет ли поле f объектом, на который указывает:
// это указатель на значение, которому нужны права (ALIASING_DESIGN.md, §11.10).
func (in *Info) Owning(f *types.Var) bool {
	p, ok := f.Type().Underlying().(*types.Pointer)
	return ok && in.Tracked(p.Elem())
}

// Struct — структура с `bound` и/или аннотированными полями.
type Struct struct {
	Obj    *types.TypeName
	Params []*Param
	Fields []*Field // только аннотированные, в порядке объявления
}

func (s *Struct) Param(name string) *Param {
	for _, p := range s.Params {
		if p.Name == name {
			return p
		}
	}
	return nil
}

// Param — индексный параметр структуры.
type Param struct {
	Owner *types.TypeName
	Index int // позиция в T<...>
	Name  string
	Type  types.Type
	Pos   token.Pos
}

// Field — аннотация поля: задано ровно одно из Equals и Close.
type Field struct {
	Var    *types.Var
	Equals *Param
	Close  []Expr // аргументы для параметров типа поля, по порядку
}

// Func — контракт функции или метода.
type Func struct {
	Obj      *types.Func
	Requires []Equality
	Returns  []Result // nil, если returns нет; иначе по одному на каждый результат
	Ensures  []Ensure
}

// Ensure — клауза ensures: если Guard верно на выходе (или Guard == nil),
// то верны Eqs. Термы Eqs берутся на выходе; Var результата —
// возвращаемое значение.
type Ensure struct {
	Pos   token.Pos
	Guard *Guard
	Eqs   []Equality
}

// Guard — условие клаузы: результат Result (позиция Index) равен
// (Neq — не равен) константе Value.
type Guard struct {
	Result *types.Var
	Index  int
	Neq    bool
	Value  *Const
}

// Result — тип результата. Args == nil: индекс неизвестен (или тип не bounded).
type Result struct {
	Type types.Type
	Args []Expr
}

type Equality struct {
	Left, Right Expr
}

// Expr — разрешённый терм спецификации.
type Expr interface {
	Type() types.Type
	Pos() token.Pos
	String() string
}

// Var — параметр или receiver функции (значение в момент входа).
type Var struct {
	Obj *types.Var
	At  token.Pos
}

// Const — литерал, константа Go или nil (Val == nil).
type Const struct {
	Val  constant.Value
	Typ  types.Type
	Text string
	At   token.Pos
}

// FieldOf — `x.f`.
type FieldOf struct {
	X     Expr
	Field *types.Var
	At    token.Pos
}

// ParamOf — `x<p>`.
type ParamOf struct {
	X     Expr
	Param *Param
	At    token.Pos
}

// SelfParam — параметр своей структуры внутри `close <...>`.
type SelfParam struct {
	Param *Param
	At    token.Pos
}

func (e *Var) Type() types.Type       { return e.Obj.Type() }
func (e *Const) Type() types.Type     { return e.Typ }
func (e *FieldOf) Type() types.Type   { return e.Field.Type() }
func (e *ParamOf) Type() types.Type   { return e.Param.Type }
func (e *SelfParam) Type() types.Type { return e.Param.Type }

func (e *Var) Pos() token.Pos       { return e.At }
func (e *Const) Pos() token.Pos     { return e.At }
func (e *FieldOf) Pos() token.Pos   { return e.At }
func (e *ParamOf) Pos() token.Pos   { return e.At }
func (e *SelfParam) Pos() token.Pos { return e.At }

func (e *Var) String() string       { return e.Obj.Name() }
func (e *Const) String() string     { return e.Text }
func (e *FieldOf) String() string   { return e.X.String() + "." + e.Field.Name() }
func (e *ParamOf) String() string   { return e.X.String() + "<" + e.Param.Name + ">" }
func (e *SelfParam) String() string { return e.Param.Name }

func (g *Guard) String() string {
	op := " == "
	if g.Neq {
		op = " != "
	}
	return g.Result.Name() + op + g.Value.String()
}

func (e Ensure) String() string {
	es := make([]string, len(e.Eqs))
	for i, eq := range e.Eqs {
		es[i] = eq.String()
	}
	g := ""
	if e.Guard != nil {
		g = e.Guard.String() + " ==> "
	}
	return g + strings.Join(es, " && ")
}

func (e Equality) String() string { return e.Left.String() + " == " + e.Right.String() }

func (s *Struct) String() string {
	var b strings.Builder
	b.WriteString(s.Obj.Name())
	if len(s.Params) > 0 {
		ps := make([]string, len(s.Params))
		for i, p := range s.Params {
			ps[i] = p.Name + " " + typeString(p.Type, s.Obj.Pkg())
		}
		b.WriteString(" <" + strings.Join(ps, ", ") + ">")
	}
	for _, f := range s.Fields {
		b.WriteString("; " + f.Var.Name())
		if f.Equals != nil {
			b.WriteString(" equals " + f.Equals.Name)
		} else {
			b.WriteString(" close <" + joinExprs(f.Close) + ">")
		}
	}
	return b.String()
}

func (f *Func) String() string {
	var parts []string
	for _, e := range f.Requires {
		parts = append(parts, "requires "+e.String())
	}
	if f.Returns != nil {
		rs := make([]string, len(f.Returns))
		for i, r := range f.Returns {
			rs[i] = r.format(f.Obj.Pkg())
		}
		parts = append(parts, "returns "+strings.Join(rs, ", "))
	}
	for _, e := range f.Ensures {
		parts = append(parts, "ensures "+e.String())
	}
	return f.Obj.Name() + ": " + strings.Join(parts, "; ")
}

func (r Result) format(pkg *types.Package) string {
	if r.Args == nil {
		return typeString(r.Type, pkg)
	}
	return typeString(r.Type, pkg) + "<" + joinExprs(r.Args) + ">"
}

func joinExprs(es []Expr) string {
	ss := make([]string, len(es))
	for i, e := range es {
		ss[i] = e.String()
	}
	return strings.Join(ss, ", ")
}

// typeString печатает тип относительно пакета pkg: amount, time.Duration.
func typeString(t types.Type, pkg *types.Package) string {
	return types.TypeString(t, func(p *types.Package) string {
		if p == pkg {
			return ""
		}
		return p.Name()
	})
}

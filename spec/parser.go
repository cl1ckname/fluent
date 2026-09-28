package spec

import (
	"fmt"
	"go/ast"
	"go/token"
)

// Error — синтаксическая ошибка в спецификации.
type Error struct {
	Pos token.Pos
	Msg string
}

func (e Error) Error() string { return e.Msg }

// ParseDoc извлекает и разбирает все спецификации doc-комментария.
func ParseDoc(doc *ast.CommentGroup) ([]Clause, []Error) {
	var clauses []Clause
	var errs []Error
	for _, b := range Extract(doc) {
		cs, es := Parse(b)
		clauses = append(clauses, cs...)
		errs = append(errs, es...)
	}
	return clauses, errs
}

// Parse разбирает один блок. После ошибки парсер пропускает текст до следующей `;`
// и продолжает, поэтому одна плохая инструкция не прячет остальные.
func Parse(b Block) ([]Clause, []Error) {
	toks, errs := lex(b)
	p := &parser{toks: toks}
	var clauses []Clause
	for p.peek().kind != kEOF {
		if c, err := p.clause(); err != nil {
			errs = append(errs, *err)
			p.sync()
		} else {
			clauses = append(clauses, c)
		}
	}
	return clauses, errs
}

type parser struct {
	toks []tok
	i    int
}

// bailout прерывает разбор текущей инструкции.
type bailout struct{ err Error }

func (p *parser) peek() tok { return p.toks[p.i] }

func (p *parser) next() tok {
	t := p.toks[p.i]
	if t.kind != kEOF {
		p.i++
	}
	return t
}

func (p *parser) got(k kind) bool {
	if p.peek().kind == k {
		p.next()
		return true
	}
	return false
}

func (p *parser) expect(k kind) tok {
	t := p.peek()
	if t.kind != k {
		p.fail(t.pos, "expected %s, found %s", k, describe(t))
	}
	return p.next()
}

func (p *parser) fail(pos token.Pos, format string, args ...any) {
	panic(bailout{Error{pos, fmt.Sprintf(format, args...)}})
}

func (p *parser) sync() {
	for {
		switch p.next().kind {
		case kSemi, kEOF:
			return
		}
	}
}

func describe(t tok) string {
	if t.kind == kIdent || t.kind == kLit {
		return fmt.Sprintf("%q", t.text)
	}
	return t.kind.String()
}

func (p *parser) clause() (c Clause, err *Error) {
	defer func() {
		if r := recover(); r != nil {
			b, ok := r.(bailout)
			if !ok {
				panic(r)
			}
			err = &b.err
		}
	}()
	kw := p.expect(kIdent)
	switch kw.text {
	case "bound":
		c = p.bound(kw.pos)
	case "equals":
		c = &Equals{At: kw.pos, Param: p.ident()}
	case "close":
		c = &Close{At: kw.pos, Args: p.args()}
	case "requires":
		c = p.requires(kw.pos)
	case "returns":
		c = p.returns(kw.pos)
	default:
		p.fail(kw.pos, "unknown clause %q", kw.text)
	}
	p.expect(kSemi)
	return c, nil
}

// bound <a, b T1, c T2>
func (p *parser) bound(at token.Pos) *Bound {
	b := &Bound{At: at}
	p.expect(kLt)
	for {
		names := []Ident{p.ident()}
		for p.got(kComma) {
			names = append(names, p.ident())
		}
		if p.peek().kind != kIdent {
			p.fail(p.peek().pos, "missing type for parameter %s", names[len(names)-1].Name)
		}
		typ := p.typeName()
		for _, n := range names {
			b.Params = append(b.Params, Param{Name: n, Type: typ})
		}
		if !p.got(kComma) {
			break
		}
	}
	p.expect(kGt)
	return b
}

func (p *parser) requires(at token.Pos) *Requires {
	r := &Requires{At: at}
	for {
		l := p.term()
		p.expect(kEq)
		r.Eqs = append(r.Eqs, Equality{Left: l, Right: p.term()})
		if !p.got(kAnd) {
			return r
		}
	}
}

func (p *parser) returns(at token.Pos) *Returns {
	r := &Returns{At: at}
	for {
		rt := ResultType{Type: p.typeName()}
		if p.peek().kind == kLt {
			rt.Args = p.args()
		}
		r.Results = append(r.Results, rt)
		if !p.got(kComma) {
			return r
		}
	}
}

// args: '<' term (',' term)* '>'
func (p *parser) args() []Term {
	p.expect(kLt)
	ts := []Term{p.term()}
	for p.got(kComma) {
		ts = append(ts, p.term())
	}
	p.expect(kGt)
	return ts
}

func (p *parser) term() Term {
	if t := p.peek(); t.kind == kLit {
		p.next()
		return &Lit{At: t.pos, Kind: t.litKind, Value: t.text}
	}
	path := &Path{Root: p.ident()}
	for {
		switch {
		case p.got(kDot):
			path.Steps = append(path.Steps, Step{Name: p.ident()})
		case p.peek().kind == kLt:
			p.next()
			path.Steps = append(path.Steps, Step{Name: p.ident(), Index: true})
			p.expect(kGt)
		default:
			return path
		}
	}
}

func (p *parser) typeName() TypeName {
	id := p.ident()
	if p.got(kDot) {
		return TypeName{Pkg: &id, Name: p.ident()}
	}
	return TypeName{Name: id}
}

func (p *parser) ident() Ident {
	t := p.expect(kIdent)
	return Ident{At: t.pos, Name: t.text}
}

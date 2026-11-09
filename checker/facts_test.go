package checker

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"testing"

	"fluent/bound"
)

const factsSrc = `package p

type Kind int

const Neg Kind = -3

// @ bound <k Kind, c string>;
type Box struct {
	// @ equals k;
	K Kind
	// @ equals c;
	C string
}

// @ bound <c string>;
type Pair struct {
	// @ close <Neg, c>;
	A Box
	Next *Pair
}

// @ requires a<k> == Neg && b<c> == "x\n";
// @ returns Box<a<k>, "y">, _;
// @ ensures err == nil ==> res<c> == b<c>;
func F(a, b Box) (res Box, err error) { panic(0) }

// @ requires p.A<c> == "z";
func (p *Pair) M() {}

// @ requires a<k> == 7;
func G(a Box) {}

func Keep(p *Pair) { global = p }

// Неэкспортированная функция в факт не попадает: снаружи её не вызвать.
func hidden(p *Pair) {}

var global *Pair
`

func TestFactsRoundTrip(t *testing.T) {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "p.go", factsSrc, parser.ParseComments)
	if err != nil {
		t.Fatal(err)
	}
	info := &types.Info{
		Types: map[ast.Expr]types.TypeAndValue{}, Defs: map[*ast.Ident]types.Object{}, Uses: map[*ast.Ident]types.Object{},
		Selections: map[*ast.SelectorExpr]*types.Selection{}, Scopes: map[ast.Node]*types.Scope{}, Implicits: map[ast.Node]types.Object{},
	}
	pkg, err := (&types.Config{Importer: importer.Default()}).Check("p", fset, []*ast.File{f}, info)
	if err != nil {
		t.Fatal(err)
	}
	exp := Check(&Package{Fset: fset, Files: []*ast.File{f}, Types: pkg, Info: info}, func(d Diagnostic) {
		t.Errorf("%s: %s", fset.Position(d.Pos), d.Message)
	})
	data, err := exp.Encode(pkg)
	if err != nil {
		t.Fatal(err)
	}
	got, bad, err := Decode([]EncodedPackage{{Pkg: pkg, Data: data}}, nil)
	if err != nil {
		t.Fatal(err)
	}
	if len(bad) != 0 {
		t.Errorf("spec errors: %v", bad)
	}
	if a, b := exp.Describe(pkg), got.Describe(pkg); a != b {
		t.Errorf("describe:\n  before %s\n  after  %s", a, b)
	}
	for obj, s := range exp.Specs.Structs {
		if g := got.Specs.Structs[obj]; g == nil || g.String() != s.String() {
			t.Errorf("struct %s: before %v, after %v", obj.Name(), s, g)
		}
	}
	for obj, fn := range exp.Specs.Funcs {
		g := got.Specs.Funcs[obj]
		if g == nil || g.String() != fn.String() {
			t.Errorf("func %s: before %v, after %v", obj.Name(), fn, g)
			continue
		}
		checkConsts(t, obj.Name(), fn, g)
	}
	for obj, s := range exp.summaries {
		g := got.summaries[obj]
		if !obj.Exported() {
			if g != nil {
				t.Errorf("summary %s: unexported function exported", obj.Name())
			}
			continue
		}
		if g == nil || !g.equal(s) {
			t.Errorf("summary %s: before %+v, after %+v", obj.Name(), s, g)
		}
	}
	keep := pkg.Scope().Lookup("Keep").(*types.Func)
	if k := got.summaries[keep].params[0].kept; k != "p.go: stored in global at line 33" {
		t.Errorf("kept reason: %q", k)
	}
}

// checkConsts сравнивает значения констант контрактов до и после.
func checkConsts(t *testing.T, name string, a, b *bound.Func) {
	t.Helper()
	var ca, cb []*bound.Const
	collect := func(out *[]*bound.Const, fn *bound.Func) {
		var walk func(bound.Expr)
		walk = func(e bound.Expr) {
			switch e := e.(type) {
			case *bound.Const:
				*out = append(*out, e)
			case *bound.FieldOf:
				walk(e.X)
			case *bound.ParamOf:
				walk(e.X)
			}
		}
		for _, eq := range fn.Requires {
			walk(eq.Left)
			walk(eq.Right)
		}
		for _, r := range fn.Returns {
			for _, e := range r.Args {
				walk(e)
			}
		}
		for _, en := range fn.Ensures {
			if en.Guard != nil {
				walk(en.Guard.Value)
			}
		}
	}
	collect(&ca, a)
	collect(&cb, b)
	if len(ca) != len(cb) {
		t.Fatalf("%s: %d constants before, %d after", name, len(ca), len(cb))
	}
	for i := range ca {
		va, vb := "nil", "nil"
		if ca[i].Val != nil {
			va = ca[i].Val.ExactString()
		}
		if cb[i].Val != nil {
			vb = cb[i].Val.ExactString()
		}
		if va != vb || !types.Identical(ca[i].Typ, cb[i].Typ) {
			t.Errorf("%s: constant %s: before %s %s, after %s %s", name, ca[i].Text, va, ca[i].Typ, vb, cb[i].Typ)
		}
	}
}

// Значения констант всех видов переживают кодирование.
func TestConstRoundTrip(t *testing.T) {
	pkg := types.NewPackage("p", "p")
	enc := &encoder{pkg: pkg}
	d := &decoder{}
	for _, src := range []string{"-3", "1 << 70", "-(1 << 70)", "1.0 / 3", "-0.5", "1e300 * 1e300", "1 - 2i", "-1.5i", "true", `"a\x00b"`, "'x'"} {
		tv, err := types.Eval(token.NewFileSet(), nil, token.NoPos, src)
		if err != nil {
			t.Fatal(err)
		}
		w, ok := enc.constant(&bound.Const{Val: tv.Value, Typ: tv.Type, Text: src})
		if !ok {
			t.Fatalf("%s: not encoded", src)
		}
		c, ok := d.constant(w)
		if !ok || c.Val.ExactString() != tv.Value.ExactString() || c.Val.Kind() != tv.Value.Kind() {
			t.Errorf("%s: before %s, after %v", src, tv.Value.ExactString(), c)
		}
	}
}

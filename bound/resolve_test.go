package bound

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"slices"
	"strings"
	"testing"
)

func resolveSource(t *testing.T, src string) (*Info, []string) {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "p.go", src, parser.ParseComments)
	if err != nil {
		t.Fatal(err)
	}
	info := &types.Info{
		Defs:   map[*ast.Ident]types.Object{},
		Uses:   map[*ast.Ident]types.Object{},
		Scopes: map[ast.Node]*types.Scope{},
	}
	conf := types.Config{Importer: importer.Default()}
	pkg, err := conf.Check("p", fset, []*ast.File{f}, info)
	if err != nil {
		t.Fatal(err)
	}
	var errs []string
	out := Resolve([]*ast.File{f}, pkg, info, func(pos token.Pos, msg string) {
		errs = append(errs, msg)
	})
	return out, errs
}

const money = `package p

import "time"

type Currency string

const RUB Currency = "rub"

//@ bound <c Currency>;
type amount struct {
	//@ equals c;
	currency Currency
	value    float64
}

//@ bound <from, to Currency>;
type rate struct {
	//@ equals from;
	from Currency
	//@ equals to;
	to Currency
	k  float64
}

//@ bound <c Currency>;
type wallet struct {
	//@ close <c>;
	main, reserve amount
	//@ close <RUB>;
	tax  amount
	name string
}

type order struct {
	//@ close <"usd">;
	price amount
}

//@ returns amount<c>;
func newAmount(c Currency, v float64) amount { return amount{currency: c, value: v} }

//@ requires a<c> == b<c>;
//@ returns amount<a<c>>;
func (a amount) sum(b amount) amount { return a }

//@ requires a<c> == r<from>;
//@ returns amount<r<to>>, _, time.Duration;
func (r *rate) convert(a amount) (amount, []byte, time.Duration) { return a, nil, 0 }

// @ requires w.main<c> == w.tax<c> && a<c> == RUB;
//@ returns wallet;
func deposit(w wallet, a amount) wallet { return w }
`

func TestResolveMoney(t *testing.T) {
	out, errs := resolveSource(t, money)
	if len(errs) > 0 {
		t.Fatalf("errors: %q", errs)
	}

	var structs, funcs []string
	for _, s := range out.Structs {
		structs = append(structs, s.String())
	}
	for _, f := range out.Funcs {
		funcs = append(funcs, f.String())
	}
	slices.Sort(structs)
	slices.Sort(funcs)

	wantStructs := []string{
		"amount <c Currency>; currency equals c",
		"order; price close <\"usd\">",
		"rate <from Currency, to Currency>; from equals from; to equals to",
		"wallet <c Currency>; main close <c>; reserve close <c>; tax close <RUB>",
	}
	wantFuncs := []string{
		"convert: requires a<c> == r<from>; returns amount<r<to>>, []byte, time.Duration",
		"deposit: requires w.main<c> == w.tax<c>; requires a<c> == RUB; returns wallet",
		"newAmount: returns amount<c>",
		"sum: requires a<c> == b<c>; returns amount<a<c>>",
	}
	if !slices.Equal(structs, wantStructs) {
		t.Errorf("structs:\n%s\nwant:\n%s", strings.Join(structs, "\n"), strings.Join(wantStructs, "\n"))
	}
	if !slices.Equal(funcs, wantFuncs) {
		t.Errorf("funcs:\n%s\nwant:\n%s", strings.Join(funcs, "\n"), strings.Join(wantFuncs, "\n"))
	}
}

func TestResolveErrors(t *testing.T) {
	const prelude = `package p

//@ bound <c string>;
type amount struct {
	//@ equals c;
	currency string
}

`
	tests := []struct {
		src  string
		want string
	}{
		{"//@ bound <c string>;\ntype x int", "bound is only allowed on struct types"},
		{"//@ bound <c string>; bound <d string>;\ntype x struct{\n//@ equals c;\nf string}", "duplicate bound"},
		{"//@ bound <c, c string>;\ntype x struct{\n//@ equals c;\nf string}", "duplicate parameter c"},
		{"type S []int\n//@ bound <c S>;\ntype x struct{\n//@ equals c;\nf S}", "type S is not comparable"},
		{"//@ bound <c nope>;\ntype x struct{}", "nope is not a type"},
		{"//@ bound <c string>;\ntype x struct{ f string }", "parameter c is not used"},
		{"//@ bound <c string>;\ntype x struct{\n//@ equals d;\nf string}", "x has no bound parameter d"},
		{"//@ bound <c string>;\ntype x struct{\n//@ equals c;\nf int}", "field f has type int, parameter c has type string"},
		{"type x struct{\n//@ close <\"rub\">;\nf string}", "type string has no bound parameters"},
		{"type x struct{\n//@ close <\"rub\", \"usd\">;\nf amount}", "amount has 1 bound parameters, got 2 arguments"},
		{"type x struct{\n//@ close <42>;\nf amount}", "cannot use 42 (type untyped int) as parameter c of amount"},
		{"type x struct{\n//@ close <\"a\">; close <\"b\">;\nf amount}", "field already has close annotation"},
		{"type x struct{\n//@ requires a == b;\nf amount}", "requires is not allowed on a field"},
		{"type x struct{\n//@ close <\"a\">;\namount}", "embedded fields are not supported"},
		{"//@ returns amount;\ntype x struct{}", "returns is not allowed on a type declaration"},
		{"//@ bound <c string>;\nvar v int", "bound is not allowed here"},
		{"//@ bound <c string>;\nfunc f() {}", "bound is not allowed on a function"},
		{"//@ requires a<c> == b.currency;\nfunc f(a amount) {}", "undefined: b"},
		{"//@ requires a<d> == \"rub\";\nfunc f(a amount) {}", "type amount has no bound parameter d"},
		{"//@ requires a.value == \"rub\";\nfunc f(a amount) {}", "type amount has no field value"},
		{"//@ requires a.currency == \"rub\";\nfunc f(a amount) {}", "a.currency is not x<p> or a constant"},
		{"//@ requires a<c> == s;\nfunc f(a amount, s string) {}", "s is not x<p> or a constant"},
		{"const K = \"k\"\n//@ requires K == \"k\";\nfunc f() {}", "K == \"k\" has none"},
		{"//@ requires n<c> == 1;\nfunc f(n int) {}", "type int has no bound parameters"},
		{"//@ requires a<c> == 1;\nfunc f(a amount) {}", "mismatched types string and untyped int"},
		{"var g string\n//@ requires a<c> == g;\nfunc f(a amount) {}", "g is not a parameter or constant"},
		{"const K = \"k\"\n//@ requires K.x == \"a\";\nfunc f() {}", "cannot select from constant K"},
		{"//@ returns amount;\nfunc f() (amount, error) { return amount{}, nil }", "returns lists 1 types, function has 2 results"},
		{"//@ returns string;\nfunc f() amount { return amount{} }", "result 1 has type amount, returns says string"},
		{"//@ returns string<\"a\">;\nfunc f() string { return \"\" }", "type string has no bound parameters"},
		{"//@ returns _<\"a\">;\nfunc f() string { return \"\" }", "_ cannot have arguments"},
		{"//@ returns amount<b>;\nfunc f(a string) amount { return amount{} }", "undefined: b"},
		{"//@ returns amount; returns amount;\nfunc f() amount { return amount{} }", "duplicate returns"},
	}
	for _, tt := range tests {
		_, errs := resolveSource(t, prelude+tt.src)
		// Проверяем первую ошибку: следом могут идти наведённые (например, «не используется»).
		if len(errs) == 0 || !strings.Contains(errs[0], tt.want) {
			t.Errorf("%s\n  errors: %q\n  want:   %q", tt.src, errs, tt.want)
		}
	}
}

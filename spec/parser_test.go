package spec

import (
	"go/ast"
	goparser "go/parser"
	"go/token"
	"strings"
	"testing"
)

func parseString(t *testing.T, src string) ([]Clause, []Error) {
	t.Helper()
	return Parse(Block{Pos: 1, Text: src})
}

func TestParseOK(t *testing.T) {
	tests := []struct {
		src  string
		want string // String() всех инструкций через пробел
	}{
		{"bound <c string>;", "bound <c string>;"},
		{"bound <from, to string>;", "bound <from string, to string>;"},
		{"bound <a, b string, n int, k money.Kind>;", "bound <a string, b string, n int, k money.Kind>;"},
		{"equals c;", "equals c;"},
		{"close <c>;", "close <c>;"},
		{`close <c, "rub", 42, 'x', -1.5e-3>;`, `close <c, "rub", 42, 'x', -1.5e-3>;`},
		{"requires a<c> == b<c>;", "requires a<c> == b<c>;"},
		{"requires a<c>==b<c>;", "requires a<c> == b<c>;"},
		{`requires a<c> == r<from> && r<to> == "usd";`, `requires a<c> == r<from> && r<to> == "usd";`},
		{"requires w.main<c> == a.currency;", "requires w.main<c> == a.currency;"},
		{"requires x == nil;", "requires x == nil;"},
		{"returns amount<c>;", "returns amount<c>;"},
		{"returns amount<a<c>>;", "returns amount<a<c>>;"},
		{"returns amount<r<to>>, error;", "returns amount<r<to>>, error;"},
		{"returns amount, money.amount<w.main<c>>;", "returns amount, money.amount<w.main<c>>;"},
		{"requires a<c> == b<c>; returns amount<a<c>>;", "requires a<c> == b<c>; returns amount<a<c>>;"},
		{"\n  requires a<c> == b<c>;\n  @ returns amount<a<c>>; ", "requires a<c> == b<c>; returns amount<a<c>>;"},
		{"   ", ""},
	}
	for _, tt := range tests {
		cs, errs := parseString(t, tt.src)
		if len(errs) > 0 {
			t.Errorf("%q: unexpected errors: %v", tt.src, errs)
			continue
		}
		var got []string
		for _, c := range cs {
			got = append(got, c.String())
		}
		if g := strings.Join(got, " "); g != tt.want {
			t.Errorf("%q:\n got  %s\n want %s", tt.src, g, tt.want)
		}
	}
}

func TestParseErrors(t *testing.T) {
	tests := []struct {
		src     string
		wantErr string
		wantOK  int // сколько инструкций всё равно разобрано
	}{
		{"bound <c string>", "expected ';'", 0},
		{"bound <c>;", "missing type for parameter c", 0},
		{"bound <>;", "expected identifier", 0},
		{"close <>;", "expected identifier", 0},
		{"ensures a == b;", `unknown clause "ensures"`, 0},
		{"requires a<c> = b<c>;", "unexpected character '='", 0},
		{"requires a<c>;", "expected '=='", 0},
		{`requires a == "rub;`, "unterminated literal", 0},
		{"requires a == 0x;", "invalid number literal 0x", 0},
		{"returns amount<a<c>;", "expected '>'", 0},
		{"foo; requires a == b; returns amount<;", `unknown clause "foo"`, 1},
	}
	for _, tt := range tests {
		cs, errs := parseString(t, tt.src)
		if len(errs) == 0 {
			t.Errorf("%q: expected error %q, got none", tt.src, tt.wantErr)
			continue
		}
		if !strings.Contains(errs[0].Msg, tt.wantErr) {
			t.Errorf("%q: got error %q, want %q", tt.src, errs[0].Msg, tt.wantErr)
		}
		if len(cs) != tt.wantOK {
			t.Errorf("%q: parsed %d clauses, want %d", tt.src, len(cs), tt.wantOK)
		}
	}
}

func TestParseDocPositions(t *testing.T) {
	const src = `package p

//@ bound <c string>;
type amount struct {
	/*@ equals
	    c; */
	currency string
}

// Обычный комментарий.
//@ requires a<c> == b<c>; returns amount<a<c>>;
func sum(a, b amount) amount { return a }
`
	fset := token.NewFileSet()
	f, err := goparser.ParseFile(fset, "p.go", src, goparser.ParseComments)
	if err != nil {
		t.Fatal(err)
	}
	gen := f.Decls[0].(*ast.GenDecl)
	field := gen.Specs[0].(*ast.TypeSpec).Type.(*ast.StructType).Fields.List[0]
	fn := f.Decls[1].(*ast.FuncDecl)

	check := func(doc *ast.CommentGroup, wantLines ...int) {
		t.Helper()
		cs, errs := ParseDoc(doc)
		if len(errs) > 0 {
			t.Fatalf("unexpected errors: %v", errs)
		}
		if len(cs) != len(wantLines) {
			t.Fatalf("got %d clauses, want %d", len(cs), len(wantLines))
		}
		for i, c := range cs {
			if l := fset.Position(c.Pos()).Line; l != wantLines[i] {
				t.Errorf("%s: line %d, want %d", c, l, wantLines[i])
			}
		}
	}
	check(gen.Doc, 3)
	check(field.Doc, 5)
	check(fn.Doc, 11, 11)

	// Терм во второй строке блочного комментария: позиция должна указывать туда.
	cs, _ := ParseDoc(field.Doc)
	p := fset.Position(cs[0].(*Equals).Param.At)
	if p.Line != 6 || p.Column != 6 {
		t.Errorf("param position %d:%d, want 6:6", p.Line, p.Column)
	}
}

func TestExtractGofmtPrefix(t *testing.T) {
	// gofmt превращает `//@` в `// @` в doc-комментариях объявлений верхнего уровня.
	doc := &ast.CommentGroup{List: []*ast.Comment{
		{Slash: 10, Text: "// @ bound <c string>;"},
		{Slash: 40, Text: "// обычный комментарий"},
		{Slash: 70, Text: "//@ requires a<c> == b<c>;"},
	}}
	cs, errs := ParseDoc(doc)
	if len(errs) > 0 || len(cs) != 2 {
		t.Fatalf("clauses %v, errors %v", cs, errs)
	}
	if cs[0].Pos() != 15 || cs[1].Pos() != 74 {
		t.Errorf("positions %d, %d; want 15, 74", cs[0].Pos(), cs[1].Pos())
	}
}

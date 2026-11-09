package lsp

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"go.lsp.dev/protocol"
)

const definitions = `package money
// @ bound <c string>;
type amount struct {
 // @ equals c;
 currency string
}
// @ returns amount<c>;
func newAmount(c string) amount { return amount{currency: c} }
// @ requires a<c> == b<c>;
func (a amount) sum(b amount) {}
`

const badCall = `package money
func use() { newAmount("usd").sum(newAmount("rub")) }
`

func writeFile(t *testing.T, dir, name, content string) string {
	t.Helper()
	path := filepath.Join(dir, name)
	if err := os.WriteFile(path, []byte(content), 0600); err != nil {
		t.Fatal(err)
	}
	return path
}

func testModule(t *testing.T) string {
	t.Helper()
	dir := filepath.Join(t.TempDir(), "пакет with spaces")
	if err := os.Mkdir(dir, 0700); err != nil {
		t.Fatal(err)
	}
	writeFile(t, dir, "go.mod", "module example.com/money\n\ngo 1.26.0\n")
	return dir
}

func TestAnalyzePackageAndTests(t *testing.T) {
	dir := testModule(t)
	writeFile(t, dir, "defs.go", definitions)
	call := writeFile(t, dir, "call.go", badCall)
	internal := writeFile(t, dir, "internal_test.go", strings.Replace(badCall, "func use()", "func testUse()", 1))
	external := writeFile(t, dir, "external_test.go", `package money_test
// @ bound <c string>;
type amount struct {
 // @ equals c;
 currency string
}
// @ returns amount<c>;
func newAmount(c string) amount { return amount{currency: c} }
// @ requires a<c> == b<c>;
func (a amount) sum(b amount) {}
func use() { newAmount("usd").sum(newAmount("rub")) }
`)
	result := analyze(context.Background(), dir, nil)
	if len(result.messages) != 0 {
		t.Fatalf("load: %v", result.messages)
	}
	for _, path := range []string{call, internal, external} {
		if got := len(result.diagnostics[path]); got != 1 {
			t.Fatalf("%s: got %d diagnostics, want 1: %+v", path, got, result)
		}
		d := result.diagnostics[path][0]
		if d.Severity != protocol.DiagnosticSeverityError || !strings.Contains(string(d.Message.(protocol.String)), "cannot prove") {
			t.Fatalf("unexpected diagnostic: %+v", d)
		}
	}
}

func TestAnalyzeOverlayAndGoErrors(t *testing.T) {
	dir := testModule(t)
	defs := writeFile(t, dir, "defs.go", definitions)
	call := writeFile(t, dir, "call.go", badCall)
	overlay := map[string][]byte{call: []byte(strings.ReplaceAll(badCall, "usd", "rub"))}
	result := analyze(context.Background(), dir, overlay)
	if len(result.messages) != 0 || len(result.diagnostics) != 0 {
		t.Fatalf("overlay should fix call: %+v", result)
	}
	for _, broken := range []string{"package money\nfunc broken( {", definitions + "\nvar broken int = \"string\"\n"} {
		overlay[defs] = []byte(broken)
		result = analyze(context.Background(), dir, overlay)
		if len(result.messages) == 0 || len(result.diagnostics) != 0 {
			t.Fatalf("Go errors should skip checking: %+v", result)
		}
	}
	delete(overlay, defs)
	delete(overlay, call)
	result = analyze(context.Background(), dir, overlay)
	if len(result.messages) != 0 || len(result.diagnostics[call]) != 1 {
		t.Fatalf("did not recover: %+v", result)
	}
}

func TestDiagnosticRange(t *testing.T) {
	for _, tt := range []struct {
		name, src, marker string
		want              protocol.Range
	}{
		{"unicode token", "package p\r\nfunc f() { _ = \"😀\"; переменная() }\r\n", "переменная", protocol.Range{Start: protocol.Position{Line: 1, Character: 21}, End: protocol.Position{Line: 1, Character: 31}}},
		{"spec comment", "// @ bound <валюта string>;\r\n", "валюта", protocol.Range{Start: protocol.Position{Character: 12}, End: protocol.Position{Character: 13}}},
		{"eof", "package p\n", "", protocol.Range{Start: protocol.Position{Line: 1}, End: protocol.Position{Line: 1}}},
	} {
		t.Run(tt.name, func(t *testing.T) {
			offset := len(tt.src)
			if tt.marker != "" {
				offset = strings.Index(tt.src, tt.marker)
			}
			if got := diagnosticRange([]byte(tt.src), offset); got != tt.want {
				t.Fatalf("got %+v, want %+v", got, tt.want)
			}
		})
	}
}

func TestPhysicalPositionsAndSpecErrors(t *testing.T) {
	dir := testModule(t)
	writeFile(t, dir, "defs.go", definitions)
	path := writeFile(t, dir, "call.go", "package money\n//line imaginary.go:100\nfunc use() { newAmount(\"usd\").sum(newAmount(\"rub\")) }\n")
	result := analyze(context.Background(), dir, nil)
	if diagnostics := result.diagnostics[path]; len(diagnostics) != 1 || diagnostics[0].Range.Start.Line != 2 {
		t.Fatalf("expected physical file/line despite //line directive: %+v", result)
	}
	writeFile(t, dir, "defs.go", strings.Replace(definitions, "equals c;", "equals unknown;", 1))
	result = analyze(context.Background(), dir, nil)
	found := false
	for _, d := range result.diagnostics[filepath.Join(dir, "defs.go")] {
		if strings.Contains(string(d.Message.(protocol.String)), "unknown") {
			found = true
		}
	}
	if !found {
		t.Fatalf("missing spec error: %+v", result)
	}
}

func TestAnalyzeAlias(t *testing.T) {
	dir := testModule(t)
	writeFile(t, dir, "defs.go", definitions)
	path := writeFile(t, dir, "alias.go", `package money
var kept *amount
func keep(a *amount) { kept = a }
func lost() {
	p := &amount{currency: "usd"}
	keep(p)
	_ = p.currency
}
`)
	got := analyze(context.Background(), dir, nil).diagnostics[path]
	if len(got) != 1 || !strings.Contains(string(got[0].Message.(protocol.String)), "cannot read p.currency: no access") {
		t.Fatalf("got %+v, want one access diagnostic", got)
	}
}

// Пакеты модуля видят спецификации друг друга; проверка каталога библиотеки
// перепроверяет и её импортёров, но не посторонние пакеты.
func TestAnalyzeCrossPackage(t *testing.T) {
	root := testModule(t)
	for _, d := range []string{"lib", "use", "other"} {
		if err := os.Mkdir(filepath.Join(root, d), 0700); err != nil {
			t.Fatal(err)
		}
	}
	lib := filepath.Join(root, "lib")
	writeFile(t, lib, "lib.go", `package lib
// @ bound <c string>;
type Amount struct {
 // @ equals c;
 Currency string
}
// @ returns Amount<c>;
func New(c string) Amount { return Amount{Currency: c} }
// @ requires a<c> == b<c>;
func Sum(a, b Amount) {}
`)
	use := writeFile(t, filepath.Join(root, "use"), "use.go", `package use
import "example.com/money/lib"
func f() { lib.Sum(lib.New("usd"), lib.New("rub")) }
`)
	other := writeFile(t, filepath.Join(root, "other"), "other.go", `package other
// @ bound <c string>;
type amount struct {
 // @ equals c;
 currency string
}
// @ requires a<c> == b<c>;
func sum(a, b amount) {}
func g() { sum(amount{currency: "usd"}, amount{currency: "rub"}) }
`)

	a := &analyzer{cache: newFactCache("")}
	for i, wantLib := range []bool{true, false} {
		result := a.analyze(context.Background(), filepath.Join(root, "use"), nil)
		if len(result.messages) != 0 || len(result.diagnostics[use]) != 1 {
			t.Fatalf("use: %+v", result)
		}
		// Повторно библиотека не проверяется: её факты в кэше.
		if got := slices.Contains(result.checked, "example.com/money/lib"); got != wantLib {
			t.Fatalf("run %d: lib checked from source: %v (%v)", i, got, result.checked)
		}
	}
	result := analyze(context.Background(), filepath.Join(root, "use"), nil)
	result = analyze(context.Background(), lib, nil)
	if len(result.messages) != 0 || len(result.diagnostics[use]) != 1 || len(result.diagnostics[other]) != 0 {
		t.Fatalf("lib should recheck its importers only: %+v", result)
	}
	if want := []string{lib, filepath.Join(root, "use")}; !slices.Equal(result.dirs, want) {
		t.Fatalf("dirs: got %v, want %v", result.dirs, want)
	}
	// Правка контракта библиотеки (несохранённая, через overlay) меняет
	// диагностики импортёра.
	overlay := map[string][]byte{filepath.Join(lib, "lib.go"): []byte("package lib\ntype Amount struct{ Currency string }\nfunc New(c string) Amount { return Amount{Currency: c} }\nfunc Sum(a, b Amount) {}\n")}
	result = analyze(context.Background(), lib, overlay)
	if len(result.messages) != 0 || len(result.diagnostics[use]) != 0 {
		t.Fatalf("contract removed: %+v", result)
	}
}

const libSource = `package lib
// @ bound <c string>;
type Amount struct {
 // @ equals c;
 Currency string
}
// @ returns Amount<c>;
func New(c string) Amount { return Amount{Currency: c} }
// @ requires a<c> == b<c>;
func Sum(a, b Amount) {}
`

const useSource = `package use
import "example.com/lib"
func f() { lib.Sum(lib.New("usd"), lib.New("rub")) }
`

func mkdir(t *testing.T, parts ...string) string {
	t.Helper()
	dir := filepath.Join(parts...)
	if err := os.MkdirAll(dir, 0700); err != nil {
		t.Fatal(err)
	}
	return dir
}

// Модуль вне workspace (replace на локальный каталог): его спецификации
// видны, после первой проверки — из кэша фактов, без проверки исходников.
func TestAnalyzeExternalModule(t *testing.T) {
	root := t.TempDir()
	lib := mkdir(t, root, "lib")
	writeFile(t, lib, "go.mod", "module example.com/lib\n\ngo 1.26.0\n")
	writeFile(t, lib, "lib.go", libSource)
	app := mkdir(t, root, "app")
	writeFile(t, app, "go.mod", "module example.com/app\n\ngo 1.26.0\n\nrequire example.com/lib v0.0.0\n\nreplace example.com/lib => ../lib\n")
	use := writeFile(t, app, "use.go", strings.Replace(useSource, "package use", "package app", 1))

	a := &analyzer{cache: newFactCache(t.TempDir())}
	check := func(wantDiags int, wantLib bool) {
		t.Helper()
		result := a.analyze(context.Background(), app, nil)
		if len(result.messages) != 0 || len(result.diagnostics[use]) != wantDiags {
			t.Fatalf("got %+v, want %d diagnostics", result, wantDiags)
		}
		if got := slices.Contains(result.checked, "example.com/lib"); got != wantLib {
			t.Fatalf("lib checked from source: %v, want %v (%v)", got, wantLib, result.checked)
		}
	}
	check(1, true)
	check(1, false)
	// Дисковый кэш переживает перезапуск сервера.
	a = &analyzer{cache: newFactCache(a.cache.dir)}
	check(1, false)
	// Изменение библиотеки меняет ключ: факты считаются заново.
	writeFile(t, lib, "lib.go", strings.Replace(libSource, "// @ requires a<c> == b<c>;\n", "", 1))
	check(0, true)
	// Ключ — по содержимому: прежний текст снова берётся из кэша.
	writeFile(t, lib, "lib.go", libSource)
	check(1, false)
	// Испорченный кэш выбрасывается, проверка повторяется из исходников.
	entries, err := os.ReadDir(a.cache.dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, e := range entries {
		writeFile(t, a.cache.dir, e.Name(), "garbage")
	}
	a = &analyzer{cache: newFactCache(a.cache.dir)}
	check(1, true)
}

// go.work: проверка библиотеки перепроверяет импортёров в соседнем модуле.
func TestAnalyzeWorkspace(t *testing.T) {
	root := t.TempDir()
	lib := mkdir(t, root, "lib")
	writeFile(t, lib, "go.mod", "module example.com/lib\n\ngo 1.26.0\n")
	writeFile(t, lib, "lib.go", libSource)
	app := mkdir(t, root, "app")
	writeFile(t, app, "go.mod", "module example.com/app\n\ngo 1.26.0\n\nrequire example.com/lib v0.0.0\n")
	use := writeFile(t, app, "use.go", strings.Replace(useSource, "package use", "package app", 1))
	writeFile(t, root, "go.work", "go 1.26.0\n\nuse (\n\t./app\n\t./lib\n)\n")

	a := &analyzer{cache: newFactCache("")}
	result := a.analyze(context.Background(), lib, nil)
	if len(result.messages) != 0 || len(result.diagnostics[use]) != 1 || !slices.Contains(result.dirs, app) {
		t.Fatalf("lib should recheck app: %+v", result)
	}
}

// Пакет в testdata (его не включает шаблон work) проверяется, даже если
// в модуле есть другие пакеты.
func TestAnalyzeTestdata(t *testing.T) {
	root := testModule(t)
	writeFile(t, root, "root.go", "package money\n")
	dir := mkdir(t, root, "testdata", "p")
	call := writeFile(t, dir, "p.go", definitions+badCall[len("package money"):])
	result := analyze(context.Background(), dir, nil)
	if len(result.messages) != 0 || len(result.diagnostics[call]) != 1 {
		t.Fatalf("testdata package: %+v", result)
	}
}

// Длинная цепочка зависимостей со спецификациями при холодном кэше
// обрабатывается до конца: контракт доходит до потребителя с первого раза.
func TestAnalyzeDeepChain(t *testing.T) {
	root := testModule(t)
	writeFile(t, mkdir(t, root, "lib"), "lib.go", `package lib
// @ bound <k string>;
type Box struct {
 // @ equals k;
 K string
}
// @ requires a<k> == b<k>;
func Same(a, b Box) {}
`)
	const depth = 25
	prev := ""
	for i := range depth {
		name := fmt.Sprintf("p%d", i)
		body := `lib.Box{K: k}`
		imports := `import "example.com/money/lib"`
		if prev != "" {
			body = prev + `.Make(k)`
			imports += "\nimport \"example.com/money/" + prev + "\""
		}
		writeFile(t, mkdir(t, root, name), name+".go", fmt.Sprintf("package %s\n%s\n// @ returns lib.Box<k>;\nfunc Make(k string) lib.Box { return %s }\n", name, imports, body))
		prev = name
	}
	app := mkdir(t, root, "app")
	use := writeFile(t, app, "app.go", fmt.Sprintf("package app\nimport \"example.com/money/lib\"\nimport \"example.com/money/%s\"\nfunc f() { lib.Same(%s.Make(\"a\"), %s.Make(\"b\")) }\n", prev, prev, prev))
	a := &analyzer{cache: newFactCache("")}
	result := a.analyze(context.Background(), app, nil)
	if len(result.messages) != 0 || len(result.diagnostics[use]) != 1 {
		t.Fatalf("deep chain: %+v", result)
	}
}

// Ключ кэша учитывает API импорта без спецификаций: константа из него
// в контракте библиотеки меняется — факты библиотеки считаются заново.
func TestAnalyzeCachePlainDependency(t *testing.T) {
	root := t.TempDir()
	plain := mkdir(t, root, "plain")
	writeFile(t, plain, "go.mod", "module example.com/plain\n\ngo 1.26.0\n")
	writeFile(t, plain, "plain.go", "package plain\nconst Currency = \"usd\"\n")
	lib := mkdir(t, root, "lib")
	writeFile(t, lib, "go.mod", "module example.com/lib\n\ngo 1.26.0\n\nrequire example.com/plain v0.0.0\n\nreplace example.com/plain => ../plain\n")
	writeFile(t, lib, "lib.go", `package lib
import "example.com/plain"
// @ bound <c string>;
type Amount struct {
 // @ equals c;
 Currency string
}
// @ returns Amount<plain.Currency>;
func Default() Amount { return Amount{Currency: plain.Currency} }
// @ requires a<c> == b<c>;
func Sum(a, b Amount) {}
`)
	app := mkdir(t, root, "app")
	writeFile(t, app, "go.mod", "module example.com/app\n\ngo 1.26.0\n\nrequire (\n\texample.com/lib v0.0.0\n\texample.com/plain v0.0.0\n)\n\nreplace example.com/lib => ../lib\n\nreplace example.com/plain => ../plain\n")
	use := writeFile(t, app, "app.go", "package app\nimport \"example.com/lib\"\nfunc f() { lib.Sum(lib.Default(), lib.Amount{Currency: \"usd\"}) }\n")

	a := &analyzer{cache: newFactCache("")}
	if result := a.analyze(context.Background(), app, nil); len(result.messages) != 0 || len(result.diagnostics[use]) != 0 {
		t.Fatalf("usd: %+v", result)
	}
	writeFile(t, plain, "plain.go", "package plain\nconst Currency = \"rub\"\n")
	if result := a.analyze(context.Background(), app, nil); len(result.messages) != 0 || len(result.diagnostics[use]) != 1 {
		t.Fatalf("rub: stale facts of lib: %+v", result)
	}
}

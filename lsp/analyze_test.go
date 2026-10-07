package lsp

import (
	"context"
	"os"
	"path/filepath"
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

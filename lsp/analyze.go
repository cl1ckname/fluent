package lsp

import (
	"context"
	"fmt"
	"go/ast"
	"go/parser"
	"go/scanner"
	"go/token"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"
	"unicode/utf8"

	"fluent/checker"

	"go.lsp.dev/protocol"
	"golang.org/x/tools/go/packages"
)

type analysisResult struct {
	diagnostics map[string][]protocol.Diagnostic
	messages    []string
}

func analyze(ctx context.Context, dir string, overlay map[string][]byte) analysisResult {
	result := analysisResult{diagnostics: make(map[string][]protocol.Diagnostic)}
	// Сохраняем именно текст, разобранный packages: при преобразовании позиций
	// содержимое файлов на диске уже могло измениться.
	sources := make(map[string][]byte)
	var sourceMu sync.Mutex
	pkgs, err := packages.Load(&packages.Config{
		Context: ctx, Dir: dir, Mode: packages.LoadSyntax, Tests: true, Overlay: overlay,
		ParseFile: func(fset *token.FileSet, filename string, src []byte) (*ast.File, error) {
			if src == nil {
				var err error
				src, err = os.ReadFile(filename)
				if err != nil {
					return nil, err
				}
			}
			sourceMu.Lock()
			sources[filepath.Clean(filename)] = src
			sourceMu.Unlock()
			return parser.ParseFile(fset, filename, src, parser.ParseComments|parser.AllErrors)
		},
	}, ".")
	if ctx.Err() != nil {
		return result
	}
	if err != nil {
		result.messages = append(result.messages, fmt.Sprintf("fluent: skipping %s: %v", dir, err))
		return result
	}
	seen := make(map[string]bool)
	for _, pkg := range pkgs {
		if ctx.Err() != nil {
			return result
		}
		if strings.HasSuffix(pkg.ID, ".test") && pkg.Name == "main" {
			continue
		}
		if pkg.IllTyped || len(pkg.Errors) != 0 || pkg.Types == nil || pkg.TypesInfo == nil {
			reason := "package or dependency contains Go errors"
			if len(pkg.Errors) != 0 {
				reason = pkg.Errors[0].Error()
			}
			result.messages = append(result.messages, fmt.Sprintf("fluent: skipping %s: %s", pkg.ID, reason))
			continue
		}
		checker.Check(&checker.Package{Fset: pkg.Fset, Files: pkg.Syntax, Types: pkg.Types, Info: pkg.TypesInfo}, func(d checker.Diagnostic) {
			position := pkg.Fset.PositionFor(d.Pos, false) // реальные позиции, без учёта //line
			path := filepath.Clean(position.Filename)
			src, ok := sources[path]
			if !ok || !position.IsValid() || position.Offset > len(src) {
				return
			}
			r := diagnosticRange(src, position.Offset)
			key := fmt.Sprintf("%s:%v:%s", path, r, d.Message)
			if seen[key] {
				return
			}
			seen[key] = true
			result.diagnostics[path] = append(result.diagnostics[path], protocol.Diagnostic{
				Range: r, Severity: protocol.DiagnosticSeverityError,
				Source: protocol.NewOptional("fluent"), Message: protocol.String(d.Message),
			})
		})
	}
	for _, diagnostics := range result.diagnostics {
		sort.Slice(diagnostics, func(i, j int) bool {
			a, b := diagnostics[i], diagnostics[j]
			if a.Range.Start.Line != b.Range.Start.Line {
				return a.Range.Start.Line < b.Range.Start.Line
			}
			if a.Range.Start.Character != b.Range.Start.Character {
				return a.Range.Start.Character < b.Range.Start.Character
			}
			return string(a.Message.(protocol.String)) < string(b.Message.(protocol.String))
		})
	}
	return result
}

// diagnosticRange подчёркивает токен Go, если позиция указывает на его начало,
// или один символ Unicode, если позиция находится внутри комментария спецификации.
func diagnosticRange(src []byte, offset int) protocol.Range {
	offset = max(0, min(offset, len(src)))
	end := offset
	if offset < len(src) {
		_, width := utf8.DecodeRune(src[offset:])
		end += width
		fset := token.NewFileSet()
		file := fset.AddFile("", -1, len(src))
		var scan scanner.Scanner
		scan.Init(file, src, nil, scanner.ScanComments)
		for {
			pos, tok, literal := scan.Scan()
			start := file.Offset(pos)
			if tok == token.EOF || start > offset {
				break
			}
			if start == offset && tok != token.COMMENT {
				if literal != "" && literal != "\n" {
					end = start + len(literal)
				} else if literal == "" {
					end = start + len(tok.String())
				}
				break
			}
		}
	}
	return protocol.Range{Start: position(src, offset), End: position(src, min(end, len(src)))}
}

func position(src []byte, offset int) protocol.Position {
	var p protocol.Position
	for _, r := range string(src[:offset]) {
		if r == '\n' {
			p.Line++
			p.Character = 0
		} else if r != '\r' {
			p.Character++
			if r > 0xffff {
				p.Character++
			}
		}
	}
	return p
}

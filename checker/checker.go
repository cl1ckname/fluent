// Package checker — ядро анализа. Не зависит от go/analysis, чтобы его можно было
// вызывать и из анализатора, и из LSP-сервера.
package checker

import (
	"go/ast"
	"go/token"
	"go/types"

	"fluent/bound"
)

// Diagnostic — сообщение о нарушении спецификации.
type Diagnostic struct {
	Pos     token.Pos
	Message string
}

// Package — входные данные для проверки одного пакета.
type Package struct {
	Fset  *token.FileSet
	Files []*ast.File
	Types *types.Package
	Info  *types.Info
}

// Check проверяет пакет и передаёт диагностики в report.
func Check(pkg *Package, report func(Diagnostic)) {
	specs := bound.Resolve(pkg.Files, pkg.Types, pkg.Info, func(pos token.Pos, msg string) {
		report(Diagnostic{Pos: pos, Message: msg})
	})
	_ = specs // TODO: распространение фактов по телам функций
}

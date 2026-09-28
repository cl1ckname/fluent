// Package analyzer — обёртка ядра checker в go/analysis.
package analyzer

import (
	"golang.org/x/tools/go/analysis"

	"fluent/checker"
)

var Analyzer = &analysis.Analyzer{
	Name: "fluent",
	Doc:  "checks equality constraints between bound fields of structs",
	Run:  run,
}

func run(pass *analysis.Pass) (any, error) {
	pkg := &checker.Package{
		Fset:  pass.Fset,
		Files: pass.Files,
		Types: pass.Pkg,
		Info:  pass.TypesInfo,
	}
	checker.Check(pkg, func(d checker.Diagnostic) {
		pass.Reportf(d.Pos, "%s", d.Message)
	})
	return nil, nil
}

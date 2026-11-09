// Package analyzer — обёртка ядра checker в go/analysis.
package analyzer

import (
	"go/types"

	"golang.org/x/tools/go/analysis"

	"fluent/checker"
)

var Analyzer = &analysis.Analyzer{
	Name:      "fluent",
	Doc:       "checks equality constraints between bound fields of structs",
	Run:       run,
	FactTypes: []analysis.Fact{new(packageFact)},
}

// packageFact — экспорты пакета (спецификации и сводки) для импортёров.
type packageFact struct {
	Data []byte
	Desc string
}

func (*packageFact) AFact() {}

func (f *packageFact) String() string { return f.Desc }

func run(pass *analysis.Pass) (any, error) {
	var encoded []checker.EncodedPackage
	for _, pf := range pass.AllPackageFacts() {
		if f, ok := pf.Fact.(*packageFact); ok && pf.Package != pass.Pkg {
			encoded = append(encoded, checker.EncodedPackage{Pkg: pf.Package, Data: f.Data})
		}
	}
	imports, specErrors, err := checker.Decode(encoded, packageLookup(pass.Pkg))
	if err != nil {
		return nil, err
	}
	bad := map[string]bool{}
	for _, p := range specErrors {
		bad[p.Path()] = true
	}
	for _, d := range checker.SpecErrorImports(pass.Files, bad) {
		pass.Reportf(d.Pos, "%s", d.Message)
	}

	pkg := &checker.Package{
		Fset:    pass.Fset,
		Files:   pass.Files,
		Types:   pass.Pkg,
		Info:    pass.TypesInfo,
		Imports: imports,
	}
	exp := checker.Check(pkg, func(d checker.Diagnostic) {
		pass.Reportf(d.Pos, "%s", d.Message)
	})
	if exp == nil {
		return nil, nil
	}
	data, err := exp.Encode(pass.Pkg)
	if err != nil {
		return nil, err
	}
	pass.ExportPackageFact(&packageFact{Data: data, Desc: exp.Describe(pass.Pkg)})
	return nil, nil
}

// packageLookup находит пакет по пути среди транзитивных импортов pkg.
func packageLookup(pkg *types.Package) func(string) *types.Package {
	var all map[string]*types.Package
	return func(path string) *types.Package {
		if all == nil {
			all = map[string]*types.Package{}
			var walk func(*types.Package)
			walk = func(p *types.Package) {
				if all[p.Path()] != nil {
					return
				}
				all[p.Path()] = p
				for _, q := range p.Imports() {
					walk(q)
				}
			}
			walk(pkg)
		}
		return all[path]
	}
}

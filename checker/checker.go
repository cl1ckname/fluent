// Package checker — ядро анализа. Не зависит от go/analysis, чтобы его можно было
// вызывать и из анализатора, и из LSP-сервера.
package checker

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"maps"
	"path/filepath"
	"slices"
	"strconv"

	"fluent/bound"
	"fluent/spec"
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

	Imports *Exports // спецификации и сводки зависимостей; nil — нет

	// GoErrors — ошибки Go в пакете или его зависимостях (разбора, типов,
	// импорта); позиция может быть token.NoPos. Непустой список включает
	// проверку по частям: функции и инициализаторы, которых касаются
	// ошибки, пропускаются (broken.go).
	GoErrors []Diagnostic
}

// Exports — то, что пакет даёт импортёрам: спецификации и сводки функций,
// свои и всех зависимостей.
type Exports struct {
	Specs     *bound.Info
	summaries map[*types.Func]*summary
	// unproven — функции с контрактом, тело которых не прошло проверку:
	// первая диагностика в теле, «файл:строка: сообщение».
	unproven map[*types.Func]string

	// SpecErrors — в спецификациях самого пакета есть ошибки, а часть
	// спецификаций разобрана: ошибочные инструкции отброшены, контракты могут
	// быть неполными. Пакет, где не разобрано ничего, не помечается: в чужом
	// коде `// @` бывает и обычным комментарием (`// @since 3.16`).
	SpecErrors bool
}

// MergeExports объединяет экспорты нескольких пакетов (например, всех
// импортов). Пакеты должны разделять объекты go/types.
func MergeExports(list ...*Exports) *Exports {
	out := &Exports{Specs: &bound.Info{Structs: map[*types.TypeName]*bound.Struct{}, Funcs: map[*types.Func]*bound.Func{}}, summaries: map[*types.Func]*summary{}, unproven: map[*types.Func]string{}}
	for _, e := range list {
		if e == nil {
			continue
		}
		maps.Copy(out.Specs.Structs, e.Specs.Structs)
		maps.Copy(out.Specs.Funcs, e.Specs.Funcs)
		maps.Copy(out.summaries, e.summaries)
		maps.Copy(out.unproven, e.unproven)
	}
	return out
}

// Check проверяет пакет, передаёт диагностики в report и возвращает экспорты
// пакета для импортёров.
//
// Пакету без спецификаций, который не видит bounded-типов, проверять нечего:
// tracked-память в него попадает только через any или интерфейс, а это
// неизвестный вызов. Для него Check сразу возвращает nil. Так дёшево проходят
// стандартная библиотека и зависимости без разметки.
func Check(pkg *Package, report func(Diagnostic)) *Exports {
	var imported *bound.Info
	if pkg.Imports != nil {
		imported = pkg.Imports.Specs
	}
	if (imported == nil || len(imported.Structs) == 0) && !hasSpecs(pkg.Files) {
		return nil
	}
	c := &checker{pkg: pkg, info: pkg.Info, unproven: map[*types.Func]string{}}
	if pkg.Imports != nil {
		maps.Copy(c.unproven, pkg.Imports.unproven)
	}
	c.report = func(d Diagnostic) {
		if c.firstDiag == "" {
			p := pkg.Fset.Position(d.Pos)
			c.firstDiag = fmt.Sprintf("%s:%d: %s", filepath.Base(p.Filename), p.Line, d.Message)
		}
		report(d)
	}
	exp := &Exports{unproven: maps.Clone(c.unproven)}
	specErrors := false
	muted := c.mutedSpecs()
	c.specs = bound.Resolve(pkg.Files, pkg.Types, bound.InfoObjects(pkg.Info), imported, func(pos token.Pos, msg string) {
		if inSpans(muted, pos) {
			return // следствие ошибки Go
		}
		specErrors = true
		report(Diagnostic{Pos: pos, Message: msg})
	})
	exp.SpecErrors = specErrors && c.specs.Declares(pkg.Types)
	var funcs []funcDecl
	for _, f := range pkg.Files {
		for _, d := range f.Decls {
			fd, ok := d.(*ast.FuncDecl)
			if !ok || fd.Body == nil {
				continue
			}
			obj, _ := c.info.Defs[fd.Name].(*types.Func)
			switch {
			case obj == nil:
			case c.broken(fd):
				// Контракт без проверенного тела импортёры получают с пометкой.
				if c.specs.Funcs[obj] != nil {
					exp.unproven[obj] = c.goErrorNote(fd.Pos())
				}
			default:
				funcs = append(funcs, funcDecl{obj, fd})
			}
		}
	}
	// Сначала сводки (молча), затем проверка тел с готовыми сводками.
	c.summarize(funcs)
	for _, f := range funcs {
		c.firstDiag = ""
		c.checkFunc(f.obj.Type().(*types.Signature), f.decl.Body, c.specs.Funcs[f.obj])
		// Контракт, тело которого не прошло проверку, импортёры получают
		// с пометкой: доверять ему можно только с предупреждением.
		if c.firstDiag != "" && c.specs.Funcs[f.obj] != nil {
			exp.unproven[f.obj] = c.firstDiag
		}
	}

	c.checkVarInits()

	exp.Specs = c.specs
	for _, d := range exportProblems(c.specs, pkg.Types) {
		if inSpans(muted, d.Pos) {
			continue
		}
		exp.SpecErrors = true
		report(d)
	}
	exp.summaries = maps.Clone(c.summaries)
	for _, f := range funcs {
		exp.summaries[f.obj] = exportSummary(c.summaries[f.obj], filepath.Base(pkg.Fset.Position(f.decl.Pos()).Filename))
	}
	return exp
}

// checkVarInits проверяет инициализаторы пакетных переменных как тела без
// параметров: вызовы в них подчиняются requires, литералы — инвариантам,
// замыкания проверяются как отдельные функции. Значения уходят в глобальные
// переменные, то есть в неизвестную память.
func (c *checker) checkVarInits() {
	empty := types.NewSignatureType(nil, nil, nil, nil, nil, false)
	for _, f := range c.pkg.Files {
		for _, d := range f.Decls {
			gd, ok := d.(*ast.GenDecl)
			if !ok || gd.Tok != token.VAR {
				continue
			}
			for _, sp := range gd.Specs {
				vs := sp.(*ast.ValueSpec)
				if len(vs.Values) == 0 || c.broken(vs) {
					continue
				}
				lhs := make([]ast.Expr, len(vs.Names))
				for i, n := range vs.Names {
					lhs[i] = n
				}
				body := &ast.BlockStmt{
					Lbrace: vs.Pos(), Rbrace: vs.End(),
					List: []ast.Stmt{&ast.AssignStmt{Lhs: lhs, TokPos: vs.Pos(), Tok: token.ASSIGN, Rhs: vs.Values}},
				}
				c.checkFunc(empty, body, nil)
			}
		}
	}
}

// SpecErrorImports — предупреждения на импортах пакетов (по пути), в
// спецификациях которых были ошибки: их контракты могут быть неполными.
func SpecErrorImports(files []*ast.File, bad map[string]bool) []Diagnostic {
	var out []Diagnostic
	for _, f := range files {
		for _, is := range f.Imports {
			if path, err := strconv.Unquote(is.Path.Value); err == nil && bad[path] {
				out = append(out, Diagnostic{Pos: is.Pos(), Message: fmt.Sprintf("package %s has errors in fluent specifications; some of its contracts are ignored", path)})
			}
		}
	}
	return out
}

// hasSpecs — есть ли в файлах спецификационные комментарии.
func hasSpecs(files []*ast.File) bool {
	for _, f := range files {
		for _, cg := range f.Comments {
			if len(spec.Extract(cg)) > 0 {
				return true
			}
		}
	}
	return false
}

// exportSummary — сводка для других пакетов: в причинах удержания номера
// строк относятся к файлу file, его имя добавляется.
func exportSummary(s *summary, file string) *summary {
	out := &summary{params: slices.Clone(s.params), results: s.results}
	for i := range out.params {
		if out.params[i].kept != "" {
			out.params[i].kept = file + ": " + out.params[i].kept
		}
	}
	return out
}

// funcName — имя функции в сообщениях; функция другого пакета — с именем пакета.
func (c *checker) funcName(fn *types.Func) string {
	if fn.Pkg() != nil && fn.Pkg() != c.pkg.Types && fn.Type().(*types.Signature).Recv() == nil {
		return fmt.Sprintf("%s.%s", fn.Pkg().Name(), fn.Name())
	}
	return fn.Name()
}

type checker struct {
	pkg       *Package
	info      *types.Info
	specs     *bound.Info
	report    func(Diagnostic)
	silent    int // > 0: пробный проход, диагностики не выдаются
	summaries map[*types.Func]*summary
	unproven  map[*types.Func]string // контракты других пакетов, не доказанные там
	firstDiag string                 // первая диагностика проверяемого тела
}

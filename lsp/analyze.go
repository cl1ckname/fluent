package lsp

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/scanner"
	"go/token"
	"go/types"
	"maps"
	"os"
	"os/exec"
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
	// dirs — каталоги, диагностики которых посчитаны заново: каталог запроса
	// и каталоги пакетов workspace, которые его импортируют.
	dirs []string
	// checked — пакеты, проверенные из исходников (ID), для тестов.
	checked []string
}

// analyzer — проверка пакетов для LSP с кэшем фактов между запусками.
type analyzer struct {
	cache *factCache
}

var (
	defaultOnce     sync.Once
	defaultAnalyzer *analyzer
)

// analyze проверяет каталог анализатором по умолчанию (дисковый кэш
// в пользовательском каталоге кэша).
func analyze(ctx context.Context, dir string, overlay map[string][]byte) analysisResult {
	defaultOnce.Do(func() { defaultAnalyzer = &analyzer{cache: newFactCache(defaultCacheDir())} })
	return defaultAnalyzer.analyze(ctx, dir, overlay)
}

// Видит ли пакет bounded-структуры (свои или зависимостей).
const (
	seesNo = iota
	seesYes
	seesUnknown // факты ещё не посчитаны
)

// pkgState — пакет в графе метаданных.
type pkgState struct {
	pkg   *packages.Package
	check bool   // пакет нужно проверять: свои спецификации или импорт видит структуры
	api   string // отпечаток пакета для импортёров
	key   string // ключ кэша фактов (у проверяемых)
	sees  int
	ready bool // факты не посчитаны, но все импорты известны: можно считать
}

// analyze проверяет пакеты каталога dir и пакеты workspace, которые от них
// зависят, по схеме go vet: из исходников проверяются только они, а
// спецификации и сводки зависимостей берутся из кэша фактов. Зависимости
// без фактов в кэше сначала проверяются из исходников снизу вверх (волнами).
func (a *analyzer) analyze(ctx context.Context, dir string, overlay map[string][]byte) analysisResult {
	result, retry := a.run(ctx, dir, overlay)
	if retry {
		result, _ = a.run(ctx, dir, overlay)
	}
	return result
}

func (a *analyzer) run(ctx context.Context, dir string, overlay map[string][]byte) (analysisResult, bool) {
	result := emptyResult()
	skip := func(err error) (analysisResult, bool) {
		if ctx.Err() != nil {
			return emptyResult(), false
		}
		result.messages = append(result.messages, fmt.Sprintf("fluent: skipping %s: %v", dir, err))
		return result, false
	}
	env, err := goEnv(ctx, dir)
	if err != nil {
		return skip(err)
	}

	// 1. Граф без проверки типов: пакеты workspace (вне модуля — каталога)
	// и все их зависимости.
	metaConfig := &packages.Config{
		Context: ctx, Dir: dir, Tests: true, Overlay: overlay,
		Mode: packages.NeedName | packages.NeedFiles | packages.NeedCompiledGoFiles | packages.NeedImports | packages.NeedDeps | packages.NeedModule,
	}
	// `.` — на случай каталога, который `work` не включает (testdata, _x, .x).
	roots, err := packages.Load(metaConfig, "work", ".")
	if err != nil || len(roots) == 0 {
		roots, err = packages.Load(metaConfig, ".")
	}
	if err != nil {
		return skip(err)
	}

	// 2. Что перепроверить: пакеты каталога и их импортёры в workspace.
	covered := map[string]bool{}
	var mark func(*packages.Package) bool
	mark = func(p *packages.Package) bool {
		if v, ok := covered[p.ID]; ok {
			return v
		}
		covered[p.ID] = packageDir(p) == dir
		for _, imp := range p.Imports {
			if mark(imp) {
				covered[p.ID] = true
			}
		}
		return covered[p.ID]
	}
	dirs := map[string]bool{dir: true}
	var targets []*packages.Package
	for _, p := range roots {
		if mark(p) && !isTestMain(p) {
			dirs[packageDir(p)] = true
			targets = append(targets, p)
		}
	}
	for d := range dirs {
		result.dirs = append(result.dirs, d)
	}
	sort.Strings(result.dirs)
	if len(targets) == 0 {
		return result, false
	}

	// 3. Факты зависимостей, которых нет в кэше: волнами снизу вверх. Волна —
	// пакеты, у которых все импорты уже известны. Пакет, где `// @` оказался
	// обычным комментарием, структур не видит, и его импортёры отсекаются.
	// Каждая волна записывает факты хотя бы одного пакета, иначе цикл
	// заканчивается: граф конечен.
	var states map[string]*pkgState
	for {
		states = map[string]*pkgState{}
		var frontier []string
		for _, p := range targets {
			for _, imp := range p.Imports {
				a.state(imp, states, env, overlay)
			}
		}
		for id, st := range states {
			if st.ready && !covered[id] && st.pkg.ID == st.pkg.PkgPath {
				frontier = append(frontier, st.pkg.PkgPath)
			}
		}
		if len(frontier) == 0 {
			break
		}
		sort.Strings(frontier)
		progress, retry, err := a.check(ctx, dir, overlay, frontier, states, nil, &result)
		if err != nil || retry {
			if err != nil {
				return skip(err)
			}
			return result, true
		}
		if !progress {
			break // зависимости с ошибками Go: факты недоступны
		}
	}
	var missing []string
	for id, st := range states {
		if st.sees == seesUnknown && !covered[id] && st.pkg.ID == st.pkg.PkgPath {
			missing = append(missing, st.pkg.PkgPath)
		}
	}
	if len(missing) > 0 {
		sort.Strings(missing)
		result.messages = append(result.messages, fmt.Sprintf("fluent: specifications of %s are unavailable (Go errors?); the check is incomplete", strings.Join(missing, ", ")))
	}

	// 4. Перепроверяемые пакеты — из исходников, с диагностиками.
	var patterns []string
	seenPath := map[string]bool{}
	for _, p := range targets {
		if !seenPath[p.PkgPath] {
			seenPath[p.PkgPath] = true
			patterns = append(patterns, p.PkgPath)
		}
	}
	sort.Strings(patterns)
	_, retry, err := a.check(ctx, dir, overlay, patterns, states, covered, &result)
	if err != nil {
		return skip(err)
	}
	if retry {
		return result, true
	}
	if ctx.Err() != nil {
		return emptyResult(), false
	}
	sort.Strings(result.checked)
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
	return result, false
}

// state вычисляет состояние пакета p и его зависимостей.
//
// api — отпечаток пакета: от него зависят типы и константы, которые видят
// импортёры. У стандартной библиотеки это версия Go, у модульного кэша —
// пути файлов (в них версия модуля), у остальных — содержимое файлов;
// всегда вместе с отпечатками импортов, транзитивно. Ключ фактов —
// отпечаток пакета, версия fluent и окружение go.
func (a *analyzer) state(p *packages.Package, states map[string]*pkgState, env goEnvironment, overlay map[string][]byte) *pkgState {
	if st := states[p.ID]; st != nil {
		return st
	}
	st := &pkgState{pkg: p, sees: seesNo}
	states[p.ID] = st
	std := isStandard(p, env.GOROOT)
	h := sha256.New()
	fmt.Fprintf(h, "pkg %s %s\n", p.ID, p.PkgPath)
	paths := make([]string, 0, len(p.Imports))
	for path := range p.Imports {
		paths = append(paths, path)
	}
	sort.Strings(paths)
	unknown := false
	for _, path := range paths {
		im := a.state(p.Imports[path], states, env, overlay)
		switch im.sees {
		case seesYes:
			st.check = true
		case seesUnknown:
			unknown = true
		}
		fmt.Fprintf(h, "import %s %s\n", path, im.api)
	}
	if std {
		fmt.Fprintf(h, "std %s %s\n", env.GOROOT, env.GOVERSION)
		st.api, st.check = hex.EncodeToString(h.Sum(nil)), false
		return st
	}
	for _, f := range p.CompiledGoFiles {
		fmt.Fprintf(h, "file %s %s\n", f, fileSum(f, overlay, env.GOMODCACHE))
	}
	st.api = hex.EncodeToString(h.Sum(nil))
	for _, f := range p.CompiledGoFiles {
		if a.cache.hasSpecs(f, overlay) {
			st.check = true
			break
		}
	}
	switch {
	case unknown:
		st.sees = seesUnknown // ни ключа, ни решения, пока не посчитаны импорты
		st.check = false
	case !st.check:
		st.sees = seesNo
	default:
		k := sha256.Sum256(fmt.Appendf(nil, "fluent %s\n%s %s %q %s\n%s", fluentVersion(), env.GOOS, env.GOARCH, env.GOFLAGS, os.Getenv("CGO_ENABLED"), st.api))
		st.key = hex.EncodeToString(k[:])
		if _, structs, ok := a.cache.facts(st.key); ok {
			st.sees = seesNo
			if structs {
				st.sees = seesYes
			}
		} else {
			st.sees, st.ready = seesUnknown, true
		}
	}
	return st
}

// check загружает пакеты patterns из исходников (зависимости — из export
// data, их факты — из кэша), проверяет их и кэширует факты. Диагностики
// и сообщения — только для пакетов из covered (nil — для волны). progress —
// факты хотя бы одного пакета записаны; retry — кэш испорчен и очищен.
func (a *analyzer) check(ctx context.Context, dir string, overlay map[string][]byte, patterns []string,
	states map[string]*pkgState, covered map[string]bool, result *analysisResult) (progress, retry bool, err error) {
	// Сохраняем именно текст, разобранный packages: при преобразовании позиций
	// содержимое файлов на диске уже могло измениться.
	sources := make(map[string][]byte)
	var sourceMu sync.Mutex
	pkgs, err := packages.Load(&packages.Config{
		Context: ctx, Dir: dir, Mode: packages.LoadSyntax, Tests: covered != nil, Overlay: overlay,
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
	}, patterns...)
	if err != nil {
		return false, false, err
	}
	loaded := make(map[*packages.Package]bool, len(pkgs))
	loadedPath := map[string]bool{}
	for _, p := range pkgs {
		loaded[p], loadedPath[p.PkgPath] = true, true
	}

	// Факты пакетов из export data — из кэша, в объектах этой загрузки.
	typesByPath := map[string]*types.Package{}
	var walk func(*types.Package)
	walk = func(p *types.Package) {
		if typesByPath[p.Path()] != nil {
			return
		}
		typesByPath[p.Path()] = p
		for _, q := range p.Imports() {
			walk(q)
		}
	}
	for _, p := range pkgs {
		if p.Types != nil {
			for _, q := range p.Types.Imports() {
				walk(q)
			}
		}
	}
	var encoded []checker.EncodedPackage
	var usedKeys []string
	for _, st := range states {
		tp := typesByPath[st.pkg.PkgPath]
		if st.key == "" || st.pkg.ID != st.pkg.PkgPath || tp == nil || loadedPath[st.pkg.PkgPath] {
			continue
		}
		if data, _, ok := a.cache.facts(st.key); ok && len(data) > 0 {
			encoded = append(encoded, checker.EncodedPackage{Pkg: tp, Data: data})
			usedKeys = append(usedKeys, st.key)
		}
	}
	base, badPkgs, err := checker.Decode(encoded, func(path string) *types.Package { return typesByPath[path] })
	if err != nil {
		a.cache.drop(usedKeys)
		return false, true, nil
	}
	bad := map[string]bool{}
	for _, p := range badPkgs {
		bad[p.Path()] = true
	}

	// Проверка: зависимости раньше импортёров.
	exports := make(map[*packages.Package]*checker.Exports)
	done := make(map[*packages.Package]bool)
	seen := make(map[string]bool)
	var visit func(*packages.Package)
	visit = func(pkg *packages.Package) {
		if done[pkg] || ctx.Err() != nil {
			return
		}
		done[pkg] = true
		imports := []*checker.Exports{base}
		importBad := maps.Clone(bad)
		for _, imp := range pkg.Imports {
			if !loaded[imp] {
				continue
			}
			visit(imp)
			if e := exports[imp]; e != nil {
				imports = append(imports, e)
				if e.SpecErrors {
					importBad[imp.PkgPath] = true
				}
			}
		}
		if isTestMain(pkg) {
			return
		}
		report := covered[pkg.ID]
		if pkg.IllTyped || len(pkg.Errors) != 0 || pkg.Types == nil || pkg.TypesInfo == nil {
			if report {
				reason := "package or dependency contains Go errors"
				if len(pkg.Errors) != 0 {
					reason = pkg.Errors[0].Error()
				}
				result.messages = append(result.messages, fmt.Sprintf("fluent: skipping %s: %s", pkg.ID, reason))
			}
			return
		}
		result.checked = append(result.checked, pkg.ID)
		add := func(d checker.Diagnostic) {
			if !report {
				return
			}
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
		}
		for _, d := range checker.SpecErrorImports(pkg.Syntax, importBad) {
			add(d)
		}
		exp := checker.Check(&checker.Package{
			Fset: pkg.Fset, Files: pkg.Syntax, Types: pkg.Types, Info: pkg.TypesInfo,
			Imports: checker.MergeExports(imports...),
		}, add)
		exports[pkg] = exp
		// Импортёрам нужны факты только основного варианта пакета, не
		// тестового; ключ есть у пакетов, посчитанных волной.
		if st := states[pkg.ID]; st != nil && st.ready && pkg.ID == pkg.PkgPath {
			var data []byte
			structs := false
			if exp != nil {
				var err error
				if data, err = exp.Encode(pkg.Types); err != nil {
					return
				}
				structs = len(exp.Specs.Structs) > 0
			}
			a.cache.store(st.key, data, structs)
			progress = true
		}
	}
	for _, pkg := range pkgs {
		visit(pkg)
	}
	return progress, false, nil
}

type goEnvironment struct {
	GOROOT, GOMODCACHE, GOOS, GOARCH, GOFLAGS, GOVERSION string
}

// goEnv — переменные go, от которых зависят ключи кэша.
func goEnv(ctx context.Context, dir string) (goEnvironment, error) {
	cmd := exec.CommandContext(ctx, "go", "env", "-json", "GOROOT", "GOMODCACHE", "GOOS", "GOARCH", "GOFLAGS", "GOVERSION")
	cmd.Dir = dir
	out, err := cmd.Output()
	if err != nil {
		return goEnvironment{}, fmt.Errorf("go env: %v", err)
	}
	var env goEnvironment
	if err := json.Unmarshal(out, &env); err != nil {
		return goEnvironment{}, fmt.Errorf("go env: %v", err)
	}
	return env, nil
}

// isStandard — пакет стандартной библиотеки: спецификаций fluent в нём нет.
func isStandard(p *packages.Package, goroot string) bool {
	if p.Module != nil || goroot == "" {
		return false
	}
	if p.PkgPath == "unsafe" || p.PkgPath == "C" {
		return true
	}
	src := filepath.Join(goroot, "src") + string(filepath.Separator)
	for _, f := range p.CompiledGoFiles {
		if !strings.HasPrefix(f, src) {
			return false
		}
	}
	return len(p.CompiledGoFiles) > 0
}

// fileSum — отпечаток файла для ключа: файлы модульного кэша неизменны
// (путь содержит версию), остальные хешируются по содержимому.
func fileSum(path string, overlay map[string][]byte, modcache string) string {
	if src, ok := overlay[path]; ok {
		sum := sha256.Sum256(src)
		return hex.EncodeToString(sum[:])
	}
	if modcache != "" && strings.HasPrefix(path, modcache+string(filepath.Separator)) {
		return "modcache"
	}
	src, err := os.ReadFile(path)
	if err != nil {
		return "missing"
	}
	sum := sha256.Sum256(src)
	return hex.EncodeToString(sum[:])
}

// packageDir — каталог файлов пакета.
func packageDir(pkg *packages.Package) string {
	for _, files := range [][]string{pkg.GoFiles, pkg.CompiledGoFiles, pkg.OtherFiles} {
		if len(files) > 0 {
			return filepath.Dir(filepath.Clean(files[0]))
		}
	}
	return ""
}

// isTestMain — сгенерированный main тестового бинарника.
func isTestMain(pkg *packages.Package) bool {
	return strings.HasSuffix(pkg.ID, ".test") && pkg.Name == "main"
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

package checker

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"go/constant"
	"go/token"
	"go/types"
	"sort"
	"strings"

	"golang.org/x/tools/go/types/objectpath"

	"fluent/bound"
)

// Сериализация экспортов пакета для других процессов (analysis.Fact).
// Объекты верхнего уровня, поля и типы задаются путём objectpath в своём
// пакете; переменные сигнатуры — позицией, индексные параметры — номером,
// константы — значением. Позиций в декодированных спецификациях нет.

type wireRef struct {
	Pkg  string
	Path string // "" — нет объекта (nil в пути сводки)
}

// wireType — comparable-тип индексного параметра или константы.
type wireType struct {
	Op       byte            // 0 — Basic или Named; 'u' встроенный именованный; 'p' указатель; 'a' массив; 'c' канал; 'i' пустой интерфейс
	Basic    types.BasicKind // != Invalid — базовый тип
	Named    wireRef
	Universe string // 'u': error, comparable
	Len      int64  // 'a'
	Dir      types.ChanDir
	Elem     *wireType // 'p', 'a', 'c'
}

type wireConst struct {
	Nil  bool
	Kind constant.Kind
	Val  string // ExactString; у complex — вещественная часть
	Imag string
	Type wireType
	Text string
}

type wireExpr struct {
	Op    byte // 'v' переменная, 'c' константа, 'f' поле, 'p' x<p>, 's' параметр своей структуры
	Index int  // 'v': >= 0 — параметр по позициям сводки, < 0 — результат -1-Index; 'p', 's': номер параметра
	Owner wireRef
	Field wireRef
	X     *wireExpr
	Const *wireConst
}

type wireEq struct{ Left, Right wireExpr }

type wireParam struct {
	Name string
	Type wireType
}

type wireField struct {
	Field  wireRef
	Equals int // номер параметра; -1 — close
	Close  []wireExpr
}

type wireStruct struct {
	Obj    wireRef
	Params []wireParam
	Fields []wireField
}

type wireResult struct {
	Args    []wireExpr
	HasArgs bool
}

type wireGuard struct {
	Index int
	Neq   bool
	Value wireConst
}

type wireEnsure struct {
	Guard *wireGuard
	Eqs   []wireEq
}

type wireFunc struct {
	Obj        wireRef
	Unproven   string // не "" — тело не прошло проверку: первая диагностика
	Requires   []wireEq
	HasReturns bool
	Returns    []wireResult
	Ensures    []wireEnsure
}

type wireParamSum struct {
	Access  access
	Kept    string
	OwnTo   int
	OwnPath []wireRef
	Wrote   bool
}

type wireResultSum struct {
	Fresh bool
	Alias int
	Slot  []wireRef
	Path  []wireRef
}

type wireSummary struct {
	Obj     wireRef
	Params  []wireParamSum
	Results []wireResultSum
}

type wirePackage struct {
	Structs    []wireStruct
	Funcs      []wireFunc
	Summaries  []wireSummary
	SpecErrors bool
}

// Encode сериализует спецификации и сводки, объявленные в пакете pkg.
// Объекты, для которых нет пути objectpath (например, объявленные внутри
// функций), пропускаются: другие пакеты не могут на них сослаться.
func (e *Exports) Encode(pkg *types.Package) ([]byte, error) {
	enc := &encoder{pkg: pkg, paths: map[*types.Package]*objectpath.Encoder{}}
	w := wirePackage{SpecErrors: e.SpecErrors}
	for obj, s := range e.Specs.Structs {
		if obj.Pkg() != pkg {
			continue
		}
		if ws, ok := enc.structSpec(s); ok {
			w.Structs = append(w.Structs, ws)
		}
	}
	for obj, f := range e.Specs.Funcs {
		if obj.Pkg() != pkg {
			continue
		}
		if wf, ok := enc.funcSpec(f); ok {
			wf.Unproven = e.unproven[obj]
			w.Funcs = append(w.Funcs, wf)
		}
	}
	for obj, s := range e.summaries {
		if obj.Pkg() != pkg {
			continue
		}
		if ws, ok := enc.summarySpec(obj, s); ok {
			w.Summaries = append(w.Summaries, ws)
		}
	}
	// Детерминированный порядок: факты кешируются по содержимому.
	sort.Slice(w.Structs, func(i, j int) bool { return w.Structs[i].Obj.Path < w.Structs[j].Obj.Path })
	sort.Slice(w.Funcs, func(i, j int) bool { return w.Funcs[i].Obj.Path < w.Funcs[j].Obj.Path })
	sort.Slice(w.Summaries, func(i, j int) bool { return w.Summaries[i].Obj.Path < w.Summaries[j].Obj.Path })
	var buf bytes.Buffer
	if err := gob.NewEncoder(&buf).Encode(&w); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

// exportProblems — спецификации пакета pkg, доступные другим пакетам, но
// не выразимые в факте (например, индекс generic-типа). Импортёр их не
// увидит, поэтому это диагностика, а не тихое ослабление проверки.
func exportProblems(specs *bound.Info, pkg *types.Package) []Diagnostic {
	enc := &encoder{pkg: pkg, paths: map[*types.Package]*objectpath.Encoder{}}
	var out []Diagnostic
	for obj, s := range specs.Structs {
		if obj.Pkg() != pkg {
			continue
		}
		if _, ok := enc.structSpec(s); !ok {
			out = append(out, Diagnostic{Pos: obj.Pos(), Message: fmt.Sprintf("specification of %s cannot be exported to other packages: unsupported type of a bound parameter", obj.Name())})
		}
	}
	for obj, f := range specs.Funcs {
		if obj.Pkg() != pkg {
			continue
		}
		if _, ok := enc.ref(obj); !ok {
			continue // неэкспортированная функция: снаружи её не вызвать
		}
		if _, ok := enc.funcSpec(f); !ok {
			out = append(out, Diagnostic{Pos: obj.Pos(), Message: fmt.Sprintf("contract of %s cannot be exported to other packages: unsupported type of a constant or bound parameter", funcKey(obj))})
		}
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Pos < out[j].Pos })
	return out
}

// Describe — краткое описание экспортов пакета pkg (для отладки и тестов):
// структуры со спецификациями, функции с контрактами, число сводок
// экспортированных функций и методов.
func (e *Exports) Describe(pkg *types.Package) string {
	var structs, funcs []string
	for obj := range e.Specs.Structs {
		if obj.Pkg() == pkg {
			structs = append(structs, obj.Name())
		}
	}
	for obj := range e.Specs.Funcs {
		if obj.Pkg() == pkg {
			funcs = append(funcs, funcKey(obj))
		}
	}
	n := 0
	for obj := range e.summaries {
		if obj.Pkg() == pkg && obj.Exported() {
			n++
		}
	}
	sort.Strings(structs)
	sort.Strings(funcs)
	s := fmt.Sprintf("structs [%s] contracts [%s] summaries %d", strings.Join(structs, " "), strings.Join(funcs, " "), n)
	if e.SpecErrors {
		s += " (spec errors)"
	}
	return s
}

func funcKey(fn *types.Func) string {
	if recv := fn.Type().(*types.Signature).Recv(); recv != nil {
		if n, ok := types.Unalias(derefType(recv.Type())).(*types.Named); ok {
			return n.Obj().Name() + "." + fn.Name()
		}
	}
	return fn.Name()
}

type encoder struct {
	pkg   *types.Package
	paths map[*types.Package]*objectpath.Encoder
}

func (enc *encoder) ref(obj types.Object) (wireRef, bool) {
	if obj == nil {
		return wireRef{}, true
	}
	if obj.Pkg() == nil {
		return wireRef{}, false
	}
	pe := enc.paths[obj.Pkg()]
	if pe == nil {
		pe = new(objectpath.Encoder)
		enc.paths[obj.Pkg()] = pe
	}
	p, err := pe.For(obj)
	if err != nil {
		return wireRef{}, false
	}
	return wireRef{Pkg: obj.Pkg().Path(), Path: string(p)}, true
}

func (enc *encoder) refs(vs []*types.Var) ([]wireRef, bool) {
	if vs == nil {
		return nil, true
	}
	out := make([]wireRef, len(vs))
	for i, v := range vs {
		var ok bool
		if v == nil {
			out[i] = wireRef{}
			continue
		}
		if out[i], ok = enc.ref(v); !ok {
			return nil, false
		}
	}
	return out, true
}

func (enc *encoder) typ(t types.Type) (wireType, bool) {
	elem := func(op byte, e types.Type) (wireType, bool) {
		w, ok := enc.typ(e)
		return wireType{Op: op, Elem: &w}, ok
	}
	switch t := types.Unalias(t).(type) {
	case *types.Basic:
		return wireType{Basic: t.Kind()}, true
	case *types.Named:
		if t.Obj().Pkg() == nil {
			return wireType{Op: 'u', Universe: t.Obj().Name()}, true
		}
		if t.TypeArgs().Len() > 0 {
			return wireType{}, false // инстанцирование generic-типа
		}
		r, ok := enc.ref(t.Obj())
		return wireType{Named: r}, ok
	case *types.Pointer:
		return elem('p', t.Elem())
	case *types.Array:
		w, ok := elem('a', t.Elem())
		w.Len = t.Len()
		return w, ok
	case *types.Chan:
		w, ok := elem('c', t.Elem())
		w.Dir = t.Dir()
		return w, ok
	case *types.Interface:
		if t.Empty() {
			return wireType{Op: 'i'}, true
		}
	}
	return wireType{}, false
}

func (enc *encoder) constant(c *bound.Const) (wireConst, bool) {
	t, ok := enc.typ(c.Typ)
	w := wireConst{Type: t, Text: c.Text}
	if c.Val == nil {
		w.Nil = true
		return w, ok
	}
	w.Kind = c.Val.Kind()
	if w.Kind == constant.Complex {
		w.Val, w.Imag = constant.Real(c.Val).ExactString(), constant.Imag(c.Val).ExactString()
	} else {
		w.Val = c.Val.ExactString()
	}
	return w, ok
}

// sigIndex — позиция переменной сигнатуры: параметр по позициям сводки или
// результат (-1-номер).
func sigIndex(sig *types.Signature, v *types.Var) (int, bool) {
	for i, p := range sigParams(sig) {
		if p == v {
			return i, true
		}
	}
	for i := range sig.Results().Len() {
		if sig.Results().At(i) == v {
			return -1 - i, true
		}
	}
	return 0, false
}

func (enc *encoder) expr(sig *types.Signature, e bound.Expr) (wireExpr, bool) {
	switch e := e.(type) {
	case *bound.Var:
		i, ok := sigIndex(sig, e.Obj)
		return wireExpr{Op: 'v', Index: i}, ok
	case *bound.Const:
		c, ok := enc.constant(e)
		return wireExpr{Op: 'c', Const: &c}, ok
	case *bound.FieldOf:
		x, ok := enc.expr(sig, e.X)
		f, fok := enc.ref(e.Field)
		return wireExpr{Op: 'f', X: &x, Field: f}, ok && fok
	case *bound.ParamOf:
		x, ok := enc.expr(sig, e.X)
		o, ook := enc.ref(e.Param.Owner)
		return wireExpr{Op: 'p', X: &x, Owner: o, Index: e.Param.Index}, ok && ook
	case *bound.SelfParam:
		o, ok := enc.ref(e.Param.Owner)
		return wireExpr{Op: 's', Owner: o, Index: e.Param.Index}, ok
	}
	return wireExpr{}, false
}

func (enc *encoder) exprs(sig *types.Signature, es []bound.Expr) ([]wireExpr, bool) {
	out := make([]wireExpr, len(es))
	for i, e := range es {
		var ok bool
		if out[i], ok = enc.expr(sig, e); !ok {
			return nil, false
		}
	}
	return out, true
}

func (enc *encoder) eqs(sig *types.Signature, eqs []bound.Equality) ([]wireEq, bool) {
	out := make([]wireEq, len(eqs))
	for i, eq := range eqs {
		l, lok := enc.expr(sig, eq.Left)
		r, rok := enc.expr(sig, eq.Right)
		if !lok || !rok {
			return nil, false
		}
		out[i] = wireEq{l, r}
	}
	return out, true
}

func (enc *encoder) structSpec(s *bound.Struct) (wireStruct, bool) {
	obj, ok := enc.ref(s.Obj)
	if !ok {
		return wireStruct{}, false
	}
	w := wireStruct{Obj: obj}
	for _, p := range s.Params {
		t, ok := enc.typ(p.Type)
		if !ok {
			return wireStruct{}, false
		}
		w.Params = append(w.Params, wireParam{Name: p.Name, Type: t})
	}
	for _, f := range s.Fields {
		fr, ok := enc.ref(f.Var)
		if !ok {
			return wireStruct{}, false
		}
		wf := wireField{Field: fr, Equals: -1}
		if f.Equals != nil {
			wf.Equals = f.Equals.Index
		} else if wf.Close, ok = enc.exprs(nil, f.Close); !ok {
			return wireStruct{}, false
		}
		w.Fields = append(w.Fields, wf)
	}
	return w, true
}

func (enc *encoder) funcSpec(f *bound.Func) (wireFunc, bool) {
	obj, ok := enc.ref(f.Obj)
	if !ok {
		return wireFunc{}, false
	}
	sig := f.Obj.Type().(*types.Signature)
	w := wireFunc{Obj: obj, HasReturns: f.Returns != nil}
	if w.Requires, ok = enc.eqs(sig, f.Requires); !ok {
		return wireFunc{}, false
	}
	for _, r := range f.Returns {
		wr := wireResult{HasArgs: r.Args != nil}
		if wr.Args, ok = enc.exprs(sig, r.Args); !ok {
			return wireFunc{}, false
		}
		w.Returns = append(w.Returns, wr)
	}
	for _, e := range f.Ensures {
		var we wireEnsure
		if g := e.Guard; g != nil {
			c, ok := enc.constant(g.Value)
			if !ok {
				return wireFunc{}, false
			}
			we.Guard = &wireGuard{Index: g.Index, Neq: g.Neq, Value: c}
		}
		if we.Eqs, ok = enc.eqs(sig, e.Eqs); !ok {
			return wireFunc{}, false
		}
		w.Ensures = append(w.Ensures, we)
	}
	return w, true
}

func (enc *encoder) summarySpec(fn *types.Func, s *summary) (wireSummary, bool) {
	obj, ok := enc.ref(fn)
	if !ok {
		return wireSummary{}, false
	}
	w := wireSummary{Obj: obj}
	for _, p := range s.params {
		path, ok := enc.refs(p.ownPath)
		if !ok {
			return wireSummary{}, false
		}
		w.Params = append(w.Params, wireParamSum{Access: p.access, Kept: p.kept, OwnTo: p.ownTo, OwnPath: path, Wrote: p.wrote})
	}
	for _, r := range s.results {
		slot, sok := enc.refs(r.slot)
		path, pok := enc.refs(r.path)
		if !sok || !pok {
			return wireSummary{}, false
		}
		w.Results = append(w.Results, wireResultSum{Fresh: r.fresh, Alias: r.alias, Slot: slot, Path: path})
	}
	return w, true
}

// ---- декодирование ----

// EncodedPackage — сериализованные экспорты пакета Pkg, каким его видит
// импортёр.
type EncodedPackage struct {
	Pkg  *types.Package
	Data []byte
}

// Decode восстанавливает экспорты зависимостей в объектах go/types
// импортёра. lookup находит пакет по пути (для типов и полей из пакетов без
// экспортов). Объекты, которых нет в данных импортёра (их нет в export
// data, потому что импортёр не может на них сослаться), пропускаются.
// specErrors — пакеты, в спецификациях которых были ошибки.
func Decode(pkgs []EncodedPackage, lookup func(path string) *types.Package) (exp *Exports, specErrors []*types.Package, err error) {
	d := &decoder{lookup: lookup, byPath: map[string]*types.Package{}}
	wires := make([]wirePackage, len(pkgs))
	for i, p := range pkgs {
		d.byPath[p.Pkg.Path()] = p.Pkg
		if err := gob.NewDecoder(bytes.NewReader(p.Data)).Decode(&wires[i]); err != nil {
			return nil, nil, fmt.Errorf("decoding fluent facts of %s: %v", p.Pkg.Path(), err)
		}
		if wires[i].SpecErrors {
			specErrors = append(specErrors, p.Pkg)
		}
	}
	exp = MergeExports()
	d.out = exp.Specs
	// Сначала параметры всех структур: на них ссылаются поля и контракты
	// других структур и пакетов.
	pending := map[*bound.Struct]wireStruct{}
	for _, w := range wires {
		for _, ws := range w.Structs {
			if s := d.structParams(ws); s != nil {
				pending[s] = ws
			}
		}
	}
	for s, ws := range pending {
		if !d.structFields(s, ws) {
			delete(d.out.Structs, s.Obj)
		}
	}
	for _, w := range wires {
		for _, wf := range w.Funcs {
			if f := d.funcSpec(wf); f != nil {
				d.out.Funcs[f.Obj] = f
				if wf.Unproven != "" {
					exp.unproven[f.Obj] = wf.Unproven
				}
			}
		}
		for _, ws := range w.Summaries {
			if fn, s := d.summary(ws); s != nil {
				exp.summaries[fn] = s
			}
		}
	}
	return exp, specErrors, nil
}

type decoder struct {
	lookup func(string) *types.Package
	byPath map[string]*types.Package
	out    *bound.Info
}

func (d *decoder) obj(r wireRef) types.Object {
	pkg := d.byPath[r.Pkg]
	if pkg == nil && d.lookup != nil {
		pkg = d.lookup(r.Pkg)
	}
	if pkg == nil {
		return nil
	}
	obj, err := objectpath.Object(pkg, objectpath.Path(r.Path))
	if err != nil {
		return nil
	}
	return obj
}

func (d *decoder) field(r wireRef) *types.Var {
	v, _ := d.obj(r).(*types.Var)
	return v
}

func (d *decoder) fields(rs []wireRef) ([]*types.Var, bool) {
	if rs == nil {
		return nil, true
	}
	out := make([]*types.Var, len(rs))
	for i, r := range rs {
		if r.Path == "" {
			continue
		}
		if out[i] = d.field(r); out[i] == nil {
			return nil, false
		}
	}
	return out, true
}

func (d *decoder) typ(w wireType) types.Type {
	var elem types.Type
	if w.Elem != nil {
		if elem = d.typ(*w.Elem); elem == nil {
			return nil
		}
	}
	switch w.Op {
	case 'u':
		if tn, ok := types.Universe.Lookup(w.Universe).(*types.TypeName); ok {
			return tn.Type()
		}
		return nil
	case 'p':
		return types.NewPointer(elem)
	case 'a':
		return types.NewArray(elem, w.Len)
	case 'c':
		return types.NewChan(w.Dir, elem)
	case 'i':
		return types.NewInterfaceType(nil, nil).Complete()
	}
	if w.Basic != types.Invalid {
		return types.Typ[w.Basic]
	}
	if tn, ok := d.obj(w.Named).(*types.TypeName); ok {
		return tn.Type()
	}
	return nil
}

func (d *decoder) constant(w wireConst) (*bound.Const, bool) {
	c := &bound.Const{Text: w.Text, At: token.NoPos}
	if w.Nil {
		c.Typ = types.Typ[types.UntypedNil]
		return c, true
	}
	switch w.Kind {
	case constant.Bool:
		c.Val = constant.MakeBool(w.Val == "true")
	case constant.String:
		c.Val = constant.MakeFromLiteral(w.Val, token.STRING, 0)
	case constant.Int:
		c.Val = signed(w.Val, func(s string) constant.Value { return constant.MakeFromLiteral(s, token.INT, 0) })
	case constant.Float:
		c.Val = ratOrFloat(w.Val)
	case constant.Complex:
		c.Val = constant.BinaryOp(ratOrFloat(w.Val), token.ADD, constant.MakeImag(ratOrFloat(w.Imag)))
	}
	if c.Val == nil || c.Val.Kind() == constant.Unknown {
		return nil, false
	}
	c.Typ = d.typ(w.Type)
	if c.Typ == nil {
		// Тип константы недоступен импортёру: значение важнее, тип — по виду.
		c.Typ = map[constant.Kind]types.Type{
			constant.Bool: types.Typ[types.UntypedBool], constant.String: types.Typ[types.UntypedString],
			constant.Int: types.Typ[types.UntypedInt], constant.Float: types.Typ[types.UntypedFloat],
			constant.Complex: types.Typ[types.UntypedComplex],
		}[w.Kind]
	}
	return c, true
}

// ratOrFloat разбирает ExactString вещественной константы: "a/b" или литерал.
func ratOrFloat(s string) constant.Value {
	return signed(s, func(s string) constant.Value {
		if num, den, ok := strings.Cut(s, "/"); ok {
			return constant.BinaryOp(constant.MakeFromLiteral(num, token.INT, 0), token.QUO, constant.MakeFromLiteral(den, token.INT, 0))
		}
		return constant.ToFloat(constant.MakeFromLiteral(s, token.FLOAT, 0))
	})
}

// signed разбирает число со знаком: литералы Go знака не содержат.
func signed(s string, parse func(string) constant.Value) constant.Value {
	if rest, ok := strings.CutPrefix(s, "-"); ok {
		return constant.UnaryOp(token.SUB, parse(rest), 0)
	}
	return parse(s)
}

func (d *decoder) param(owner wireRef, i int) *bound.Param {
	tn, _ := d.obj(owner).(*types.TypeName)
	if tn == nil {
		return nil
	}
	s := d.out.Structs[tn]
	if s == nil || i < 0 || i >= len(s.Params) {
		return nil
	}
	return s.Params[i]
}

func (d *decoder) expr(sig *types.Signature, w wireExpr) bound.Expr {
	switch w.Op {
	case 'v':
		if sig == nil {
			return nil
		}
		if w.Index >= 0 {
			ps := sigParams(sig)
			if w.Index < len(ps) {
				return &bound.Var{Obj: ps[w.Index]}
			}
		} else if i := -1 - w.Index; i < sig.Results().Len() {
			return &bound.Var{Obj: sig.Results().At(i)}
		}
	case 'c':
		if w.Const != nil {
			if c, ok := d.constant(*w.Const); ok {
				return c
			}
		}
	case 'f':
		if f := d.field(w.Field); f != nil && w.X != nil {
			if x := d.expr(sig, *w.X); x != nil {
				return &bound.FieldOf{X: x, Field: f}
			}
		}
	case 'p':
		if p := d.param(w.Owner, w.Index); p != nil && w.X != nil {
			if x := d.expr(sig, *w.X); x != nil {
				return &bound.ParamOf{X: x, Param: p}
			}
		}
	case 's':
		if p := d.param(w.Owner, w.Index); p != nil {
			return &bound.SelfParam{Param: p}
		}
	}
	return nil
}

func (d *decoder) exprs(sig *types.Signature, ws []wireExpr) ([]bound.Expr, bool) {
	out := make([]bound.Expr, len(ws))
	for i, w := range ws {
		if out[i] = d.expr(sig, w); out[i] == nil {
			return nil, false
		}
	}
	return out, true
}

func (d *decoder) eqs(sig *types.Signature, ws []wireEq) ([]bound.Equality, bool) {
	var out []bound.Equality
	for _, w := range ws {
		l, r := d.expr(sig, w.Left), d.expr(sig, w.Right)
		if l == nil || r == nil {
			return nil, false
		}
		out = append(out, bound.Equality{Left: l, Right: r})
	}
	return out, true
}

func (d *decoder) structParams(w wireStruct) *bound.Struct {
	tn, _ := d.obj(w.Obj).(*types.TypeName)
	if tn == nil {
		return nil
	}
	s := &bound.Struct{Obj: tn}
	for i, wp := range w.Params {
		t := d.typ(wp.Type)
		if t == nil {
			return nil
		}
		s.Params = append(s.Params, &bound.Param{Owner: tn, Index: i, Name: wp.Name, Type: t})
	}
	d.out.Structs[tn] = s
	return s
}

func (d *decoder) structFields(s *bound.Struct, w wireStruct) bool {
	for _, wf := range w.Fields {
		v := d.field(wf.Field)
		if v == nil {
			return false
		}
		f := &bound.Field{Var: v}
		if wf.Equals >= 0 {
			if wf.Equals >= len(s.Params) {
				return false
			}
			f.Equals = s.Params[wf.Equals]
		} else {
			var ok bool
			if f.Close, ok = d.exprs(nil, wf.Close); !ok {
				return false
			}
		}
		s.Fields = append(s.Fields, f)
	}
	return true
}

func (d *decoder) funcSpec(w wireFunc) *bound.Func {
	fn, _ := d.obj(w.Obj).(*types.Func)
	if fn == nil {
		return nil
	}
	sig := fn.Type().(*types.Signature)
	f := &bound.Func{Obj: fn}
	var ok bool
	if f.Requires, ok = d.eqs(sig, w.Requires); !ok {
		// Контракт без предусловия ослабил бы проверку вызовов: отбрасывается
		// целиком, вызов становится неизвестным.
		return nil
	}
	if w.HasReturns {
		if len(w.Returns) != sig.Results().Len() {
			return nil
		}
		f.Returns = make([]bound.Result, len(w.Returns))
		for i, wr := range w.Returns {
			f.Returns[i].Type = sig.Results().At(i).Type()
			if wr.HasArgs {
				if f.Returns[i].Args, ok = d.exprs(sig, wr.Args); !ok {
					return nil
				}
			}
		}
	}
	for _, we := range w.Ensures {
		e := bound.Ensure{}
		if g := we.Guard; g != nil {
			if g.Index < 0 || g.Index >= sig.Results().Len() {
				return nil
			}
			c, ok := d.constant(g.Value)
			if !ok {
				return nil
			}
			e.Guard = &bound.Guard{Result: sig.Results().At(g.Index), Index: g.Index, Neq: g.Neq, Value: c}
		}
		if e.Eqs, ok = d.eqs(sig, we.Eqs); !ok {
			return nil
		}
		f.Ensures = append(f.Ensures, e)
	}
	return f
}

func (d *decoder) summary(w wireSummary) (*types.Func, *summary) {
	fn, _ := d.obj(w.Obj).(*types.Func)
	if fn == nil {
		return nil, nil
	}
	sig := fn.Type().(*types.Signature)
	if len(w.Params) != len(sigParams(sig)) || len(w.Results) != sig.Results().Len() {
		return nil, nil
	}
	s := &summary{}
	for _, p := range w.Params {
		path, ok := d.fields(p.OwnPath)
		if !ok {
			return nil, nil
		}
		s.params = append(s.params, paramSum{access: p.Access, kept: p.Kept, ownTo: p.OwnTo, ownPath: path, wrote: p.Wrote})
	}
	for _, r := range w.Results {
		slot, sok := d.fields(r.Slot)
		path, pok := d.fields(r.Path)
		if !sok || !pok {
			return nil, nil
		}
		s.results = append(s.results, resultSum{fresh: r.Fresh, alias: r.Alias, slot: slot, path: path})
	}
	return fn, s
}

package checker

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"path/filepath"
)

// Проверка пакета с ошибками Go (LSP: пакет в процессе правки).
//
// Объявление считается сломанным, если в нём есть ошибка Go (её позиция
// внутри объявления или плохой узел AST) или оно пользуется чем-то
// невалидного типа: объектом, объявление которого содержит ошибку
// (`var limit = undefined()`, поле неизвестного типа, сигнатура с неизвестным
// типом), или выражением, тип которого не вывелся. Сломанные функции
// и инициализаторы не проверяются и сводок не получают: их вызовы —
// неизвестные вызовы. Остальное проверяется как обычно.

// broken — объявление n сломано.
func (c *checker) broken(n ast.Node) bool {
	if len(c.pkg.GoErrors) == 0 {
		return false
	}
	for _, e := range c.pkg.GoErrors {
		if e.Pos.IsValid() && n.Pos() <= e.Pos && e.Pos < n.End() {
			return true
		}
	}
	found := false
	ast.Inspect(n, func(n ast.Node) bool {
		if found {
			return false
		}
		switch n := n.(type) {
		case *ast.BadExpr, *ast.BadStmt, *ast.BadDecl:
			found = true
		case *ast.Ident:
			// У PkgName, Label и Builtin тип всегда Invalid — это не ошибка.
			switch obj := c.info.ObjectOf(n).(type) {
			case *types.Var, *types.Const, *types.Func, *types.TypeName:
				found = invalidType(obj.Type())
			}
		}
		if e, ok := n.(ast.Expr); ok && !found {
			if tv, ok := c.info.Types[e]; ok && invalidType(tv.Type) {
				found = true
			}
		}
		return !found
	})
	return found
}

// invalidType — в составе типа есть невалидный тип. Именованные типы не
// раскрываются (кроме случая, когда сам базовый тип невалиден): структура
// с одним невалидным полем остаётся пригодной для остальных полей.
func invalidType(t types.Type) bool {
	switch t := types.Unalias(t).(type) {
	case nil:
		return false
	case *types.Basic:
		return t.Kind() == types.Invalid
	case *types.Named:
		if u, ok := t.Underlying().(*types.Basic); ok && u.Kind() == types.Invalid {
			return true
		}
		for a := range t.TypeArgs().Types() {
			if invalidType(a) {
				return true
			}
		}
		return false
	case *types.Pointer:
		return invalidType(t.Elem())
	case *types.Slice:
		return invalidType(t.Elem())
	case *types.Array:
		return invalidType(t.Elem())
	case *types.Chan:
		return invalidType(t.Elem())
	case *types.Map:
		return invalidType(t.Key()) || invalidType(t.Elem())
	case *types.Tuple:
		for v := range t.Variables() {
			if invalidType(v.Type()) {
				return true
			}
		}
		return false
	case *types.Signature:
		return invalidType(t.Params()) || invalidType(t.Results()) ||
			(t.Recv() != nil && invalidType(t.Recv().Type()))
	case *types.Struct:
		for f := range t.Fields() {
			if invalidType(f.Type()) {
				return true
			}
		}
		return false
	}
	return false
}

// goErrorNote — пометка о непроверенном теле для импортёров (как
// firstDiag: «файл:строка: сообщение»).
func (c *checker) goErrorNote(pos token.Pos) string {
	p := c.pkg.Fset.Position(pos)
	return fmt.Sprintf("%s:%d: the function has Go errors and is not checked", filepath.Base(p.Filename), p.Line)
}

// span — диапазон исходника [pos, end).
type span struct{ pos, end token.Pos }

// mutedSpecs — объявления, диагностики спецификаций которых в пакете
// с ошибками Go не выдаются: их спецификации ссылаются на то, что ошибки
// делают невалидным, и сообщения были бы следствием ошибки Go («Curr is not
// a type», «amount has no bound parameters»). Это типы со сломанным
// объявлением, типы, которые на них ссылаются (транзитивно), и функции,
// сигнатура которых сломана или ссылается на такие типы. Диапазон включает
// doc-комментарий со спецификациями.
func (c *checker) mutedSpecs() []span {
	if len(c.pkg.GoErrors) == 0 {
		return nil
	}
	type typeDecl struct {
		obj  *types.TypeName
		node ast.Node
		at   span
	}
	var decls []typeDecl
	var funcs []*ast.FuncDecl
	for _, f := range c.pkg.Files {
		for _, d := range f.Decls {
			switch d := d.(type) {
			case *ast.FuncDecl:
				funcs = append(funcs, d)
			case *ast.GenDecl:
				if d.Tok != token.TYPE {
					continue
				}
				for _, s := range d.Specs {
					ts := s.(*ast.TypeSpec)
					doc := ts.Doc
					if !d.Lparen.IsValid() {
						doc = d.Doc
					}
					obj, _ := c.info.Defs[ts.Name].(*types.TypeName)
					decls = append(decls, typeDecl{obj, ts, span{withDoc(ts.Pos(), doc), ts.End()}})
				}
			}
		}
	}
	brokenTypes := map[*types.TypeName]bool{}
	mentions := func(n ast.Node) bool {
		found := false
		ast.Inspect(n, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok {
				if tn, ok := c.info.Uses[id].(*types.TypeName); ok && brokenTypes[tn] {
					found = true
				}
			}
			return !found
		})
		return found
	}
	var out []span
	for changed := true; changed; {
		changed = false
		for _, d := range decls {
			if d.obj != nil && !brokenTypes[d.obj] && (c.broken(d.node) || mentions(d.node)) {
				brokenTypes[d.obj], changed = true, true
				out = append(out, d.at)
			}
		}
	}
	for _, fd := range funcs {
		sig := []ast.Node{fd.Type}
		if fd.Recv != nil {
			sig = append(sig, fd.Recv)
		}
		for _, n := range sig {
			if c.broken(n) || mentions(n) {
				out = append(out, span{withDoc(fd.Pos(), fd.Doc), fd.Type.End()})
				break
			}
		}
	}
	return out
}

func withDoc(pos token.Pos, doc *ast.CommentGroup) token.Pos {
	if doc != nil {
		return doc.Pos()
	}
	return pos
}

func inSpans(spans []span, pos token.Pos) bool {
	for _, s := range spans {
		if s.pos <= pos && pos < s.end {
			return true
		}
	}
	return false
}

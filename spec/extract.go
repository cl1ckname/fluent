// Package spec содержит язык спецификаций: извлечение из комментариев,
// AST спецификаций и парсер (см. SPEC.md).
package spec

import (
	"go/ast"
	"go/token"
	"strings"
)

// Block — сырой текст одного спецификационного комментария
// (`// @ ...`, `//@ ...` или `/* @ ... */`).
type Block struct {
	Pos  token.Pos // позиция первого символа Text
	Text string
}

// Extract возвращает спецификационные блоки из doc-комментария в порядке появления.
//
// Строчный комментарий — спецификация, если начинается с `//@` или `// @`.
// Блочный — если первый непробельный символ после `/*` это `@`. Обе поблажки
// нужны из-за gofmt: в doc-комментариях объявлений верхнего уровня он
// переписывает `//@` в `// @`, а `/*@ a; b; */` — в `/*\n@ a;\n\n\tb;\n*/`.
func Extract(doc *ast.CommentGroup) []Block {
	if doc == nil {
		return nil
	}
	var blocks []Block
	for _, c := range doc.List {
		var body string
		var off int
		switch {
		case strings.HasPrefix(c.Text, "//@"):
			body, off = c.Text[3:], 3
		case strings.HasPrefix(c.Text, "// @"):
			body, off = c.Text[4:], 4
		case strings.HasPrefix(c.Text, "/*"):
			body, off = strings.TrimSuffix(c.Text[2:], "*/"), 2
			if !strings.HasPrefix(strings.TrimLeft(body, " \t\r\n"), "@") {
				continue
			}
		default:
			continue
		}
		blocks = append(blocks, Block{Pos: c.Slash + token.Pos(off), Text: body})
	}
	return blocks
}

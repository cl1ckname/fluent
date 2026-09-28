// Package spec содержит язык спецификаций: извлечение из комментариев,
// AST спецификаций и парсер (см. SPEC.md).
package spec

import (
	"go/ast"
	"go/token"
	"strings"
)

// Block — сырой текст одного спецификационного комментария
// (`//@ ...`, `// @ ...` или `/*@ ... */`).
type Block struct {
	Pos  token.Pos // позиция первого символа Text
	Text string
}

// prefixes — начала спецификационных комментариев. `// @` нужен потому, что gofmt
// переписывает `//@` в `// @` в doc-комментариях объявлений верхнего уровня.
var prefixes = []string{"//@", "// @", "/*@"}

// Extract возвращает спецификационные блоки из doc-комментария в порядке появления.
func Extract(doc *ast.CommentGroup) []Block {
	if doc == nil {
		return nil
	}
	var blocks []Block
	for _, c := range doc.List {
		for _, p := range prefixes {
			if body, ok := strings.CutPrefix(c.Text, p); ok {
				if p == "/*@" {
					body = strings.TrimSuffix(body, "*/")
				}
				blocks = append(blocks, Block{Pos: c.Slash + token.Pos(len(p)), Text: body})
				break
			}
		}
	}
	return blocks
}

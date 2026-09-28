package spec

import (
	"fmt"
	"go/constant"
	"go/token"
	"strings"
	"unicode"
	"unicode/utf8"
)

type kind int

const (
	kEOF kind = iota
	kIdent
	kLit
	kLt    // <
	kGt    // >
	kComma // ,
	kSemi  // ;
	kDot   // .
	kEq    // ==
	kAnd   // &&
)

var kindNames = [...]string{"end of spec", "identifier", "literal", "'<'", "'>'", "','", "';'", "'.'", "'=='", "'&&'"}

func (k kind) String() string { return kindNames[k] }

type tok struct {
	kind    kind
	text    string
	pos     token.Pos
	litKind token.Token // только для kLit
}

// lex разбивает текст блока на токены. `>>` всегда два токена `>`,
// поэтому `amount<a<c>>` разбирается без особых случаев.
// Символ `@` считается пробельным, как в ACSL (`@` в начале строк блочного комментария).
func lex(b Block) ([]tok, []Error) {
	var toks []tok
	var errs []Error
	src := b.Text
	i := 0
	pos := func(off int) token.Pos { return b.Pos + token.Pos(off) }
	for i < len(src) {
		r, w := utf8.DecodeRuneInString(src[i:])
		start := i
		switch {
		case unicode.IsSpace(r) || r == '@':
			i += w
		case isLetter(r):
			for i < len(src) {
				r, w := utf8.DecodeRuneInString(src[i:])
				if !isLetter(r) && !unicode.IsDigit(r) {
					break
				}
				i += w
			}
			toks = append(toks, tok{kind: kIdent, text: src[start:i], pos: pos(start)})
		case isDigit(r) || (r == '-' && i+1 < len(src) && isDigit(rune(src[i+1]))):
			i++
			for i < len(src) {
				c := src[i]
				exp := (c == '+' || c == '-') && strings.IndexByte("eEpP", src[i-1]) >= 0
				if !exp && !isDigit(rune(c)) && !isLetter(rune(c)) && c != '.' {
					break
				}
				i++
			}
			text := src[start:i]
			lk, ok := numberKind(text)
			if !ok {
				errs = append(errs, Error{pos(start), fmt.Sprintf("invalid number literal %s", text)})
				continue
			}
			toks = append(toks, tok{kind: kLit, text: text, pos: pos(start), litKind: lk})
		case r == '"' || r == '\'' || r == '`':
			i++
			for i < len(src) && src[i] != byte(r) {
				if src[i] == '\\' && r != '`' {
					i++
				}
				i++
			}
			if i >= len(src) {
				errs = append(errs, Error{pos(start), "unterminated literal"})
				break
			}
			i++
			text := src[start:i]
			lk := token.STRING
			if r == '\'' {
				lk = token.CHAR
			}
			if constant.MakeFromLiteral(text, lk, 0).Kind() == constant.Unknown {
				errs = append(errs, Error{pos(start), fmt.Sprintf("invalid literal %s", text)})
				continue
			}
			toks = append(toks, tok{kind: kLit, text: text, pos: pos(start), litKind: lk})
		default:
			k, n := punct(src[i:])
			if n == 0 {
				errs = append(errs, Error{pos(start), fmt.Sprintf("unexpected character %q", r)})
				i += w
				continue
			}
			toks = append(toks, tok{kind: k, text: src[i : i+n], pos: pos(start)})
			i += n
		}
	}
	toks = append(toks, tok{kind: kEOF, pos: pos(len(src))})
	return toks, errs
}

func punct(s string) (kind, int) {
	switch s[0] {
	case '<':
		return kLt, 1
	case '>':
		return kGt, 1
	case ',':
		return kComma, 1
	case ';':
		return kSemi, 1
	case '.':
		return kDot, 1
	case '=':
		if len(s) > 1 && s[1] == '=' {
			return kEq, 2
		}
	case '&':
		if len(s) > 1 && s[1] == '&' {
			return kAnd, 2
		}
	}
	return 0, 0
}

func numberKind(text string) (token.Token, bool) {
	for _, k := range []token.Token{token.INT, token.FLOAT, token.IMAG} {
		if constant.MakeFromLiteral(text, k, 0).Kind() != constant.Unknown {
			return k, true
		}
	}
	return 0, false
}

func isLetter(r rune) bool { return r == '_' || unicode.IsLetter(r) }
func isDigit(r rune) bool  { return '0' <= r && r <= '9' }

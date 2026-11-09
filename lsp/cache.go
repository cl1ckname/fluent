package lsp

import (
	"crypto/sha256"
	"encoding/hex"
	"go/scanner"
	"go/token"
	"io"
	"os"
	"path/filepath"
	"strings"
	"sync"

	"go.lsp.dev/protocol"
)

// factCache — сериализованные экспорты пакетов (checker.Exports.Encode) по
// ключу содержимого: файлы пакета, ключи его значимых импортов, версия
// fluent. Ключ меняется при любом изменении, влияющем на факты, поэтому
// записи не устаревают и их можно хранить на диске между сессиями.
type factCache struct {
	dir string // "" — только в памяти

	mu    sync.Mutex
	mem   map[string][]byte
	specs map[fileID]bool // есть ли в файле спецификационные комментарии
}

type fileID struct {
	path string
	size int64
	mod  int64
	sum  string // хеш содержимого для буферов редактора
}

func newFactCache(dir string) *factCache {
	return &factCache{dir: dir, mem: map[string][]byte{}, specs: map[fileID]bool{}}
}

// defaultCacheDir — каталог дискового кэша фактов или "", если его нет:
// $FLUENT_CACHE_DIR («off» — только память) или fluent/facts в
// пользовательском каталоге кэша.
func defaultCacheDir() string {
	switch d := os.Getenv("FLUENT_CACHE_DIR"); d {
	case "off":
		return ""
	case "":
	default:
		return d
	}
	d, err := os.UserCacheDir()
	if err != nil {
		return ""
	}
	return filepath.Join(d, "fluent", "facts")
}

// facts возвращает факты пакета по ключу и признак того, что пакет видит
// bounded-структуры (свои или зависимостей). Без структур импортёрам
// без своих спецификаций проверять нечего (checker.Check).
func (c *factCache) facts(key string) (data []byte, structs, ok bool) {
	raw, ok := c.get(key)
	if !ok || len(raw) == 0 {
		return nil, false, false
	}
	return raw[1:], raw[0] == 1, true
}

func (c *factCache) store(key string, data []byte, structs bool) {
	flag := byte(0)
	if structs {
		flag = 1
	}
	c.put(key, append([]byte{flag}, data...))
}

func (c *factCache) get(key string) ([]byte, bool) {
	c.mu.Lock()
	data, ok := c.mem[key]
	c.mu.Unlock()
	if ok || c.dir == "" {
		return data, ok
	}
	data, err := os.ReadFile(filepath.Join(c.dir, key))
	if err != nil {
		return nil, false
	}
	c.mu.Lock()
	c.mem[key] = data
	c.mu.Unlock()
	return data, true
}

func (c *factCache) put(key string, data []byte) {
	c.mu.Lock()
	c.mem[key] = data
	c.mu.Unlock()
	if c.dir == "" {
		return
	}
	// Запись через временный файл: параллельный читатель не увидит половину.
	if err := os.MkdirAll(c.dir, 0o700); err != nil {
		return
	}
	tmp, err := os.CreateTemp(c.dir, key+".tmp*")
	if err != nil {
		return
	}
	_, werr := tmp.Write(data)
	cerr := tmp.Close()
	if werr != nil || cerr != nil || os.Rename(tmp.Name(), filepath.Join(c.dir, key)) != nil {
		os.Remove(tmp.Name())
	}
}

// drop удаляет записи (например, если их не удалось декодировать).
func (c *factCache) drop(keys []string) {
	c.mu.Lock()
	for _, k := range keys {
		delete(c.mem, k)
	}
	c.mu.Unlock()
	if c.dir != "" {
		for _, k := range keys {
			os.Remove(filepath.Join(c.dir, k))
		}
	}
}

// hasSpecs — есть ли в файле спецификационные комментарии (`//@`, `// @`,
// `/*@`). Результат запоминается по размеру и времени изменения файла или
// по содержимому буфера.
func (c *factCache) hasSpecs(path string, overlay map[string][]byte) bool {
	src, inOverlay := overlay[path]
	var id fileID
	if inOverlay {
		sum := sha256.Sum256(src)
		id = fileID{path: path, sum: string(sum[:])}
	} else {
		st, err := os.Stat(path)
		if err != nil {
			return true // не прочитать — пусть решит полная загрузка
		}
		id = fileID{path: path, size: st.Size(), mod: st.ModTime().UnixNano()}
	}
	c.mu.Lock()
	v, ok := c.specs[id]
	c.mu.Unlock()
	if ok {
		return v
	}
	if !inOverlay {
		var err error
		if src, err = os.ReadFile(path); err != nil {
			return true
		}
	}
	v = scanSpecs(src)
	c.mu.Lock()
	c.specs[id] = v
	c.mu.Unlock()
	return v
}

// scanSpecs ищет спецификационные комментарии без разбора файла. Правило
// то же, что у spec.Extract, но для любого комментария, не только doc.
func scanSpecs(src []byte) bool {
	fset := token.NewFileSet()
	var s scanner.Scanner
	s.Init(fset.AddFile("", -1, len(src)), src, nil, scanner.ScanComments)
	for {
		_, tok, lit := s.Scan()
		switch {
		case tok == token.EOF:
			return false
		case tok != token.COMMENT:
		case strings.HasPrefix(lit, "//@"), strings.HasPrefix(lit, "// @"):
			return true
		case strings.HasPrefix(lit, "/*") && strings.HasPrefix(strings.TrimLeft(lit[2:], " \t\r\n"), "@"):
			return true
		}
	}
}

var (
	versionOnce sync.Once
	versionSum  string
)

// fluentVersion — хеш исполняемого файла: другой сборке fluent нужны
// другие факты (формат и правила вывода сводок могли измениться).
func fluentVersion() string {
	versionOnce.Do(func() {
		h := sha256.New()
		if exe, err := os.Executable(); err == nil {
			if f, err := os.Open(exe); err == nil {
				io.Copy(h, f)
				f.Close()
			}
		}
		versionSum = hex.EncodeToString(h.Sum(nil))
	})
	return versionSum
}

// emptyResult — результат без диагностик (отменённая проверка).
func emptyResult() analysisResult {
	return analysisResult{diagnostics: make(map[string][]protocol.Diagnostic)}
}

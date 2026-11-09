package lsp

import (
	"os"
	"testing"
)

// Тесты не пишут в пользовательский кэш фактов.
func TestMain(m *testing.M) {
	dir, err := os.MkdirTemp("", "fluent-cache")
	if err != nil {
		panic(err)
	}
	os.Setenv("FLUENT_CACHE_DIR", dir)
	code := m.Run()
	os.RemoveAll(dir)
	os.Exit(code)
}

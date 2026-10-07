// Команда fluent-lsp передаёт диагностики fluent по LSP через stdio.
package main

import (
	"context"
	"io"
	"log"
	"os"
	"os/signal"
	"syscall"

	"fluent/lsp"
)

type stdio struct{ reader *io.PipeReader }

// IDE может передать блокирующий stdin, у которого Close не прерывает Read.
// Промежуточный поток позволяет завершить LSP-сессию по exit, не дожидаясь EOF в stdin.
// Горутина перенаправления завершается вместе с процессом команды.
func newStdio() stdio {
	reader, writer := io.Pipe()
	go func() {
		_, err := io.Copy(writer, os.Stdin)
		_ = writer.CloseWithError(err)
	}()
	return stdio{reader: reader}
}

func (s stdio) Read(p []byte) (int, error) { return s.reader.Read(p) }
func (stdio) Write(p []byte) (int, error)  { return os.Stdout.Write(p) }
func (s stdio) Close() error               { return s.reader.Close() }

func main() {
	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()
	logger := log.New(os.Stderr, "fluent-lsp: ", log.LstdFlags)
	code, err := lsp.Serve(ctx, newStdio(), logger)
	if err != nil {
		logger.Print(err)
		code = 1
	}
	os.Exit(code)
}

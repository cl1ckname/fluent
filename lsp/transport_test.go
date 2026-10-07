package lsp

import (
	"bytes"
	"context"
	"errors"
	"io"
	"net"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"go.lsp.dev/jsonrpc2"
	"go.lsp.dev/protocol"
	"go.lsp.dev/uri"
)

type session struct {
	ctx      context.Context
	conn     jsonrpc2.Conn
	server   protocol.Server
	client   *recordingClient
	finished chan int
}

func newSession(t *testing.T) *session {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	a, b := net.Pipe()
	s := &session{ctx: ctx, client: newRecordingClient(), finished: make(chan int, 1)}
	go func() {
		code, err := Serve(ctx, a, nil)
		if err != nil && ctx.Err() == nil {
			t.Errorf("Serve: %v", err)
		}
		s.finished <- code
	}()
	s.conn = jsonrpc2.NewConn(jsonrpc2.NewHeaderStream(b), jsonrpc2.WithCodec(protocolCodec{}))
	s.conn.Go(ctx, protocol.ClientHandler(s.client, jsonrpc2.MethodNotFoundHandler))
	s.server = protocol.ServerDispatcher(s.conn)
	t.Cleanup(func() {
		cancel()
		_ = s.conn.Close()
		select {
		case <-s.finished:
		case <-time.After(5 * time.Second):
			t.Error("server failed to stop")
		}
	})
	return s
}

func initialize(t *testing.T, s *session) {
	t.Helper()
	r, err := s.server.Initialize(s.ctx, &protocol.InitializeParams{})
	if err != nil {
		t.Fatal(err)
	}
	syncOptions, ok := r.Capabilities.TextDocumentSync.(*protocol.TextDocumentSyncOptions)
	if !ok || syncOptions.Change == nil || *syncOptions.Change != protocol.TextDocumentSyncKindFull || r.Capabilities.HoverProvider != nil {
		t.Fatalf("bad capabilities: %+v", r.Capabilities)
	}
	if err := s.server.Initialized(s.ctx, &protocol.InitializedParams{}); err != nil {
		t.Fatal(err)
	}
}

func barrier(t *testing.T, s *session) {
	t.Helper()
	_, err := s.conn.Call(s.ctx, "fluent/testBarrier", nil, nil)
	if !errors.Is(err, jsonrpc2.ErrMethodNotFound) {
		t.Fatalf("unknown request: %v", err)
	}
}

func TestLifecycle(t *testing.T) {
	s := newSession(t)
	_, err := s.server.Initialize(s.ctx, &protocol.InitializeParams{})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := s.server.Initialize(s.ctx, &protocol.InitializeParams{}); !errors.Is(err, jsonrpc2.ErrInvalidRequest) {
		t.Fatalf("duplicate initialize: %v", err)
	}
	if err := s.conn.Notify(s.ctx, "unknown/notification", nil); err != nil {
		t.Fatal(err)
	}
	barrier(t, s)
	if err := s.server.Shutdown(s.ctx); err != nil {
		t.Fatal(err)
	}
	if err := s.server.Exit(s.ctx); err != nil {
		t.Fatal(err)
	}
	select {
	case code := <-s.finished:
		if code != 0 {
			t.Fatalf("exit code %d", code)
		}
		s.finished <- code // сохраняем результат завершения для очистки
	case <-time.After(3 * time.Second):
		t.Fatal("exit timed out")
	}
}

func TestBeforeInitializeAndUncleanExit(t *testing.T) {
	s := newSession(t)
	_, err := s.conn.Call(s.ctx, "unknown/request", nil, nil)
	var rpcErr *jsonrpc2.Error
	if !errors.As(err, &rpcErr) || rpcErr.Code != -32002 {
		t.Fatalf("before initialize: %v", err)
	}
	if err := s.server.Exit(s.ctx); err != nil {
		t.Fatal(err)
	}
	select {
	case code := <-s.finished:
		if code != 1 {
			t.Fatalf("exit code %d", code)
		}
		s.finished <- code
	case <-time.After(3 * time.Second):
		t.Fatal("exit timed out")
	}
}

func TestDiagnosticsOverProtocol(t *testing.T) {
	dir := testModule(t)
	defs := writeFile(t, dir, "defs.go", definitions)
	call := writeFile(t, dir, "call.go", badCall)
	s := newSession(t)
	initialize(t, s)
	open := func(path, text string) {
		t.Helper()
		if err := s.server.DidOpen(s.ctx, &protocol.DidOpenTextDocumentParams{TextDocument: protocol.TextDocumentItem{URI: uri.File(path), LanguageID: "go", Version: 1, Text: text}}); err != nil {
			t.Fatal(err)
		}
	}
	change := func(path, text string, version int32) {
		t.Helper()
		if err := s.server.DidChange(s.ctx, &protocol.DidChangeTextDocumentParams{
			TextDocument:   protocol.VersionedTextDocumentIdentifier{TextDocumentIdentifier: protocol.TextDocumentIdentifier{URI: uri.File(path)}, Version: version},
			ContentChanges: []protocol.TextDocumentContentChangeEvent{&protocol.TextDocumentContentChangeWholeDocument{Text: text}},
		}); err != nil {
			t.Fatal(err)
		}
		barrier(t, s)
	}
	save := func(path string) {
		t.Helper()
		if err := s.server.DidSave(s.ctx, &protocol.DidSaveTextDocumentParams{TextDocument: protocol.TextDocumentIdentifier{URI: uri.File(path)}}); err != nil {
			t.Fatal(err)
		}
	}
	// Открытие файла запускает проверку и соседнего файла, даже если тот закрыт.
	open(defs, definitions)
	p := waitDiagnostic(t, s.client, call, 1)
	if source, ok := p.Diagnostics[0].Source.Get(); !ok || source != "fluent" {
		t.Fatalf("source: %+v", p)
	}
	open(call, badCall)
	waitDiagnostic(t, s.client, call, 1)
	change(call, strings.ReplaceAll(badCall, "usd", "rub"), 2)
	waitDiagnostic(t, s.client, call, 0)
	// Сохранение другого файла учитывает несохранённый буфер соседнего.
	save(defs)
	p = waitDiagnostic(t, s.client, call, 0)
	if version, ok := p.Version.Get(); !ok || version != 2 {
		t.Fatalf("version: %+v", p)
	}
	change(call, badCall, 3)
	waitDiagnostic(t, s.client, call, 0)
	save(call)
	waitDiagnostic(t, s.client, call, 1)
	change(defs, "package money\nfunc broken( {", 2)
	waitDiagnostic(t, s.client, call, 0)
	save(defs)
	select {
	case message := <-s.client.messages:
		if !strings.Contains(message, "skipping") {
			t.Fatalf("message: %s", message)
		}
	case <-time.After(30 * time.Second):
		t.Fatal("missing skip message")
	}
	change(defs, definitions, 3)
	save(defs)
	waitDiagnostic(t, s.client, call, 1)
	change(call, strings.ReplaceAll(badCall, "usd", "rub"), 4)
	waitDiagnostic(t, s.client, call, 0)
	save(call)
	waitDiagnostic(t, s.client, call, 0)
	if err := s.server.DidClose(s.ctx, &protocol.DidCloseTextDocumentParams{TextDocument: protocol.TextDocumentIdentifier{URI: uri.File(call)}}); err != nil {
		t.Fatal(err)
	}
	waitDiagnostic(t, s.client, call, 0)
	// Закрытие удаляет исправленный буфер и проверяет ошибочный текст с диска.
	waitDiagnostic(t, s.client, call, 1)
	// Второй модуль работает без общего корня и предварительного обхода рабочей области.
	other := testModule(t)
	writeFile(t, other, "defs.go", definitions)
	otherCall := writeFile(t, other, "call.go", badCall)
	open(otherCall, badCall)
	waitDiagnostic(t, s.client, otherCall, 1)
	if err := s.server.DidOpen(s.ctx, &protocol.DidOpenTextDocumentParams{TextDocument: protocol.TextDocumentItem{URI: uri.URI("untitled:buffer.go"), LanguageID: "go"}}); err != nil {
		t.Fatal(err)
	}
	barrier(t, s)
	select {
	case message := <-s.client.messages:
		if !strings.Contains(message, "unsupported document URI") {
			t.Fatalf("message: %s", message)
		}
	case <-time.After(3 * time.Second):
		t.Fatal("unsupported URI not logged")
	}
}

type processStream struct {
	io.ReadCloser
	io.WriteCloser
}

func (s processStream) Close() error {
	return errors.Join(s.ReadCloser.Close(), s.WriteCloser.Close())
}

func TestStdioCommand(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	binary := filepath.Join(t.TempDir(), "fluent-lsp")
	build := exec.CommandContext(ctx, "go", "build", "-o", binary, "./cmd/fluent-lsp")
	build.Dir = ".."
	if output, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build: %v\n%s", err, output)
	}
	cmd := exec.CommandContext(ctx, binary)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	stdin, err := cmd.StdinPipe()
	if err != nil {
		t.Fatal(err)
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatal(err)
	}
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	waited := false
	t.Cleanup(func() {
		if !waited {
			cancel()
			_ = cmd.Wait()
		}
	})
	conn := jsonrpc2.NewConn(jsonrpc2.NewHeaderStream(processStream{stdout, stdin}), jsonrpc2.WithCodec(protocolCodec{}))
	conn.Go(ctx, protocol.ClientHandler(newRecordingClient(), jsonrpc2.MethodNotFoundHandler))
	defer conn.Close()
	server := protocol.ServerDispatcher(conn)
	if _, err := server.Initialize(ctx, &protocol.InitializeParams{}); err != nil {
		t.Fatal(err)
	}
	if err := server.Shutdown(ctx); err != nil {
		t.Fatal(err)
	}
	if err := server.Exit(ctx); err != nil {
		t.Fatal(err)
	}
	err = cmd.Wait()
	waited = true
	if err != nil {
		t.Fatalf("exit: %v\n%s", err, stderr.String())
	}
	if stderr.Len() != 0 {
		t.Fatalf("unexpected stderr: %s", stderr.String())
	}
}

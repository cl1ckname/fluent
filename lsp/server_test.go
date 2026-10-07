package lsp

import (
	"context"
	"io"
	"log"
	"path/filepath"
	"testing"
	"time"

	"go.lsp.dev/protocol"
	"go.lsp.dev/uri"
)

type recordingClient struct {
	protocol.UnimplementedClient
	diagnostics chan protocol.PublishDiagnosticsParams
	messages    chan string
}

func newRecordingClient() *recordingClient {
	return &recordingClient{diagnostics: make(chan protocol.PublishDiagnosticsParams, 100), messages: make(chan string, 100)}
}
func (c *recordingClient) PublishDiagnostics(_ context.Context, p *protocol.PublishDiagnosticsParams) error {
	c.diagnostics <- *p
	return nil
}
func (c *recordingClient) LogMessage(_ context.Context, p *protocol.LogMessageParams) error {
	c.messages <- p.Message
	return nil
}

func waitDiagnostic(t *testing.T, c *recordingClient, path string, count int) protocol.PublishDiagnosticsParams {
	t.Helper()
	timer := time.NewTimer(30 * time.Second)
	defer timer.Stop()
	for {
		select {
		case p := <-c.diagnostics:
			if p.URI.FsPath() == path && len(p.Diagnostics) == count {
				return p
			}
		case <-timer.C:
			t.Fatalf("timed out waiting for %d diagnostics for %s", count, path)
		}
	}
}

func TestWorkerDiscardsStaleResults(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	s := newServer(ctx, log.New(io.Discard, "", 0))
	c := newRecordingClient()
	s.client = c
	path := filepath.Join(t.TempDir(), "file.go")
	started := make(chan map[string][]byte, 10)
	release := make(chan struct{}, 10)
	s.load = func(ctx context.Context, dir string, overlay map[string][]byte) analysisResult {
		started <- overlay
		<-release // имитируем проверку, которую нельзя прервать посередине
		return analysisResult{diagnostics: map[string][]protocol.Diagnostic{path: {{Message: protocol.String("old")}}}}
	}
	go s.work()
	t.Cleanup(func() { cancel(); release <- struct{}{}; <-s.done })
	if err := s.DidOpen(ctx, &protocol.DidOpenTextDocumentParams{TextDocument: protocol.TextDocumentItem{URI: uri.File(path), Version: 1, Text: "old"}}); err != nil {
		t.Fatal(err)
	}
	select {
	case <-started:
	case <-time.After(3 * time.Second):
		t.Fatal("worker did not start")
	}
	if err := s.DidChange(ctx, &protocol.DidChangeTextDocumentParams{
		TextDocument:   protocol.VersionedTextDocumentIdentifier{TextDocumentIdentifier: protocol.TextDocumentIdentifier{URI: uri.File(path)}, Version: 2},
		ContentChanges: []protocol.TextDocumentContentChangeEvent{&protocol.TextDocumentContentChangeWholeDocument{Text: "new"}},
	}); err != nil {
		t.Fatal(err)
	}
	release <- struct{}{}
	select {
	case p := <-c.diagnostics:
		t.Fatalf("stale result published: %+v", p)
	case <-time.After(2 * debounce):
	}
	select {
	case <-started:
		t.Fatal("typing triggered analysis")
	default:
	}
	if err := s.DidSave(ctx, &protocol.DidSaveTextDocumentParams{TextDocument: protocol.TextDocumentIdentifier{URI: uri.File(path)}}); err != nil {
		t.Fatal(err)
	}
	select {
	case overlay := <-started:
		if string(overlay[path]) != "new" {
			t.Fatalf("wrong snapshot: %q", overlay[path])
		}
	case <-time.After(3 * time.Second):
		t.Fatal("save did not trigger analysis")
	}
	release <- struct{}{}
	p := waitDiagnostic(t, c, path, 1)
	if version, ok := p.Version.Get(); !ok || version != 2 {
		t.Fatalf("wrong version: %+v", p.Version)
	}
}

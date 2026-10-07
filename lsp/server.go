package lsp

import (
	"context"
	"fmt"
	"log"
	"path/filepath"
	"sort"
	"strings"
	"sync"
	"time"

	"go.lsp.dev/jsonrpc2"
	"go.lsp.dev/protocol"
	"go.lsp.dev/uri"
)

const debounce = 150 * time.Millisecond

type document struct {
	uri     uri.URI
	text    string
	version int32
}

type server struct {
	protocol.UnimplementedServer
	ctx         context.Context
	logger      *log.Logger
	client      protocol.Client
	mu          sync.Mutex
	initialized bool
	shutdown    bool
	documents   map[string]document
	pending     map[string]time.Time
	published   map[string]map[string]bool // каталог -> файлы с опубликованными диагностиками
	generation  uint64
	active      context.CancelFunc
	activeDir   string
	wake        chan struct{}
	exit        chan int
	done        chan struct{}
	load        func(context.Context, string, map[string][]byte) analysisResult
}

func newServer(ctx context.Context, logger *log.Logger) *server {
	return &server{ctx: ctx, logger: logger, documents: make(map[string]document),
		pending: make(map[string]time.Time), published: make(map[string]map[string]bool),
		wake: make(chan struct{}, 1), exit: make(chan int, 1), done: make(chan struct{}), load: analyze}
}

func ptr[T any](v T) *T { return &v }

func (s *server) Initialize(context.Context, *protocol.InitializeParams) (*protocol.InitializeResult, error) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.initialized {
		return nil, jsonrpc2.ErrInvalidRequest
	}
	s.initialized = true
	return &protocol.InitializeResult{
		Capabilities: protocol.ServerCapabilities{
			PositionEncoding: protocol.PositionEncodingKindUTF16,
			TextDocumentSync: &protocol.TextDocumentSyncOptions{
				OpenClose: ptr(true), Change: ptr(protocol.TextDocumentSyncKindFull),
				Save: &protocol.SaveOptions{IncludeText: ptr(true)},
			},
		},
		ServerInfo: protocol.ServerInfo{Name: "fluent"},
	}, nil
}

func (s *server) Initialized(context.Context, *protocol.InitializedParams) error { return nil }
func (s *server) SetTrace(context.Context, *protocol.SetTraceParams) error       { return nil }

func (s *server) Shutdown(context.Context) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.shutdown = true
	clear(s.pending)
	if s.active != nil {
		s.active()
	}
	s.signal()
	return nil
}

func (s *server) Exit(context.Context) error {
	s.mu.Lock()
	code := 1
	if s.shutdown {
		code = 0
	}
	s.mu.Unlock()
	select {
	case s.exit <- code:
	default:
	}
	return nil
}

func (s *server) path(u uri.URI) (string, bool) {
	if !u.IsFile() || !filepath.IsAbs(u.FsPath()) {
		s.log(fmt.Sprintf("skipping unsupported document URI %q", u))
		return "", false
	}
	p := filepath.Clean(u.FsPath())
	return p, filepath.Ext(p) == ".go"
}

func (s *server) DidOpen(_ context.Context, p *protocol.DidOpenTextDocumentParams) error {
	path, ok := s.path(p.TextDocument.URI)
	if !ok {
		return nil
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	s.documents[path] = document{p.TextDocument.URI, p.TextDocument.Text, p.TextDocument.Version}
	s.invalidate(filepath.Dir(path))
	s.schedule(filepath.Dir(path))
	return nil
}

func (s *server) DidChange(_ context.Context, p *protocol.DidChangeTextDocumentParams) error {
	path, ok := s.path(p.TextDocument.URI)
	if !ok {
		return nil
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	doc, ok := s.documents[path]
	if !ok || p.TextDocument.Version <= doc.version {
		return nil
	}
	for _, change := range p.ContentChanges {
		whole, ok := change.(*protocol.TextDocumentContentChangeWholeDocument)
		if !ok {
			return fmt.Errorf("fluent requires full document synchronization")
		}
		doc.text = whole.Text
	}
	doc.version = p.TextDocument.Version
	s.documents[path] = doc
	dir := filepath.Dir(path)
	s.invalidate(dir)
	// Ввод отменяет и ожидающие проверки: новую запускает только открытие или сохранение.
	delete(s.pending, dir)
	s.clear(dir)
	return nil
}

func (s *server) DidSave(_ context.Context, p *protocol.DidSaveTextDocumentParams) error {
	path, ok := s.path(p.TextDocument.URI)
	if !ok {
		return nil
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if doc, exists := s.documents[path]; exists && p.Text != nil {
		doc.text = *p.Text
		s.documents[path] = doc
	}
	s.invalidate(filepath.Dir(path))
	s.schedule(filepath.Dir(path))
	return nil
}

func (s *server) DidClose(_ context.Context, p *protocol.DidCloseTextDocumentParams) error {
	path, ok := s.path(p.TextDocument.URI)
	if !ok {
		return nil
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	dir := filepath.Dir(path)
	s.invalidate(dir)
	s.clear(dir)
	delete(s.documents, path)
	delete(s.pending, dir)
	for filename := range s.documents {
		if filepath.Dir(filename) == dir {
			s.schedule(dir)
			break
		}
	}
	return nil
}

// Методы ниже обращаются к состоянию сессии под блокировкой mu. Публикация
// использует ту же блокировку, чтобы старый снимок не отменил очистку диагностик.
func (s *server) invalidate(dir string) {
	s.generation++
	if s.active != nil {
		s.active()
		if s.activeDir != dir {
			s.schedule(s.activeDir)
		}
	}
}

func (s *server) signal() {
	select {
	case s.wake <- struct{}{}:
	default:
	}
}
func (s *server) schedule(dir string) {
	if !s.shutdown {
		s.pending[dir] = time.Now().Add(debounce)
		s.signal()
	}
}

func (s *server) log(message string) {
	s.logger.Print(message)
	if err := s.client.LogMessage(s.ctx, &protocol.LogMessageParams{Type: protocol.MessageTypeWarning, Message: message}); err != nil {
		s.logger.Printf("logMessage: %v", err)
	}
}

func (s *server) publish(path string, diagnostics []protocol.Diagnostic) {
	if diagnostics == nil {
		diagnostics = []protocol.Diagnostic{}
	}
	p := &protocol.PublishDiagnosticsParams{URI: uri.File(path), Diagnostics: diagnostics}
	if doc, ok := s.documents[path]; ok {
		p.URI = doc.uri
		p.Version = protocol.NewOptional(doc.version)
	}
	if err := s.client.PublishDiagnostics(s.ctx, p); err != nil {
		s.logger.Printf("publishDiagnostics: %v", err)
	}
}

func (s *server) clear(dir string) {
	for path := range s.published[dir] {
		s.publish(path, nil)
	}
	delete(s.published, dir)
}

func (s *server) work() {
	defer close(s.done)
	for {
		if s.ctx.Err() != nil {
			return
		}
		s.mu.Lock()
		var dir string
		var deadline time.Time
		for candidate, due := range s.pending {
			if dir == "" || due.Before(deadline) || (due.Equal(deadline) && candidate < dir) {
				dir, deadline = candidate, due
			}
		}
		if dir != "" && !time.Now().Before(deadline) {
			delete(s.pending, dir)
			ctx, cancel := context.WithCancel(s.ctx)
			s.active, s.activeDir = cancel, dir
			generation := s.generation
			overlay := make(map[string][]byte, len(s.documents))
			for path, doc := range s.documents {
				overlay[path] = []byte(doc.text)
			}
			s.mu.Unlock()
			result := s.load(ctx, dir, overlay)
			s.mu.Lock()
			if ctx.Err() == nil && generation == s.generation && !s.shutdown {
				paths := make(map[string]bool)
				for path := range s.published[dir] {
					paths[path] = true
				}
				for path := range result.diagnostics {
					paths[path] = true
				}
				for path := range s.documents {
					if filepath.Dir(path) == dir {
						paths[path] = true
					}
				}
				ordered := make([]string, 0, len(paths))
				for path := range paths {
					ordered = append(ordered, path)
				}
				sort.Strings(ordered)
				for _, path := range ordered {
					s.publish(path, result.diagnostics[path])
				}
				s.published[dir] = paths
				if len(result.messages) != 0 {
					s.log(strings.Join(result.messages, "\n"))
				}
			}
			cancel()
			s.active, s.activeDir = nil, ""
			s.mu.Unlock()
			continue
		}
		s.mu.Unlock()
		var timer *time.Timer
		var timerC <-chan time.Time
		if dir != "" {
			timer = time.NewTimer(time.Until(deadline))
			timerC = timer.C
		}
		select {
		case <-s.ctx.Done():
			if timer != nil {
				timer.Stop()
			}
			return
		case <-s.wake:
		case <-timerC:
		}
		if timer != nil {
			timer.Stop()
		}
	}
}

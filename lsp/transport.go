// Пакет lsp — LSP-сервер диагностик fluent.
package lsp

import (
	"context"
	"io"
	"log"

	"go.lsp.dev/jsonrpc2"
	"go.lsp.dev/protocol"
)

// protocolCodec использует библиотечный кодек для типов объединений протокола.
type protocolCodec struct{}

func (protocolCodec) Marshal(v any) ([]byte, error)   { return protocol.Marshal(v) }
func (protocolCodec) Unmarshal(b []byte, v any) error { return protocol.Unmarshal(b, v) }

// Serve обслуживает одну LSP-сессию через поток stdio. Код завершения следует
// правилам LSP: exit без предварительного shutdown возвращает 1.
func Serve(ctx context.Context, stream io.ReadWriteCloser, logger *log.Logger) (int, error) {
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()
	if logger == nil {
		logger = log.New(io.Discard, "", 0)
	}
	s := newServer(ctx, logger)
	conn := jsonrpc2.NewConn(jsonrpc2.NewHeaderStream(stream), jsonrpc2.WithCodec(protocolCodec{}))
	s.client = protocol.ClientDispatcher(conn)
	go s.work()
	handler := protocol.ServerHandler(s, jsonrpc2.MethodNotFoundHandler)
	// protocol.Handlers через AsyncHandler допускает параллельную обработку
	// событий до применения изменений. Параллельно выполняем только анализ.
	conn.Go(ctx, func(ctx context.Context, req *jsonrpc2.Request) (any, error) {
		s.mu.Lock()
		initialized, shutdown := s.initialized, s.shutdown
		s.mu.Unlock()
		if req.Method() != protocol.MethodExit {
			if !initialized && req.Method() != protocol.MethodInitialize {
				if req.IsCall() {
					return nil, jsonrpc2.NewError(-32002, "server not initialized")
				}
				return nil, nil
			}
			if shutdown {
				if req.IsCall() {
					return nil, jsonrpc2.ErrInvalidRequest
				}
				return nil, nil
			}
		}
		// Общий диспетчер пытается декодировать даже отсутствующие параметры
		// неизвестных методов. Отклоняем такие запросы до декодирования, а
		// уведомления, включая отмену коротких запросов, игнорируем.
		switch req.Method() {
		case protocol.MethodInitialize, protocol.MethodInitialized, protocol.MethodShutdown,
			protocol.MethodExit, protocol.MethodSetTrace, protocol.MethodTextDocumentDidOpen,
			protocol.MethodTextDocumentDidChange, protocol.MethodTextDocumentDidSave,
			protocol.MethodTextDocumentDidClose:
		default:
			return jsonrpc2.MethodNotFoundHandler(ctx, req)
		}
		result, err := handler(ctx, req)
		if !req.IsCall() {
			// Неизвестные и нереализованные уведомления не завершают сессию.
			if err != nil && req.Method() != protocol.MethodSetTrace {
				logger.Printf("%s: %v", req.Method(), err)
			}
			return nil, nil
		}
		return result, err
	})
	code := 0
	var err error
	select {
	case code = <-s.exit:
	case <-conn.Done():
		err = conn.Err()
		s.mu.Lock()
		if !s.shutdown {
			code = 1
		}
		s.mu.Unlock()
	case <-ctx.Done():
		err = ctx.Err()
	}
	cancel()
	_ = conn.Close()
	<-s.done
	return code, err
}

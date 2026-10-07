GO ?= go
BIN_DIR := bin

.DEFAULT_GOAL := build
.PHONY: build fluent fluent-lsp test test-race

build: fluent fluent-lsp

test:
	$(GO) test ./...

test-race:
	$(GO) test -race ./...

fluent: | $(BIN_DIR)
	$(GO) build -o $(BIN_DIR)/fluent ./cmd/fluent

fluent-lsp: | $(BIN_DIR)
	$(GO) build -o $(BIN_DIR)/fluent-lsp ./cmd/fluent-lsp

$(BIN_DIR):
	mkdir -p "$@"

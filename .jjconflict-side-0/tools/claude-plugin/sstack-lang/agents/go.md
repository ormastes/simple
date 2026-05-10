# Go Language Agent

**Language:** Go
**File extensions:** `.go`
**LSP server:** `gopls`

---

## Build & Test Commands

```bash
go build ./...                      # Build all packages
go build -o output ./cmd/app        # Build specific binary
go test ./...                       # Run all tests
go test ./pkg/name                  # Test specific package
go test -run TestName ./...         # Single test by name
go test -cover ./...                # With coverage
go vet ./...                        # Static analysis
go fmt ./...                        # Format all files
```

## LSP Setup

Install `gopls`:
```bash
go install golang.org/x/tools/gopls@latest
```

Ensure `GOPATH` and `GOROOT` are set. `gopls` works automatically with Go modules (`go.mod`).

## Style Rules

- **gofmt:** always format with `gofmt` or `goimports`; non-negotiable in Go
- **Naming:** `camelCase` for unexported, `PascalCase` for exported; short variable names in tight scopes
- **Error handling:** always check errors; `if err != nil { return err }` pattern
- **Interfaces:** keep interfaces small (1-3 methods); define at point of use, not implementation
- **Packages:** one package per directory; package name matches directory name
- **Comments:** exported symbols must have doc comments starting with the symbol name
- **Dependencies:** use Go modules (`go.mod`); run `go mod tidy` regularly
- **Concurrency:** prefer channels over shared memory; use `sync.Mutex` when channels are awkward
- **Testing:** use table-driven tests; `_test.go` files in same package for white-box tests

## When To Use This Agent

Dispatch this agent when the task involves:
- Writing or editing `.go` files
- Go CLI tools or servers
- Go module management (`go.mod`, `go.sum`)
- gRPC or protobuf service implementations
- Container/Docker tooling written in Go
- Cloud infrastructure tools (Terraform providers, Kubernetes operators)
- High-performance concurrent services

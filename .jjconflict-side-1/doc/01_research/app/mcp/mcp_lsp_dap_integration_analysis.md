# MCP/LSP/DAP Integration Analysis & Plan

**Date**: 2026-02-04
**Status**: Research & Planning Phase

---

## Executive Summary

This document analyzes Simple's current MCP/LSP/DAP implementation against Claude's official Rust MCP SDK, identifies gaps, and proposes a comprehensive integration plan linking these protocols with Simple's compiler/interpreter infrastructure.

### Current Status

| Protocol | Implementation | Status | Phase |
|----------|----------------|--------|-------|
| **MCP** | ✅ Complete | Production-ready | Self-hosted in Simple |
| **LSP** | ⚠️ Partial | Protocol layer only | Phase 1/4 complete |
| **DAP** | ⚠️ Partial | Mock data | Phase 1/4 complete |

---

## 1. MCP (Model Context Protocol) Comparison

### 1.1 Official Rust MCP SDK (`rmcp` crate)

**Source**: https://github.com/modelcontextprotocol (official MCP organization)

**Features**:
- JSON-RPC 2.0 transport (stdio, HTTP/SSE)
- Tool registration with JSON Schema validation
- Resource management (static + dynamic templates)
- Prompt templates
- Lifecycle management (`initialize`, `shutdown`)
- Error handling with standard MCP error codes
- Logging to stderr (stdio compliance)
- OAuth/API key authentication (HTTP transport)

**Core Primitives**:
```rust
// Tool definition
Tool {
    name: String,
    description: String,
    input_schema: JsonSchema,
}

// Resource definition
Resource {
    uri: String,
    name: String,
    description: Option<String>,
    mime_type: Option<String>,
}

// Prompt definition
Prompt {
    name: String,
    description: Option<String>,
    arguments: Vec<PromptArgument>,
}
```

### 1.2 Simple's MCP Implementation

**Location**: `src/app/mcp/main.spl`
**Config**: `.mcp.json`
**Runtime**: `bin/simple_runtime src/app/mcp/main.spl server`

**Implemented Features**:
- ✅ JSON-RPC 2.0 over stdio
- ✅ Tool registration and invocation
- ✅ Error handling with MCP error codes
- ✅ 4 core tools: `read`, `search`, `list_files`, `file_info`
- ✅ SFFI integration for file operations
- ✅ Self-hosted implementation (written in Simple)

**Missing Features** (compared to official SDK):
- ❌ Resource management (static/dynamic)
- ❌ Prompt templates
- ❌ HTTP/SSE transport (only stdio)
- ❌ Authentication mechanisms
- ❌ Advanced tool features:
  - Progress notifications
  - Cancellation support
  - Streaming responses
- ❌ Resource templates with URI patterns
- ❌ Capability negotiation beyond basic `initialize`
- ❌ Server metadata and versioning

### 1.3 Simple's Extended MCP Ecosystem

**Strength**: Simple has extensive MCP-related libraries not in the official SDK:

**Location**: `rust/lib/std/src/mcp/` (44+ modules)

**Advanced Features**:
- Multi-language providers (Python, Go, Rust, JavaScript, Ruby, C, Erlang)
- Simple language provider with:
  - Symbol table extraction
  - Parser integration
  - Dependency analysis
  - Coverage tracking
- Binary format handling (`mcp_binary.spl`)
- Transformation utilities (`mcp_transform.spl`)
- Context management (`mcp_context.spl`)
- Formatting helpers (`mcp_formatting.spl`)

**Unique Capability**: "Model Context Preview" (MCP-MCP) format
- **Spec**: `doc/06_spec/tooling/basic_mcp.md`
- Custom code representation format for LLM consumption
- Not part of official MCP protocol

---

## 2. LSP (Language Server Protocol) Analysis

### 2.1 Standard LSP Features

**Required for Full IDE Integration**:

| Category | Features | Simple Status |
|----------|----------|---------------|
| **Lifecycle** | initialize, initialized, shutdown, exit | ✅ Complete |
| **Synchronization** | didOpen, didChange, didClose, didSave | ✅ Complete |
| **Diagnostics** | publishDiagnostics | ✅ Basic (parse errors) |
| **Completion** | textDocument/completion | ❌ Missing |
| **Navigation** | definition, declaration, references, implementation | ❌ Missing |
| **Hover** | textDocument/hover | ❌ Missing |
| **Symbols** | documentSymbol, workspaceSymbol | ❌ Missing |
| **Formatting** | formatting, rangeFormatting, onTypeFormatting | ❌ Missing |
| **Refactoring** | rename, codeAction, codeLens | ❌ Missing |
| **Semantic** | semanticTokens (syntax highlighting) | ❌ Missing |

### 2.2 Simple LSP Implementation

**Location**: `src/app/lsp/*.spl`

**Files**:
- `main.spl` - Entry point
- `protocol.spl` - Type definitions
- `transport.spl` - JSON-RPC/Content-Length protocol
- `server.spl` - Request handling
- `__init__.spl` - Module initialization

**Phase 1 Complete** ✅:
- JSON-RPC 2.0 transport
- Content-Length protocol (LSP standard)
- Server lifecycle
- Document synchronization
- Basic diagnostics (parse errors)

**Phase 2-4 TODO** ⏳:
- **Phase 2**: Code completion, hover, go to definition
- **Phase 3**: Find references, document symbols, semantic tokens
- **Phase 4**: Workspace support, refactoring, formatting

**Blocker**: Needs deep compiler integration
- Parser AST access
- Type inference results
- Symbol table queries
- Scope analysis

---

## 3. DAP (Debug Adapter Protocol) Analysis

### 3.1 Standard DAP Features

**Required for Full Debugging**:

| Category | Features | Simple Status |
|----------|----------|---------------|
| **Lifecycle** | initialize, launch, attach, disconnect | ✅ Complete |
| **Breakpoints** | setBreakpoints, setFunctionBreakpoints, setExceptionBreakpoints | ✅ Protocol only |
| **Execution** | continue, pause, next, stepIn, stepOut, terminate | ✅ Protocol only |
| **Stack** | stackTrace, scopes, variables | ✅ Mock data |
| **Evaluation** | evaluate (watch, hover, repl) | ❌ Missing |
| **Advanced** | dataBreakpoints, logPoints, reverseContinue | ❌ Missing |

### 3.2 Simple DAP Implementation

**Location**: `src/app/dap/*.spl`

**Files**:
- `main.spl` - Entry point
- `protocol.spl` - DAP types
- `transport.spl` - Content-Length protocol
- `server.spl` - Request handling
- `breakpoints.spl` - Breakpoint management

**Phase 1 Complete** ✅:
- DAP protocol compliance
- Breakpoint storage (line, conditional)
- Execution control (protocol level)
- Stack trace inspection (mock)
- Variable viewing (mock)

**Phase 2-4 TODO** ⏳:
- **Phase 2**: Actual interpreter integration
- **Phase 3**: Real breakpoint triggering, live stack frames
- **Phase 4**: Expression evaluation, watch expressions

**Blocker**: Needs interpreter/runtime integration
- Bytecode execution hooks
- Stack frame capture
- Variable inspection
- Breakpoint triggers
- Step-by-step execution control

---

## 4. Simple Executable Architecture

### 4.1 Current Flow

```
User Command: simple <args>
       ↓
bin/simple (shell wrapper)
       ↓
bin/simple_runtime (Rust binary, 326 MB)
       ↓
src/app/cli/main.spl (Simple bytecode)
       ↓
Pattern match on command:
  - "mcp" → cli_run_mcp() SFFI
  - "lsp" → (not yet connected)
  - "dap" → (not yet connected)
  - "test" → cli_run_tests() SFFI
  - "lint" → cli_run_lint() SFFI
  - "fmt" → cli_run_fmt() SFFI
  - "build" → src/app/build/ (Simple)
       ↓
Rust FFI functions (src/app/io/mod.spl extern declarations)
       ↓
Execution
```

### 4.2 Compilation Pipeline

**Phases**:
1. **Lexer** → Tokens
2. **Parser** → AST
3. **HIR (High-level IR)** → Desugaring, name resolution
4. **MIR (Mid-level IR)** → Type checking, borrow checking (50+ instructions)
5. **Codegen** → Hybrid (Cranelift JIT + Interpreter)

**Current Interpreter**:
- Location: `rust/compiler/src/interpreter_extern/mod.rs`
- RuntimeValue system: `rust/runtime/src/value/ffi/mod.rs`
- Execution modes:
  - JIT compilation (Cranelift)
  - Bytecode interpretation
  - Hybrid mode

### 4.3 Missing Integration Points

**For LSP**:
- ❌ Parser API for on-demand AST generation
- ❌ Type inference query interface
- ❌ Symbol table access
- ❌ Incremental compilation
- ❌ Error recovery (partial AST)

**For DAP**:
- ❌ Interpreter execution hooks
- ❌ Breakpoint insertion in bytecode
- ❌ Stack frame introspection
- ❌ Variable inspection API
- ❌ Step execution control

**For MCP (Enhancement)**:
- ⚠️ No resource management
- ⚠️ No prompt templates
- ⚠️ No HTTP transport

---

## 5. Gap Analysis

### 5.1 MCP Gaps (vs Official Rust SDK)

| Feature | Priority | Complexity | Impact |
|---------|----------|------------|--------|
| Resource management | P1 | Medium | High - enables data context |
| Prompt templates | P2 | Low | Medium - workflow automation |
| HTTP/SSE transport | P3 | High | Low - stdio sufficient for now |
| Progress notifications | P2 | Low | Low - UX improvement |
| Cancellation support | P3 | Medium | Low - nice to have |
| Streaming responses | P3 | Medium | Low - for large data |

**Recommendation**: Prioritize Resource management first (P1), then Prompt templates (P2).

### 5.2 LSP Gaps (Phases 2-4)

| Phase | Features | Blocker | Estimated Effort |
|-------|----------|---------|------------------|
| Phase 2 | Completion, hover, definition | Parser API, symbol table | 3-4 weeks |
| Phase 3 | References, symbols, semantic tokens | Full type inference | 4-6 weeks |
| Phase 4 | Workspace, refactoring, formatting | Incremental compilation | 6-8 weeks |

**Critical Path**: Parser API → Symbol table access → Type inference integration

### 5.3 DAP Gaps (Phases 2-4)

| Phase | Features | Blocker | Estimated Effort |
|-------|----------|---------|------------------|
| Phase 2 | Interpreter hooks, basic stepping | Execution callback API | 2-3 weeks |
| Phase 3 | Real breakpoints, stack frames | Bytecode instrumentation | 3-4 weeks |
| Phase 4 | Expression evaluation, watches | Runtime value inspection | 4-5 weeks |

**Critical Path**: Interpreter hooks → Breakpoint system → Expression evaluator

---

## 6. Integration Plan

### 6.1 Architecture Vision

```
                    ┌─────────────────────────┐
                    │   Simple Compiler Core  │
                    │  (Parser, Type System,  │
                    │   Symbol Tables, HIR)   │
                    └───────────┬─────────────┘
                                │
                  ┌─────────────┼─────────────┐
                  │             │             │
         ┌────────▼────────┐   │   ┌────────▼────────┐
         │   LSP Server    │   │   │   DAP Server    │
         │  (IDE Support)  │   │   │   (Debugging)   │
         └────────┬────────┘   │   └────────┬────────┘
                  │            │            │
         ┌────────▼────────────▼────────────▼────────┐
         │       Simple Runtime & Interpreter        │
         │  (Bytecode execution, GC, FFI, Hooks)     │
         └────────┬──────────────────────────────────┘
                  │
         ┌────────▼────────┐
         │   MCP Server    │
         │ (Tool/Resource  │
         │   Integration)  │
         └─────────────────┘
```

### 6.2 Shared Infrastructure Needed

**1. Compiler Query API**

```simple
# Location: src/compiler/query_api.spl (NEW)

class CompilerQuery:
    # Parse file and return AST
    fn parse_file(path: text) -> Result<AST, ParseError>

    # Get symbol at position
    fn symbol_at(path: text, line: i64, col: i64) -> Option<Symbol>

    # Find all references
    fn find_references(symbol: Symbol) -> [Location]

    # Get type information
    fn type_of(expr: Expr) -> Option<Type>

    # Get completions at position
    fn completions_at(path: text, line: i64, col: i64) -> [Completion]

    # Get diagnostics
    fn diagnostics(path: text) -> [Diagnostic]
```

**2. Interpreter Hook API**

```simple
# Location: src/runtime/hooks.spl (NEW)

class InterpreterHooks:
    # Register breakpoint
    fn add_breakpoint(file: text, line: i64, condition: Option<text>) -> BreakpointID

    # Remove breakpoint
    fn remove_breakpoint(id: BreakpointID)

    # Step execution
    fn step_over() -> ExecutionState
    fn step_into() -> ExecutionState
    fn step_out() -> ExecutionState

    # Get current stack frames
    fn stack_frames() -> [StackFrame]

    # Inspect variables in scope
    fn variables_in_scope(frame_id: i64) -> [Variable]

    # Evaluate expression in context
    fn evaluate(expr: text, frame_id: i64) -> Result<Value, EvalError>

    # Execution control
    fn continue() -> ExecutionState
    fn pause()
```

**3. Resource Management API (for MCP)**

```simple
# Location: src/app/mcp/resources.spl (NEW)

class ResourceManager:
    # Register static resource
    fn register_resource(uri: text, content_fn: fn() -> text)

    # Register dynamic resource template
    fn register_template(uri_pattern: text, content_fn: fn(params: Dict) -> text)

    # List available resources
    fn list_resources() -> [ResourceInfo]

    # Read resource content
    fn read_resource(uri: text) -> Result<text, Error>
```

### 6.3 Implementation Phases

#### **Phase 1: Shared Infrastructure** (4-6 weeks)
**Goal**: Build query APIs for LSP/DAP integration

**Tasks**:
1. ✅ Parser API for on-demand AST generation
2. ✅ Symbol table query interface
3. ✅ Type inference integration
4. ✅ Error recovery (partial AST)
5. ✅ Interpreter hook API design
6. ✅ Bytecode execution callbacks

**Deliverables**:
- `src/compiler/query_api.spl`
- `src/runtime/hooks.spl`
- Unit tests for both APIs
- Documentation in `doc/07_guide/compiler_query_api.md`

#### **Phase 2: MCP Enhancement** (2-3 weeks)
**Goal**: Add Resource and Prompt support to MCP

**Tasks**:
1. Implement Resource management
   - Static resources (file contents, docs)
   - Dynamic templates (symbol info, type info)
2. Implement Prompt templates
   - Refactoring prompts
   - Code generation prompts
3. Add progress notifications
4. Update `.mcp.json` configuration

**Deliverables**:
- `src/app/mcp/resources.spl`
- `src/app/mcp/prompts.spl`
- Updated `doc/07_guide/mcp_setup_and_usage.md`
- Test coverage in `test/lib/std/unit/mcp/`

#### **Phase 3: LSP Phase 2** (3-4 weeks)
**Goal**: Code completion, hover, go to definition

**Tasks**:
1. Integrate Compiler Query API
2. Implement `textDocument/completion`
   - Variable/function completion
   - Module imports
   - Keyword completion
3. Implement `textDocument/hover`
   - Type information
   - Documentation strings
4. Implement `textDocument/definition`
   - Symbol navigation
5. Update diagnostics with type errors

**Deliverables**:
- Enhanced `src/app/lsp/server.spl`
- New `src/app/lsp/features/` module
- VS Code/Neovim configuration guides
- Test suite

#### **Phase 4: DAP Phase 2** (2-3 weeks)
**Goal**: Real debugging with interpreter integration

**Tasks**:
1. Integrate Interpreter Hook API
2. Implement real breakpoint triggering
3. Capture live stack frames
4. Variable inspection in current scope
5. Step execution (over, into, out)

**Deliverables**:
- Enhanced `src/app/dap/server.spl`
- Integrated `src/app/dap/interpreter_bridge.spl`
- VS Code/Neovim debugging guides
- Test suite with debuggable sample programs

#### **Phase 5: LSP Phase 3** (4-6 weeks)
**Goal**: Find references, symbols, semantic tokens

**Tasks**:
1. `textDocument/references` - find all usages
2. `textDocument/documentSymbol` - outline view
3. `workspace/symbol` - global symbol search
4. `textDocument/semanticTokens` - syntax highlighting
5. Signature help

**Deliverables**:
- Full LSP feature set (90% coverage)
- Performance optimization
- Multi-file workspace support

#### **Phase 6: DAP Phase 3-4** (4-5 weeks)
**Goal**: Expression evaluation, watches, advanced debugging

**Tasks**:
1. Expression evaluation in debug context
2. Watch expressions
3. Conditional breakpoints (with evaluation)
4. Exception breakpoints
5. Log points

**Deliverables**:
- Full DAP feature set (90% coverage)
- Advanced debugging workflows
- Debugging guide with examples

---

## 7. Technical Considerations

### 7.1 Performance

**LSP Performance Targets**:
- Completion: < 50ms response time
- Hover: < 20ms response time
- Diagnostics: < 200ms for typical file
- Incremental parsing: < 100ms for typical edit

**Strategies**:
- Incremental compilation
- AST caching
- Symbol table indexing
- Background analysis threads

**DAP Performance Targets**:
- Breakpoint hit: < 10ms overhead
- Stack frame capture: < 50ms
- Variable inspection: < 100ms

**Strategies**:
- Lazy stack frame construction
- On-demand variable evaluation
- Efficient bytecode instrumentation

### 7.2 Error Recovery

**LSP Requirement**: Partial AST even with syntax errors
- Error productions in parser
- Resilient type inference
- Graceful degradation

**DAP Requirement**: Debugging broken programs
- Safe evaluation in error states
- Partial stack traces
- Undefined variable handling

### 7.3 Concurrency

**LSP**: Multi-threaded analysis
- Background parsing
- Incremental analysis
- Async diagnostics

**DAP**: Single-threaded debugging
- Pause/resume execution
- Step control
- Breakpoint synchronization

### 7.4 Security

**MCP Resources**:
- Path traversal prevention
- Resource access control
- Rate limiting

**DAP Expression Evaluation**:
- Sandboxed execution
- Timeout enforcement
- Side-effect prevention

---

## 8. Comparison with Other Languages

### 8.1 Rust Analyzer (rust-analyzer)

**Features Simple should adopt**:
- Incremental compilation
- Macro expansion (for Simple metaprogramming)
- Workspace-wide analysis
- Semantic tokens
- Code actions (quick fixes)

### 8.2 TypeScript Language Server (tsserver)

**Features Simple should adopt**:
- Fast completion (< 50ms)
- Intelligent imports
- Rename refactoring
- Organize imports

### 8.3 Python Language Server (pyright/pylsp)

**Features Simple should adopt**:
- Type inference hints
- Import resolution
- Docstring integration

---

## 9. Documentation Gaps

**Current Documentation** ✅:
- MCP setup guide: `doc/07_guide/mcp_setup_and_usage.md`
- LSP README: `src/app/lsp/README.md`
- DAP README: `src/app/dap/README.md`
- MCP spec: `doc/06_spec/tooling/basic_mcp.md`

**Needed Documentation** ❌:
- Compiler Query API guide
- Interpreter Hook API guide
- LSP integration guide (VS Code, Neovim, Emacs)
- DAP integration guide with examples
- Performance tuning guide
- Troubleshooting guide

---

## 10. Testing Strategy

### 10.1 MCP Testing
- ✅ Existing: `test/lib/std/unit/mcp/` (4 test files)
- ⏳ Needed: Resource/prompt integration tests

### 10.2 LSP Testing
- SPipe tests for each LSP feature
- Integration tests with sample Simple projects
- Performance benchmarks

### 10.3 DAP Testing
- SPipe tests for debugging workflows
- Sample programs with known breakpoint behavior
- Edge case testing (errors, infinite loops)

---

## 11. Roadmap Summary

| Phase | Duration | Deliverable | Status |
|-------|----------|-------------|--------|
| Phase 1 | 4-6 weeks | Compiler Query API + Interpreter Hooks | 📝 Planned |
| Phase 2 | 2-3 weeks | MCP Resources + Prompts | 📝 Planned |
| Phase 3 | 3-4 weeks | LSP Phase 2 (Completion, Hover, Goto) | 📝 Planned |
| Phase 4 | 2-3 weeks | DAP Phase 2 (Real debugging) | 📝 Planned |
| Phase 5 | 4-6 weeks | LSP Phase 3 (References, Symbols) | 📝 Planned |
| Phase 6 | 4-5 weeks | DAP Phase 3-4 (Evaluation, Watches) | 📝 Planned |

**Total Estimated Time**: 19-27 weeks (~5-7 months)

---

## 12. Success Criteria

### MCP Enhancement
- ✅ Resources API implemented
- ✅ Prompt templates working
- ✅ Documentation updated
- ✅ Tests passing (>90% coverage)

### LSP Full Integration
- ✅ Code completion works in VS Code
- ✅ Go to definition navigates correctly
- ✅ Hover shows type information
- ✅ Find references shows all usages
- ✅ Diagnostics show type errors
- ✅ Response time < 50ms for completion

### DAP Full Integration
- ✅ Breakpoints trigger correctly
- ✅ Step execution works (over, into, out)
- ✅ Stack frames show live data
- ✅ Variables inspect correctly
- ✅ Expression evaluation works
- ✅ Conditional breakpoints evaluate

---

## 13. Next Steps

**Immediate Actions**:
1. **Get user approval** on this plan
2. **Design Compiler Query API** (`src/compiler/query_api.spl`)
3. **Design Interpreter Hook API** (`src/runtime/hooks.spl`)
4. **Prototype incremental parsing** for LSP performance
5. **Prototype breakpoint injection** for DAP

**Review Required**:
- Architecture feasibility with core team
- Performance targets validation
- Resource allocation and timeline

---

## References

- Official MCP SDK: https://github.com/modelcontextprotocol
- LSP Specification: https://microsoft.github.io/language-server-protocol/
- DAP Specification: https://microsoft.github.io/debug-adapter-protocol/
- Simple MCP Implementation: `src/app/mcp/main.spl`
- Simple LSP Implementation: `src/app/lsp/*.spl`
- Simple DAP Implementation: `src/app/dap/*.spl`
- Compiler Architecture: `rust/compiler/`
- Runtime Architecture: `rust/runtime/`

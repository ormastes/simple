# LSP Branch Coverage Analysis and Implementation Plan

**Generated:** 2026-01-29
**Goal:** Achieve 100% branch coverage for Simple LSP implementation

---

## Executive Summary

The Simple Language Server implementation in `src/app/lsp/` has **partial test coverage**:
- **Current tests:** 157 tests across 16 spec files
- **Coverage gaps:** Multiple critical branches untested
- **Priority:** HIGH - LSP is user-facing and critical for editor integration

---

## LSP Server Architecture

### Core Components

1. **Server (`src/app/lsp/server.spl`)** - Main server logic with 629 lines
2. **Protocol (`src/app/lsp/protocol.spl`)** - LSP protocol types
3. **Transport (`src/app/lsp/transport.spl`)** - JSON-RPC communication
4. **Handlers** - Request/notification handlers:
   - `handlers/completion.spl` - Autocomplete
   - `handlers/definition.spl` - Go to definition
   - `handlers/diagnostics.spl` - Error/warning diagnostics
   - `handlers/hover.spl` - Hover information
   - `handlers/references.spl` - Find references
   - `handlers/semantic_tokens.spl` - Syntax highlighting
   - `handlers/verification.spl` - Lean verification integration

---

## Branch Coverage Analysis

### 1. Request Handler Dispatcher (Lines 550-577)

**Method:** `handle_request(request: JsonRpcRequest)`

| Branch | Method | Tested | Test File |
|--------|--------|--------|-----------|
| ✅ | `"initialize"` | Partial | None (lifecycle tests missing) |
| ✅ | `"shutdown"` | No | ❌ Missing |
| ✅ | `"textDocument/semanticTokens/full"` | Yes | semantic_tokens_spec.spl |
| ✅ | `"textDocument/hover"` | Yes | hover_spec.spl |
| ✅ | `"textDocument/definition"` | Yes | definition_spec.spl |
| ✅ | `"textDocument/references"` | Yes | references_spec.spl |
| ✅ | `"textDocument/completion"` | Yes | completion_spec.spl |
| ❌ | `"simple/leanDefinition"` | No | ❌ Missing |
| ❌ | `"simple/verificationSymbols"` | No | ❌ Missing |
| ✅ | `default (unknown method)` | No | ❌ Missing |

**Coverage:** 6/10 branches tested (60%)

---

### 2. Notification Handler Dispatcher (Lines 580-595)

**Method:** `handle_notification(notification: JsonRpcNotification)`

| Branch | Method | Tested | Test File |
|--------|--------|--------|-----------|
| ❌ | `"initialized"` | No | ❌ Missing |
| ❌ | `"exit"` | No | ❌ Missing |
| ❌ | `"textDocument/didOpen"` | No | ❌ Missing |
| ❌ | `"textDocument/didChange"` | No | ❌ Missing |
| ❌ | `"textDocument/didClose"` | No | ❌ Missing |
| ✅ | `default (unknown notification)` | No | ❌ Missing |

**Coverage:** 0/6 branches tested (0%)

---

### 3. Message Type Dispatcher (Lines 615-626)

**Method:** `run()` main loop

| Branch | Type | Tested | Test File |
|--------|------|--------|-----------|
| ❌ | `"request"` | No | ❌ Missing |
| ❌ | `"notification"` | No | ❌ Missing |
| ❌ | `"response"` (unexpected) | No | ❌ Missing |
| ❌ | `default (unknown type)` | No | ❌ Missing |

**Coverage:** 0/4 branches tested (0%)

---

### 4. Individual Handler Error Branches

Each handler has multiple error paths:

#### `handle_completion` (Lines 250-293)
- ❌ Missing params → Error response
- ❌ Document not found → Error response
- ❌ No tree (parse failed) → Empty completions
- ✅ Tree available, no completions → Empty array
- ✅ Tree available, with completions → Completion items

#### `handle_definition` (Lines 356-401)
- ❌ Missing params → Error
- ❌ Document not found → Error
- ❌ No tree → Null response
- ✅ Tree available, definition found → Location
- ✅ Tree available, no definition → Null

#### `handle_hover` (Lines 404-446)
- ❌ Missing params → Error
- ❌ Document not found → Error
- ❌ No tree → Null response
- ✅ Tree available, hover info found → Hover data
- ✅ Tree available, no hover info → Null

#### `handle_references` (Lines 296-354)
- ❌ Missing params → Error
- ❌ Document not found → Error
- ❌ No tree → Null response
- ✅ Tree available, references found → Locations
- ✅ Tree available, no references → Null
- ❌ `includeDeclaration` parameter handling

#### `handle_semantic_tokens_full` (Lines 449-478)
- ❌ Missing params → Error
- ❌ Document not found → Error
- ❌ No tree → Empty tokens
- ✅ Tree available → Token array

#### `handle_did_open` (Lines 133-152)
- ❌ Missing params → Error
- ✅ Valid params → Document cached + diagnostics

#### `handle_did_change` (Lines 154-206)
- ❌ Missing params → Error
- ❌ Empty content changes → Error
- ✅ Debouncing logic → Delayed parsing
- ✅ Immediate parsing → Incremental update
- ❌ Metrics recording

#### `handle_did_close` (Lines 208-222)
- ❌ Missing params → Error
- ❌ Valid params → Document removed

#### `publish_diagnostics` (Lines 224-248)
- ❌ Document not in cache → Empty diagnostics
- ❌ Tree available → Tree-sitter diagnostics
- ❌ No tree → Empty diagnostics

---

### 5. Lifecycle Handlers

#### `handle_initialize` (Lines 88-101)
- ❌ State transition Uninitialized → Initialized
- ❌ Capability negotiation
- ❌ Response with server capabilities

#### `handle_shutdown` (Lines 109-118)
- ❌ State transition to ShuttingDown
- ❌ Null response sent

#### `handle_exit` (Lines 121-131)
- ❌ Exit code 0 when ShuttingDown
- ❌ Exit code 1 when not ShuttingDown

---

### 6. Custom Handlers (Simple-specific)

#### `handle_lean_definition` (Lines 481-518)
- ❌ Missing params → Error
- ❌ Document not found → Error
- ❌ No tree → Null
- ❌ No Lean output dir → Null
- ❌ With Lean output dir → Verification location

#### `handle_verification_symbols` (Lines 521-547)
- ❌ Missing params → Error
- ❌ Document not found → Error
- ❌ No tree → Empty array
- ❌ Tree available → Symbol array

---

## Overall Coverage Statistics

| Category | Total Branches | Tested | Untested | Coverage |
|----------|----------------|--------|----------|----------|
| Request dispatcher | 10 | 6 | 4 | 60% |
| Notification dispatcher | 6 | 0 | 6 | 0% |
| Message type dispatcher | 4 | 0 | 4 | 0% |
| Error paths | ~40 | ~5 | ~35 | 12.5% |
| Lifecycle | 6 | 0 | 6 | 0% |
| Custom handlers | 8 | 0 | 8 | 0% |
| **TOTAL** | **~74** | **~11** | **~63** | **~15%** |

---

## Test File Status

### Existing Tests (157 tests)
1. ✅ `completion_spec.spl` - 11 tests (CompletionItem builder)
2. ✅ `definition_spec.spl` - 5 tests (basic definition finding)
3. ✅ `diagnostics_spec.spl` - 10 tests (Position, Range, Diagnostic types)
4. ✅ `hover_spec.spl` - 5 tests (basic hover)
5. ✅ `references_spec.spl` - 5 tests (basic references)
6. ✅ `semantic_tokens_spec.spl` - 6 tests (token types)
7. ✅ `semantic_tokens_integration_spec.spl` - 4 tests (integration)
8. ✅ `code_action_kind_spec.spl` - 31 tests (CodeActionKind enum)
9. ✅ `symbol_kind_spec.spl` - 80 tests (SymbolKind enum)
10. ❌ `helper_functions_spec.spl` - 0 tests (empty file)
11. ❌ `server_capabilities_spec.spl` - 0 tests (empty file)
12. ❌ `workspace_edit_spec.spl` - 0 tests (empty file)
13. ❌ `wasm_*.spl` - 0 tests (4 empty files for WASM integration)

### Missing Tests (Need to Create)
1. ❌ `server_lifecycle_spec.spl` - Initialize, initialized, shutdown, exit
2. ❌ `document_sync_spec.spl` - didOpen, didChange, didClose
3. ❌ `error_handling_spec.spl` - Error paths for all handlers
4. ❌ `verification_spec.spl` - leanDefinition, verificationSymbols
5. ❌ `message_dispatcher_spec.spl` - Main loop message routing
6. ❌ `diagnostics_integration_spec.spl` - Full diagnostics pipeline
7. ❌ `debouncing_spec.spl` - didChange debouncing logic
8. ❌ `metrics_spec.spl` - Performance metrics tracking
9. ❌ `query_cache_spec.spl` - Query result caching

---

## Implementation Plan

### Phase 1: Critical Path Coverage (High Priority)
**Goal:** Cover main request/notification dispatchers and lifecycle

1. **Create `server_lifecycle_spec.spl`**
   - Test initialize → initialized → shutdown → exit flow
   - Test exit codes (0 after shutdown, 1 otherwise)
   - Test state transitions

2. **Create `document_sync_spec.spl`**
   - Test didOpen with valid document
   - Test didChange with content updates
   - Test didChange debouncing
   - Test didClose removes document

3. **Create `message_dispatcher_spec.spl`**
   - Test request routing
   - Test notification routing
   - Test unexpected response handling
   - Test unknown message type handling

**Estimated new tests:** ~30 tests
**Coverage gain:** 40% → 65%

---

### Phase 2: Error Path Coverage (Medium Priority)
**Goal:** Cover all error branches in handlers

4. **Create `error_handling_spec.spl`**
   - Test missing params for each handler
   - Test document not found errors
   - Test parse failures (no tree)
   - Test empty result cases

**Estimated new tests:** ~25 tests
**Coverage gain:** 65% → 85%

---

### Phase 3: Advanced Features (Medium Priority)
**Goal:** Cover custom handlers and optimizations

5. **Create `verification_spec.spl`**
   - Test leanDefinition with/without output dir
   - Test verificationSymbols extraction
   - Test Lean artifact file paths

6. **Create `debouncing_spec.spl`**
   - Test didChange debouncing delay
   - Test multiple rapid changes
   - Test metrics recording

7. **Create `query_cache_spec.spl`**
   - Test query result caching
   - Test cache invalidation on document change
   - Test cache size limits

**Estimated new tests:** ~20 tests
**Coverage gain:** 85% → 95%

---

### Phase 4: Integration Tests (Low Priority)
**Goal:** Full end-to-end workflows

8. **Create `diagnostics_integration_spec.spl`**
   - Test full diagnostics publishing pipeline
   - Test diagnostics after didOpen
   - Test diagnostics after didChange

9. **Enhance existing tests**
   - Add error path tests to completion_spec.spl
   - Add error path tests to definition_spec.spl
   - Add error path tests to hover_spec.spl
   - Add error path tests to references_spec.spl

**Estimated new tests:** ~15 tests
**Coverage gain:** 95% → 100%

---

## Test Implementation Priority

### Immediate (Phase 1) - 3 files, ~30 tests
1. `server_lifecycle_spec.spl` - Core LSP lifecycle
2. `document_sync_spec.spl` - Document management
3. `message_dispatcher_spec.spl` - Message routing

### Next (Phase 2) - 1 file, ~25 tests
4. `error_handling_spec.spl` - Error branches

### Later (Phase 3) - 3 files, ~20 tests
5. `verification_spec.spl` - Custom handlers
6. `debouncing_spec.spl` - Optimizations
7. `query_cache_spec.spl` - Caching

### Final (Phase 4) - Enhancements, ~15 tests
8. `diagnostics_integration_spec.spl` - End-to-end
9. Enhance existing 7 test files with error paths

---

## Success Criteria

✅ **100% branch coverage** in `src/app/lsp/server.spl`
✅ **All error paths tested** for every handler
✅ **Lifecycle flow tested** from initialize to exit
✅ **Document sync tested** with all notification types
✅ **Custom handlers tested** (Lean verification)
✅ **Optimizations tested** (debouncing, caching, metrics)

**Total new tests:** ~90 tests
**Total tests after completion:** ~247 tests
**Estimated coverage:** 100% branch coverage

---

## Next Steps

1. Create Phase 1 test files (server_lifecycle, document_sync, message_dispatcher)
2. Run tests and verify branch coverage
3. Continue with Phase 2-4 implementation
4. Add coverage reporting to CI/CD pipeline

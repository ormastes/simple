# LSP & Treesitter Pure Simple + SFFI Implementation Plan

**Status:** Design Complete - Ready for Implementation
**Author:** Claude + User
**Date:** 2026-02-05
**Estimated Time:** 2-3 weeks (80+ tests)

---

## 📊 Executive Summary

**Goal:** Implement LSP server and Treesitter parser in **Pure Simple** using SFFI wrappers for native functionality.

**Current Status:**
- ❌ LSP: 0/80 tests passing (skeleton exists)
- ❌ Treesitter: 0/11 tests passing (no implementation)

**Strategy:**
1. **Two-Tier SFFI Pattern** - Simple wrappers over minimal FFI
2. **Pure Simple Logic** - All business logic in Simple
3. **Incremental Rollout** - Core → Features → Optimizations

---

## 🔍 Phase 1: Requirements Analysis

### LSP Requirements (80 tests)

#### A. Server Lifecycle (17 tests)
```
✅ Initialize/shutdown protocol
✅ State management (Uninitialized → Initialized → ShuttingDown)
✅ Capability negotiation
✅ Exit codes (0 if shutdown, 1 otherwise)
```

#### B. Document Synchronization (18 tests)
```
✅ didOpen - Document opened in editor
✅ didChange - Document edited (incremental)
✅ didSave - Document saved
✅ didClose - Document closed
✅ Version tracking
✅ Content sync
```

#### C. Code Intelligence Features (45 tests)

| Feature | Tests | Description |
|---------|-------|-------------|
| Completion | 11 | Auto-complete (keywords, functions, variables) |
| Hover | 5 | Show type info on hover |
| Definition | 5 | Go to definition |
| References | 5 | Find all references |
| Diagnostics | 9 | Show errors/warnings |
| Semantic Tokens | 10 | Syntax highlighting |

### Treesitter Requirements (11 tests)

#### A. Core Parser (5 tests)
```
✅ Create parser for language
✅ Parse source code → AST
✅ Incremental parsing (edits)
✅ Error recovery
✅ Cursor navigation
```

#### B. Query System (6 tests)
```
✅ S-expression queries
✅ Pattern matching
✅ Captures
✅ Predicates
✅ Highlights
```

---

## 🏗️ Phase 2: Architecture Design

### High-Level Architecture

```
┌─────────────────────────────────────────────────────┐
│                    LSP Server                        │
│                  (Pure Simple)                       │
│                                                      │
│  ┌──────────────┐  ┌──────────────┐  ┌───────────┐ │
│  │  Lifecycle   │  │   Document   │  │  Handlers │ │
│  │  Management  │  │     Sync     │  │ (Features)│ │
│  └──────┬───────┘  └──────┬───────┘  └─────┬─────┘ │
│         │                 │                 │       │
│         └─────────────────┴─────────────────┘       │
│                           │                         │
└───────────────────────────┼─────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────┐
│              Treesitter Parser                       │
│            (Simple + SFFI Wrapper)                   │
│                                                      │
│  ┌──────────────┐  ┌──────────────┐  ┌───────────┐ │
│  │   Parser     │  │     Tree     │  │   Query   │ │
│  │   Wrapper    │  │   Wrapper    │  │  Wrapper  │ │
│  └──────┬───────┘  └──────┬───────┘  └─────┬─────┘ │
│         │                 │                 │       │
└─────────┼─────────────────┼─────────────────┼───────┘
          │                 │                 │
          ▼                 ▼                 ▼
┌─────────────────────────────────────────────────────┐
│           SFFI Runtime Functions                     │
│         (Minimal Rust FFI Bridge)                    │
│                                                      │
│  rt_ts_parser_new()        rt_ts_parse()            │
│  rt_ts_tree_root_node()    rt_ts_query_new()        │
│  rt_ts_node_child()        rt_ts_query_exec()       │
└─────────────────────────────────────────────────────┘
```

### Two-Tier SFFI Pattern

**Tier 1: Extern Declarations** (in `src/app/io/mod.spl`)
```simple
# Treesitter Parser FFI
extern fn rt_ts_parser_new(language: text) -> i64
extern fn rt_ts_parser_parse(handle: i64, source: text) -> i64
extern fn rt_ts_tree_root_node(tree_handle: i64) -> i64
extern fn rt_ts_node_type(node_handle: i64) -> text
extern fn rt_ts_node_start_byte(node_handle: i64) -> i64
extern fn rt_ts_node_end_byte(node_handle: i64) -> i64
extern fn rt_ts_node_child_count(node_handle: i64) -> i64
extern fn rt_ts_node_child(node_handle: i64, index: i64) -> i64
```

**Tier 2: Simple Wrappers** (in `src/lib/src/parser/treesitter.spl`)
```simple
class TreeSitterParser:
    _handle: i64
    language: text

    static fn create(lang: text) -> Result<TreeSitterParser, text>:
        val handle = rt_ts_parser_new(lang)
        if handle == 0:
            return Err("Failed to create parser for {lang}")
        Ok(TreeSitterParser(_handle: handle, language: lang))

    fn parse(source: text) -> Result<Tree, text>:
        val tree_handle = rt_ts_parser_parse(self._handle, source)
        if tree_handle == 0:
            return Err("Parse failed")
        Ok(Tree(_handle: tree_handle, source: source))
```

---

## 📐 Phase 3: Detailed Design

### 3.1 Treesitter SFFI Module

**Location:** `src/lib/src/parser/treesitter.spl`

**Exports:**
```simple
export TreeSitterParser, Tree, Node, Query, QueryCursor
export TreeSitterError, ParseError, QueryError
```

**Core Types:**

```simple
# Parser handle wrapper
class TreeSitterParser:
    _handle: i64
    language: text

    static fn create(lang: text) -> Result<TreeSitterParser, text>
    fn parse(source: text) -> Result<Tree, text>
    fn parse_incremental(source: text, old_tree: Tree, edits: [Edit]) -> Result<Tree, text>

# Parse tree wrapper
class Tree:
    _handle: i64
    source: text

    fn root_node() -> Node
    fn edit(edit: Edit)

# AST node wrapper
class Node:
    _handle: i64
    tree: Tree  # Keep reference to prevent tree from being freed

    fn kind() -> text
    fn start_byte() -> i64
    fn end_byte() -> i64
    fn start_point() -> Point
    fn end_point() -> Point
    fn child_count() -> i64
    fn child(index: i64) -> Node?
    fn named_child_count() -> i64
    fn named_child(index: i64) -> Node?
    fn parent() -> Node?
    fn next_sibling() -> Node?
    fn text() -> text

# Query wrapper
class Query:
    _handle: i64
    pattern_count: i64

    static fn create(language: text, source: text) -> Result<Query, text>
    fn capture_names() -> [text]

# Query cursor for executing queries
class QueryCursor:
    _handle: i64

    static fn create() -> QueryCursor
    fn exec(query: Query, node: Node) -> QueryMatches
    fn set_byte_range(start: i64, end: i64)

# Supporting types
struct Point:
    row: i64
    column: i64

struct Edit:
    start_byte: i64
    old_end_byte: i64
    new_end_byte: i64
    start_point: Point
    old_end_point: Point
    new_end_point: Point

struct QueryMatch:
    pattern_index: i64
    captures: [QueryCapture]

struct QueryCapture:
    node: Node
    index: i64
```

### 3.2 LSP Server Module

**Location:** `src/app/lsp/server.spl`

**Already Exists (Needs Completion):**

```simple
enum ServerState:
    Uninitialized
    Initialized
    ShuttingDown

class LspServer:
    state: ServerState
    documents: Dict<text, DocumentInfo>
    query_optimizer: QueryOptimizer
    query_cache: QueryCache
    debouncer: Debouncer
    metrics: PerformanceMetrics

    static fn create() -> LspServer
    fn handle_request(request: JsonRpcRequest) -> Result<JsonRpcResponse, text>
    fn handle_notification(notification: JsonRpcNotification)

class DocumentInfo:
    uri: text
    version: i64
    text: text
    tree: Tree?
    parser: TreeSitterParser

    static fn create(uri: text, version: i64, text: text) -> DocumentInfo
    me update(new_text: text, new_version: i64)
```

### 3.3 LSP Handlers

**Location:** `src/app/lsp/handlers/`

**Files to Implement:**

```
src/app/lsp/handlers/
├── completion.spl       # Auto-complete
├── hover.spl            # Hover info
├── definition.spl       # Go to definition
├── references.spl       # Find references
├── diagnostics.spl      # Errors/warnings
├── semantic_tokens.spl  # Syntax highlighting
└── document_symbols.spl # Outline view
```

**Example: completion.spl**

```simple
export handle_completion

use parser.treesitter.{Node, Query, QueryCursor}
use lsp.protocol.{CompletionItem, CompletionItemKind, Position}

fn handle_completion(doc: DocumentInfo, position: Position) -> Result<[CompletionItem], text>:
    """Generate completion items at cursor position."""

    # Get syntax node at position
    val node = node_at_position(doc.tree?, position)?

    # Determine completion context
    val context = completion_context(node)

    # Generate completions based on context
    match context:
        case KeywordContext:
            keyword_completions()
        case IdentifierContext:
            identifier_completions(doc, node)
        case MemberAccessContext:
            member_completions(doc, node)
        case _:
            []

fn keyword_completions() -> [CompletionItem]:
    """Return keyword completions."""
    [
        CompletionItem.create("fn", CompletionItemKind.Keyword)
            .with_detail("Function definition")
            .with_insert_text("fn ${1:name}(${2:args}):\n    ${0}"),

        CompletionItem.create("val", CompletionItemKind.Keyword)
            .with_detail("Immutable variable"),

        CompletionItem.create("var", CompletionItemKind.Keyword)
            .with_detail("Mutable variable"),

        # ... more keywords
    ]

fn identifier_completions(doc: DocumentInfo, node: Node) -> [CompletionItem]:
    """Complete identifiers from scope."""
    var items: [CompletionItem] = []

    # Find all definitions in scope
    val scope_query = Query.create("simple", """
        (function_definition name: (identifier) @name)
        (variable_declaration name: (identifier) @name)
        (class_definition name: (identifier) @name)
    """)

    val cursor = QueryCursor.create()
    val matches = cursor.exec(scope_query, doc.tree?.root_node())

    for match in matches:
        for capture in match.captures:
            val name = capture.node.text()
            items.push(CompletionItem.create(name, CompletionItemKind.Variable))

    items
```

---

## 🛠️ Phase 4: SFFI Runtime Functions

### 4.1 Required Runtime Functions

**Location:** `src/app/ffi_gen/specs/treesitter.spl`

```simple
# SFFI Spec for Treesitter
@sffi_spec("treesitter")
module TreesitterFFI:
    """SFFI bindings for tree-sitter C library."""

    # Parser management
    @extern
    fn rt_ts_parser_new(language: text) -> i64:
        """Create new parser for language. Returns handle or 0 on error."""

    @extern
    fn rt_ts_parser_free(handle: i64):
        """Free parser handle."""

    @extern
    fn rt_ts_parser_set_language(handle: i64, language: text) -> bool:
        """Set parser language."""

    # Parsing
    @extern
    fn rt_ts_parser_parse(handle: i64, source: text) -> i64:
        """Parse source code. Returns tree handle or 0 on error."""

    @extern
    fn rt_ts_parser_parse_string(handle: i64, old_tree: i64, source: text) -> i64:
        """Parse with old tree for incremental parsing."""

    # Tree management
    @extern
    fn rt_ts_tree_free(handle: i64):
        """Free tree handle."""

    @extern
    fn rt_ts_tree_root_node(tree_handle: i64) -> i64:
        """Get root node of tree. Returns node handle."""

    @extern
    fn rt_ts_tree_edit(tree_handle: i64, start_byte: i64, old_end_byte: i64,
                       new_end_byte: i64, start_row: i64, start_col: i64,
                       old_end_row: i64, old_end_col: i64,
                       new_end_row: i64, new_end_col: i64):
        """Edit tree for incremental parsing."""

    # Node operations
    @extern
    fn rt_ts_node_type(node_handle: i64) -> text:
        """Get node type string (e.g., 'function_definition')."""

    @extern
    fn rt_ts_node_symbol(node_handle: i64) -> i32:
        """Get node symbol ID."""

    @extern
    fn rt_ts_node_start_byte(node_handle: i64) -> i64:
        """Get node start byte offset."""

    @extern
    fn rt_ts_node_end_byte(node_handle: i64) -> i64:
        """Get node end byte offset."""

    @extern
    fn rt_ts_node_start_point(node_handle: i64) -> (i64, i64):
        """Get node start point (row, column)."""

    @extern
    fn rt_ts_node_end_point(node_handle: i64) -> (i64, i64):
        """Get node end point (row, column)."""

    @extern
    fn rt_ts_node_child_count(node_handle: i64) -> i64:
        """Get number of children."""

    @extern
    fn rt_ts_node_child(node_handle: i64, index: i64) -> i64:
        """Get child at index. Returns node handle or 0 if out of bounds."""

    @extern
    fn rt_ts_node_named_child_count(node_handle: i64) -> i64:
        """Get number of named children."""

    @extern
    fn rt_ts_node_named_child(node_handle: i64, index: i64) -> i64:
        """Get named child at index."""

    @extern
    fn rt_ts_node_parent(node_handle: i64) -> i64:
        """Get parent node. Returns 0 if root."""

    @extern
    fn rt_ts_node_next_sibling(node_handle: i64) -> i64:
        """Get next sibling. Returns 0 if last."""

    @extern
    fn rt_ts_node_prev_sibling(node_handle: i64) -> i64:
        """Get previous sibling. Returns 0 if first."""

    @extern
    fn rt_ts_node_is_named(node_handle: i64) -> bool:
        """Check if node is named."""

    @extern
    fn rt_ts_node_is_missing(node_handle: i64) -> bool:
        """Check if node is missing (error recovery)."""

    @extern
    fn rt_ts_node_is_extra(node_handle: i64) -> bool:
        """Check if node is extra (e.g., whitespace)."""

    @extern
    fn rt_ts_node_has_error(node_handle: i64) -> bool:
        """Check if node or descendants have errors."""

    # Query operations
    @extern
    fn rt_ts_query_new(language: text, source: text) -> i64:
        """Create query from S-expression. Returns handle or 0 on error."""

    @extern
    fn rt_ts_query_free(handle: i64):
        """Free query handle."""

    @extern
    fn rt_ts_query_pattern_count(handle: i64) -> i64:
        """Get number of patterns in query."""

    @extern
    fn rt_ts_query_capture_count(handle: i64) -> i64:
        """Get number of captures."""

    @extern
    fn rt_ts_query_capture_name(handle: i64, index: i64) -> text:
        """Get capture name by index."""

    # Query cursor operations
    @extern
    fn rt_ts_query_cursor_new() -> i64:
        """Create new query cursor."""

    @extern
    fn rt_ts_query_cursor_free(handle: i64):
        """Free query cursor."""

    @extern
    fn rt_ts_query_cursor_exec(cursor_handle: i64, query_handle: i64, node_handle: i64):
        """Execute query on node."""

    @extern
    fn rt_ts_query_cursor_next_match(cursor_handle: i64) -> (bool, i64, i64):
        """Get next match. Returns (has_match, pattern_index, capture_count)."""

    @extern
    fn rt_ts_query_cursor_next_capture(cursor_handle: i64) -> (bool, i64, i64):
        """Get next capture. Returns (has_capture, node_handle, capture_index)."""

    @extern
    fn rt_ts_query_cursor_set_byte_range(cursor_handle: i64, start: i64, end: i64):
        """Set cursor search range."""
```

**Generation:**
```bash
simple sffi-gen --gen-intern src/app/ffi_gen/specs/treesitter.spl
# Generates: build/rust/ffi_gen/src/treesitter.rs
```

### 4.2 Runtime Implementation Template

**Generated Location:** `build/rust/ffi_gen/src/treesitter.rs`

```rust
// Auto-generated by sffi-gen - DO NOT EDIT

use tree_sitter::{Parser, Tree, Node, Query, QueryCursor, Language, Point, InputEdit};
use std::collections::HashMap;

// Handle management
static mut PARSERS: Option<HashMap<i64, Parser>> = None;
static mut TREES: Option<HashMap<i64, Tree>> = None;
static mut NODES: Option<HashMap<i64, Node>> = None;
static mut QUERIES: Option<HashMap<i64, Query>> = None;
static mut CURSORS: Option<HashMap<i64, QueryCursor>> = None;
static mut NEXT_HANDLE: i64 = 1;

fn get_next_handle() -> i64 {
    unsafe {
        let handle = NEXT_HANDLE;
        NEXT_HANDLE += 1;
        handle
    }
}

#[no_mangle]
pub extern "C" fn rt_ts_parser_new(language: *const c_char) -> i64 {
    let lang_str = unsafe { CStr::from_ptr(language).to_str().unwrap() };

    let language = match lang_str {
        "simple" => tree_sitter_simple::language(),
        _ => return 0,
    };

    let mut parser = Parser::new();
    parser.set_language(language).ok()?;

    let handle = get_next_handle();
    unsafe {
        if PARSERS.is_none() {
            PARSERS = Some(HashMap::new());
        }
        PARSERS.as_mut().unwrap().insert(handle, parser);
    }

    handle
}

#[no_mangle]
pub extern "C" fn rt_ts_parser_parse(handle: i64, source: *const c_char) -> i64 {
    let source_str = unsafe { CStr::from_ptr(source).to_str().unwrap() };

    unsafe {
        let parser = PARSERS.as_mut()?.get_mut(&handle)?;
        let tree = parser.parse(source_str, None)?;

        let tree_handle = get_next_handle();
        if TREES.is_none() {
            TREES = Some(HashMap::new());
        }
        TREES.as_mut().unwrap().insert(tree_handle, tree);
        tree_handle
    }
}

// ... more implementations ...
```

---

## 🎯 Phase 5: Implementation Roadmap

### Sprint 1: Treesitter Core (Days 1-3)

**Goals:** Get basic parsing working

**Tasks:**
1. ✅ Create SFFI spec: `src/app/ffi_gen/specs/treesitter.spl`
2. ✅ Generate Rust FFI: `simple sffi-gen --gen-intern treesitter.spl`
3. ✅ Implement Simple wrappers: `src/lib/src/parser/treesitter.spl`
4. ✅ Add extern declarations: `src/app/io/mod.spl`
5. ✅ Test basic parsing: 5 core tests passing

**Deliverables:**
- `TreeSitterParser.create()` works
- `parser.parse()` returns valid tree
- `tree.root_node()` returns root
- Node navigation works (child, parent, sibling)

### Sprint 2: Treesitter Queries (Days 4-5)

**Goals:** Query system working

**Tasks:**
1. ✅ Implement Query wrapper
2. ✅ Implement QueryCursor
3. ✅ Add query execution
4. ✅ Test pattern matching: 6 query tests passing

**Deliverables:**
- S-expression queries compile
- Pattern matching works
- Captures work
- Query results iterate correctly

### Sprint 3: LSP Lifecycle (Days 6-8)

**Goals:** Server starts and responds

**Tasks:**
1. ✅ Complete `LspServer` class
2. ✅ Implement initialize/shutdown
3. ✅ Add state management
4. ✅ Test lifecycle: 17 tests passing

**Deliverables:**
- Server initializes
- Server reports capabilities
- Server shuts down cleanly
- Exit codes correct

### Sprint 4: Document Sync (Days 9-11)

**Goals:** Document tracking works

**Tasks:**
1. ✅ Implement didOpen handler
2. ✅ Implement didChange handler
3. ✅ Implement incremental parsing
4. ✅ Add document cache
5. ✅ Test document sync: 18 tests passing

**Deliverables:**
- Documents open/close
- Changes sync correctly
- Incremental parsing works
- Version tracking correct

### Sprint 5: Code Intelligence (Days 12-18)

**Goals:** All features working

**Tasks:**

| Feature | Days | Tests |
|---------|------|-------|
| Completion | 2 | 11 |
| Hover | 1 | 5 |
| Definition | 1 | 5 |
| References | 1 | 5 |
| Diagnostics | 2 | 9 |
| Semantic Tokens | 2 | 10 |

**Deliverables:**
- Auto-complete works
- Hover shows types
- Go to definition works
- Find references works
- Diagnostics show errors
- Syntax highlighting works

### Sprint 6: Polish & Optimization (Days 19-21)

**Goals:** Production ready

**Tasks:**
1. ✅ Add query caching
2. ✅ Add debouncing
3. ✅ Add performance metrics
4. ✅ Fix edge cases
5. ✅ All 91 tests passing

---

## 📋 Phase 6: Implementation Checklist

### Treesitter Module

- [ ] SFFI Spec (`src/app/ffi_gen/specs/treesitter.spl`)
  - [ ] Parser functions
  - [ ] Tree functions
  - [ ] Node functions
  - [ ] Query functions
  - [ ] Cursor functions

- [ ] Simple Wrappers (`src/lib/src/parser/treesitter.spl`)
  - [ ] `TreeSitterParser` class
  - [ ] `Tree` class
  - [ ] `Node` class
  - [ ] `Query` class
  - [ ] `QueryCursor` class
  - [ ] Supporting types (Point, Edit, etc.)

- [ ] Extern Declarations (`src/app/io/mod.spl`)
  - [ ] Add all `rt_ts_*` functions
  - [ ] Export wrapper functions

- [ ] Tests (11 tests)
  - [ ] Parser creation
  - [ ] Basic parsing
  - [ ] Incremental parsing
  - [ ] Error recovery
  - [ ] Query system
  - [ ] Captures

### LSP Server Module

- [ ] Core Server (`src/app/lsp/server.spl`)
  - [ ] Complete LspServer class
  - [ ] Add all request handlers
  - [ ] Add all notification handlers
  - [ ] Document cache management

- [ ] Handlers (`src/app/lsp/handlers/`)
  - [ ] `completion.spl` (11 tests)
  - [ ] `hover.spl` (5 tests)
  - [ ] `definition.spl` (5 tests)
  - [ ] `references.spl` (5 tests)
  - [ ] `diagnostics.spl` (9 tests)
  - [ ] `semantic_tokens.spl` (10 tests)

- [ ] Protocol (`src/app/lsp/protocol.spl`)
  - [ ] Complete JSON-RPC types
  - [ ] Complete LSP types
  - [ ] Serialization/deserialization

- [ ] Transport (`src/app/lsp/transport.spl`)
  - [ ] stdin/stdout transport
  - [ ] Message framing
  - [ ] Error handling

- [ ] Tests (80 tests)
  - [ ] Lifecycle (17 tests)
  - [ ] Document sync (18 tests)
  - [ ] Features (45 tests)

---

## 🔧 Phase 7: Build & Test Commands

### Build Commands

```bash
# Generate SFFI bindings
simple sffi-gen --gen-intern src/app/ffi_gen/specs/treesitter.spl

# Build with treesitter support
simple build --features treesitter

# Run LSP server
simple lsp
```

### Test Commands

```bash
# Test treesitter module
simple test test/lib/std/unit/parser/treesitter*.spl

# Test LSP server
simple test test/lib/std/unit/lsp/*.spl

# Test specific feature
simple test test/lib/std/unit/lsp/completion_spec.spl

# Run all LSP/Treesitter tests
simple test --tag lsp --tag treesitter
```

---

## 📈 Success Metrics

### Phase Completion

| Phase | Deliverable | Tests | Status |
|-------|-------------|-------|--------|
| 1 | Treesitter Core | 5/11 | 🔴 TODO |
| 2 | Treesitter Queries | 6/11 | 🔴 TODO |
| 3 | LSP Lifecycle | 17/80 | 🔴 TODO |
| 4 | Document Sync | 18/80 | 🔴 TODO |
| 5 | Code Intelligence | 45/80 | 🔴 TODO |
| 6 | Polish | All | 🔴 TODO |
| **Total** | **Complete** | **91/91** | **0% → 100%** |

### Performance Targets

| Metric | Target | Current |
|--------|--------|---------|
| Parse time (1000 lines) | < 50ms | ⏱️ TBD |
| Incremental parse | < 10ms | ⏱️ TBD |
| Completion latency | < 100ms | ⏱️ TBD |
| Memory per document | < 5MB | 📊 TBD |

---

## 🎓 Key Design Principles

1. **Pure Simple First** - All business logic in Simple
2. **Minimal FFI Surface** - Only performance-critical operations
3. **Two-Tier Pattern** - Extern → Simple wrapper → Business logic
4. **Incremental Rollout** - Core → Features → Optimizations
5. **Test-Driven** - Fix tests incrementally, verify each phase

---

## 🚀 Next Steps

**Immediate Actions:**
1. Create SFFI spec for Treesitter
2. Generate Rust bindings
3. Implement Simple wrappers
4. Pass first 5 core tests

**Ready to Start:** ✅
**Estimated Completion:** 2-3 weeks
**Expected Test Improvement:** +91 tests (89.1% → 90.4%)

---

**Document Status:** ✅ Complete and Ready for Implementation

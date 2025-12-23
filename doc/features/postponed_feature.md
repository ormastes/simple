# Postponed Features - Not Yet Listed in feature.md

**Status:** Documented but not tracked in feature.md
**Total Features:** 104
**Average Difficulty:** 3.2/5

This document catalogs features that are fully specified in documentation (doc/spec/, doc/plans/, doc/design/) but not yet added to the main feature tracking system in `doc/features/feature.md`.

---

## Feature ID Ranges

| Range | Category | Count | Avg Diff | Source Documents |
|-------|----------|-------|----------|------------------|
| #1300-1324 | Metaprogramming (Macros, DSL, Decorators) | 25 | 3.2 | macro.md, metaprogramming.md |
| #1325-1329 | Pattern Matching Safety | 5 | 3.0 | language_enhancement.md |
| #1330-1342 | Type System (Unions, Bitfields) | 13 | 3.5 | type_system_features.md |
| #1343-1347 | Gherkin/BDD Extensions | 5 | 2.6 | gherkin_dsl.md |
| #1348-1358 | MCP (LLM Integration) | 11 | 3.1 | basic_mcp.md |
| #1359-1368 | Developer Tools (LSP, DAP) | 10 | 3.7 | 30_pending_features.md |
| #1369-1378 | UI Frameworks (TUI, GUI) | 10 | 4.2 | 30_pending_features.md |
| #1379-1387 | Language Features (Slicing, Context Managers) | 9 | 2.7 | metaprogramming.md |
| #1388-1390 | Shared Infrastructure | 3 | 2.3 | semantic_duplication_analysis.md |
| #1391-1395 | Advanced Contract Features | 5 | 2.8 | invariant.md |
| #1396-1403 | Mock Library Fluent API | 8 | 2.9 | mock.md |

**Total:** 104 features

---

## Summary Statistics

**Overall Progress:** 0% (0/104 features complete - all postponed)

| Difficulty Level | Count | Percentage |
|------------------|-------|------------|
| Level 1 (Trivial) | 2 | 2% |
| Level 2 (Easy) | 23 | 22% |
| Level 3 (Medium) | 41 | 39% |
| Level 4 (Hard) | 31 | 30% |
| Level 5 (Very Hard) | 7 | 7% |

**Difficulty-5 Features:** See `doc/features/remain_level_5.md`

---

## A. Metaprogramming (#1300-1324)

### Contract-First Macros (#1300-1304)

**Source:** `doc/spec/macro.md`
**Status:** Partially implemented - Parser complete, non-hygienic expansion working

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1300 | `macro` keyword with contract syntax | 4 | 🔄 | R (Partial) | Full | Parser |
| #1301 | `const_eval:` and `emit:` blocks | 3 | 🔄 | R (Partial) | Full | Interp |
| #1302 | Hygienic macro expansion | 5 | ✅ | R | Full | - |
| #1303 | `intro`/`inject`/`returns` contract items | 4 | 🔄 | R (Partial) | Full | Parser |
| #1304 | One-pass macro compilation (LL(1)) | 4 | 📋 | - | Full | - |

**Description:** LL(1)-friendly macro system with compile-time symbol introduction. Macros declare effects in headers (`-> (intro fn: ..., returns: ...)`), enabling IDE autocomplete without expansion.

**Current Implementation Status:**
- ✅ **Parser (#1300, #1303):** Full macro syntax parsing (`src/parser/src/statements/mod.rs`)
  - `MacroDef`, `MacroParam`, `MacroContractItem` AST nodes complete
  - Contract items: `returns`, `intro`, `inject` - all parsed
  - Targets: `enclosing.{module|class|struct|trait}`, `callsite.block.{head|tail|here}`
  - Intro kinds: `fn`, `field`, `type`, `let`, `const`
- ✅ **Basic Expansion (#1301):** Non-hygienic template substitution (`src/compiler/src/interpreter_macro.rs`)
  - `const_eval:` blocks execute at macro expansion time
  - `emit:` blocks substitute const parameters and execute
  - Built-in macros: `println!`, `assert!`, `assert_eq!`, `vec!`, `panic!`, `format!`, `dbg!`
- ✅ **Hygienic Expansion (#1302):** Implemented via AST renaming pass
  - `MacroHygieneContext` tracks gensym counter + scope stack, renaming identifiers in emitted AST nodes before execution (`src/compiler/src/interpreter_macro.rs`)
  - `apply_macro_hygiene_*` helpers walk statements, expressions, and patterns, binding macro-introduced names with unique gensyms while preserving surrounding scopes
  - Hygiene now runs for `const_eval`, `emit`, and inline statements so macros cannot shadow runtime bindings
- ⏳ **Symbol Table Integration (#1303, #1304):** Partial
  - Contract items parsed but not integrated into symbol table
  - One-pass compilation not yet implemented
  - IDE autocomplete from headers not yet working

**Example:**
```simple
macro assert_eq(left, right) -> (intro fn: panic):
    const_eval:
        # Compile-time validation
        if !has_operator(left.type, "=="):
            error("Type {left.type} doesn't support ==")

    emit:
        if !(left == right):
            panic("assertion failed: {left} != {right}")
```

### DSL Support (#1305-1307)

**Source:** `doc/spec/metaprogramming.md` §DSL Features

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1305 | `context obj:` block (implicit receiver) | 3 | 📋 | - | Full | - |
| #1306 | `method_missing` handler | 4 | 📋 | - | Full | - |
| #1307 | Fluent interface support (method chaining) | 2 | 📋 | - | Full | - |

**Example:**
```simple
context html:
    tag("h1", "Welcome")
    p "This is a DSL"
    div:
        span "Nested content"
```

### Built-in Decorators (#1308-1311)

**Source:** `doc/spec/metaprogramming.md` §Decorators

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1308 | `@cached` decorator (memoization) | 3 | 📋 | - | Full | - |
| #1309 | `@logged` decorator (automatic logging) | 2 | 📋 | - | Full | - |
| #1310 | `@deprecated(message)` decorator | 2 | 📋 | - | Full | - |
| #1311 | `@timeout(seconds)` decorator | 3 | 📋 | - | Full | - |

**Example:**
```simple
@cached
fn expensive_calculation(x: i64) -> i64:
    return result

@logged
@retry(attempts: 3)
fn fetch_data(url: str) -> Data:
    return http_get(url)
```

### Comprehensions (#1312-1313)

**Source:** `doc/spec/metaprogramming.md` §Comprehensions

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1312 | List comprehensions `[x*x for x in 0..10]` | 3 | 📋 | - | Full | - |
| #1313 | Dict comprehensions `{x: x*x for x in 0..10}` | 3 | 📋 | - | Full | - |

### Enhanced Pattern Matching (#1314-1319)

**Source:** `doc/spec/metaprogramming.md` §Enhanced Pattern Matching

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1314 | Match guards `case x if x > 0:` | 2 | 📋 | - | Full | - |
| #1315 | Or patterns `case "quit" \| "exit":` | 2 | 📋 | - | Full | - |
| #1316 | Range patterns `case 90..100: "A"` | 3 | 📋 | - | Full | - |
| #1317 | `if let` syntax | 2 | 📋 | - | Full | - |
| #1318 | `while let` syntax | 2 | 📋 | - | Full | - |
| #1319 | Chained comparisons `if 0 < x < 10:` | 2 | 📋 | - | Full | - |

### Slicing & Spread (#1320-1324)

**Source:** `doc/spec/metaprogramming.md` §Slicing and Indexing

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1320 | Negative indexing `items[-1]` | 2 | 📋 | - | Full | - |
| #1321 | Slice syntax `items[2:5]`, `items[::2]` | 3 | 📋 | - | Full | - |
| #1322 | Tuple unpacking `let a, b = (1, 2)` | 2 | 📋 | - | Full | - |
| #1323 | Rest patterns `let first, *rest = [1,2,3,4]` | 3 | 📋 | - | Full | - |
| #1324 | Spread operators `[*a, *b]`, `{**d1, **d2}` | 3 | 📋 | - | Full | - |

---

## B. Pattern Matching Safety (#1325-1329)

**Source:** `doc/spec/language_enhancement.md` §7

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1325 | Exhaustiveness checking (compile-time) | 4 | 📋 | - | Full | - |
| #1326 | Unreachable arm detection | 3 | 📋 | - | Full | - |
| #1327 | Nested destructuring (tuples, structs, enums) | 3 | 📋 | - | Full | - |
| #1328 | Refutable vs irrefutable pattern distinction | 3 | 📋 | - | Full | - |
| #1329 | `else` as explicit non-exhaustiveness marker | 1 | 📋 | - | Full | - |

**Description:** Rust-level match safety guarantees missing from current spec. Essential for production-grade language.

---

## C. Type System Enhancements (#1330-1342)

### Union Types with Impl Blocks (#1330-1334)

**Source:** `doc/design/type_system_features.md` §3

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1330 | Union type declarations (`union Shape: Circle(...) \| Rect(...)`) | 4 | 📋 | - | Design | - |
| #1331 | Discriminant storage and runtime representation | 4 | 📋 | - | Design | - |
| #1332 | Impl blocks for unions | 3 | 📋 | - | Design | - |
| #1333 | Variant-specific methods (`fn Ok.get(self) -> T`) | 4 | 📋 | - | Design | - |
| #1334 | Recursive union support (tree structures) | 4 | 📋 | - | Design | - |

**Note:** Enums (#50-56 in feature.md) exist but lack associated data (algebraic data types). Unions extend this.

### Bitfield Types (#1335-1339)

**Source:** `doc/design/type_system_features.md` §5

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1335 | `bitfield Name(backing):` syntax | 3 | 📋 | - | Design | - |
| #1336 | Field width specification and offset calculation | 3 | 📋 | - | Design | - |
| #1337 | Automatic getter/setter generation (bit masking) | 3 | 📋 | - | Design | - |
| #1338 | FFI compatibility (C struct packing) | 4 | 📋 | - | Design | - |
| #1339 | Multi-bit fields (`red: 8, green: 8`) | 3 | 📋 | - | Design | - |

**Use Cases:** Hardware registers, network protocol headers, compact data structures.

**Example:**
```simple
bitfield StatusReg(u32):
    enabled: 1       # bit 0
    mode: 2          # bits 1-2
    priority: 4      # bits 3-6
    reserved: 25     # bits 7-31

let status = StatusReg(0b1010110)
status.enabled = 1
```

### HTTP Components (#1340-1342)

**Source:** `doc/spec/web.md`

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1340 | `StatusCode` enum with all HTTP status codes | 2 | 📋 | - | Full | - |
| #1341 | Fluent response builder API (`HttpResponse.ok().json(data)`) | 2 | 📋 | - | Full | - |
| #1342 | Route parameter extraction and matching | 3 | 📋 | - | Full | - |

**Note:** Most web framework features are tracked (#520-536), but these sub-features are undocumented.

---

## D. Gherkin DSL for BDD (#1343-1347)

**Source:** `doc/spec/gherkin_dsl.md`

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1343 | `examples` table definitions | 2 | 📋 | - | Full | - |
| #1344 | `context` step definitions (reusable given/when/then) | 3 | 📋 | - | Full | - |
| #1345 | `scenario outline` with table-driven tests | 3 | 📋 | - | Full | - |
| #1346 | Parameterized contexts (`context calculator at <n>:`) | 3 | 📋 | - | Full | - |
| #1347 | Multi-format docstrings in features | 2 | 📋 | - | Full | - |

**Note:** Basic BDD framework exists (spec tests in stdlib), but extended Gherkin features not tracked.

---

## E. MCP (Minimal Code Preview) - LLM Integration (#1348-1358)

**Source:** `doc/spec/basic_mcp.md`

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1348 | Block-mark notation (`C>`, `F>`, `T>`, `P>`, `V•`) | 2 | 📋 | - | Full | - |
| #1349 | Progressive disclosure (collapsed by default) | 3 | 📋 | - | Full | - |
| #1350 | Virtual information overlays (implicit traits, coverage) | 4 | 📋 | - | Full | - |
| #1351 | Single JSON `text` field format (token efficiency) | 2 | 📋 | - | Full | - |
| #1352 | Expand-on-demand via MCP tools | 3 | 📋 | - | Full | - |
| #1353 | Public API outline filtering | 3 | 📋 | - | Full | - |
| #1354 | Dependency symbol extraction (minimal context) | 4 | 📋 | - | Full | - |
| #1355 | AOP pointcut visualization | 3 | 📋 | - | Full | - |
| #1356 | Coverage metric overlays | 3 | 📋 | - | Full | - |
| #1357 | Signature shrinking and elision | 2 | 📋 | - | Full | - |
| #1358 | Context-aware symbol filtering | 4 | 📋 | - | Full | - |

**Description:** Token-efficient code representation for LLMs. Default view shows only public API; expand signatures/bodies on demand. 90%+ token reduction claimed.

**Relationship:** Complements existing LLM features:
- #885-889 (AST/IR Export)
- #890-893 (Context Pack Generator)
- #1200-1299 (Language Model Server & MCP - recently added to feature.md)

**Note:** #1200-1299 covers Tree-sitter and multi-language support. These features (#1348-1358) are the core MCP protocol implementation.

---

## F. Developer Tools (#1359-1368)

### Language Server Protocol (LSP) (#1359-1365)

**Source:** `doc/plans/30_pending_features.md` §1
**Priority:** Medium
**Estimated Effort:** 40 hours

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1359 | Language Server Protocol implementation | 5 | 📋 | - | Plan | - |
| #1360 | Syntax highlighting | 2 | 📋 | - | Plan | - |
| #1361 | Auto-completion | 4 | 📋 | - | Plan | - |
| #1362 | Go to definition | 3 | 📋 | - | Plan | - |
| #1363 | Find references | 3 | 📋 | - | Plan | - |
| #1364 | Hover documentation | 2 | 📋 | - | Plan | - |
| #1365 | Error diagnostics in LSP | 3 | 📋 | - | Plan | - |

**Editor Support:**
- VS Code extension
- Neovim plugin
- Generic LSP support (Emacs, Sublime, etc.)

**Dependencies:**
- Parser complete ✅
- Type checker (partial)
- AST traversal utilities

### Debug Adapter Protocol (DAP) (#1366-1368)

**Source:** `doc/plans/30_pending_features.md` §2
**Priority:** Medium
**Estimated Effort:** 50 hours

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1366 | Debug Adapter Protocol (DAP) implementation | 5 | 📋 | - | Plan | - |
| #1367 | Breakpoints and stepping (step in/over/out) | 4 | 📋 | - | Plan | - |
| #1368 | Variable inspection in debugger | 4 | 📋 | - | Plan | - |

**Integration:**
- VS Code debugger
- Neovim debugger (nvim-dap)
- Generic DAP support

**Dependencies:**
- Interpreter complete ✅
- Runtime introspection
- Source map generation

---

## G. UI Frameworks (#1369-1378)

### Terminal UI (TUI) Framework (#1369-1373)

**Source:** `doc/plans/30_pending_features.md` §6
**Priority:** Medium
**Estimated Effort:** 30 hours

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1369 | Widget system (buttons, input, lists, tables) | 4 | 📋 | - | Plan | - |
| #1370 | Layout engine (flex, grid) | 4 | 📋 | - | Plan | - |
| #1371 | Event handling (keyboard, mouse) | 3 | 📋 | - | Plan | - |
| #1372 | Styling (colors, borders, padding) | 3 | 📋 | - | Plan | - |
| #1373 | Screen management | 3 | 📋 | - | Plan | - |

**Inspiration:**
- Rust: ratatui
- Go: bubbletea
- Python: textual

**Example:**
```simple
use std.tui.*

app = App():
    layout = VBox():
        title = Text("Welcome").style(bold, color: blue)
        input = Input(placeholder: "Enter name...")
        button = Button("Submit").on_click(handle_submit)

    render(layout)
```

### GUI Framework (#1374-1378)

**Source:** `doc/plans/30_pending_features.md` §7
**Priority:** Low
**Estimated Effort:** 150+ hours

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1374 | Immediate Mode GUI (egui-style) | 5 | 📋 | - | Plan | - |
| #1375 | Native widgets (platform-specific) | 5 | 📋 | - | Plan | - |
| #1376 | Web-based GUI (Electron-style) | 5 | 📋 | - | Plan | - |
| #1377 | Hot reload support | 4 | 📋 | - | Plan | - |
| #1378 | Cross-platform rendering | 5 | 📋 | - | Plan | - |

**Recommendation:** Start with Immediate Mode GUI (#1374).

**Options:**
- **A. Native Widgets** (GTK, Qt, Cocoa, Win32) - Native look, complex
- **B. Immediate Mode** (Dear ImGui, egui) - Simple API, hot reload friendly
- **C. Web-Based** (Electron-style) - Cross-platform, heavy runtime

---

## H. Additional Language Features (#1379-1387)

### Context Managers (#1379-1380)

**Source:** `doc/spec/metaprogramming.md` §Context Managers

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1379 | `with` statement and RAII | 3 | 📋 | - | Full | - |
| #1380 | `ContextManager` trait (enter/exit) | 3 | 📋 | - | Full | - |

**Example:**
```simple
with open("file.txt") as file:
    let content = file.read()
# file automatically closed
```

### Move Closures (#1381)

**Source:** `doc/spec/metaprogramming.md` §Move Closures

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1381 | `move \:` closure syntax (capture by value) | 3 | 📋 | - | Full | - |

**Use Case:** Sending closures to actors, outliving creation scope.

**Example:**
```simple
let data = [1, 2, 3]
actor.send(move \: process(data))  # data moved into closure
```

### Primitive-as-Object Unification (#1382-1387)

**Source:** `doc/spec/primitive_as_obj.md`

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1382 | `[]` → `List[T]` auto-promotion | 2 | 📋 | - | Full | - |
| #1383 | `[T; N]` → `Array[T, N]` fixed-size arrays | 3 | 📋 | - | Full | - |
| #1384 | `str` → `String` object unification | 2 | 📋 | - | Full | - |
| #1385 | Immutable `List[T]` as persistent linked list | 4 | 📋 | - | Full | - |
| #1386 | Structural sharing for immutable collections | 4 | 📋 | - | Full | - |
| #1387 | Integer/Float/Bool object methods | 2 | 📋 | - | Full | - |

**Description:** C#-style primitive promotion where all primitives are full objects. No split like Rust's `&str` vs `String`.

---

## I. Shared Infrastructure (#1388-1390)

**Source:** `doc/design/semantic_duplication_analysis.md` §3

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1388 | Move `Diagnostic` struct to `simple_common` | 2 | 📋 | - | Design | - |
| #1389 | Cross-crate diagnostic infrastructure | 3 | 📋 | - | Design | - |
| #1390 | Structured error reporting across all crates | 3 | 📋 | - | Design | - |

**Current Issue:** Diagnostics live in parser crate, creating circular dependency. Should move to `src/common/` for shared access.

---

## J. Advanced Contract Features (#1391-1395)

**Source:** `doc/spec/invariant.md`

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1391 | `in:` precondition blocks | 2 | 📋 | - | Full | - |
| #1392 | `out(ret):` postcondition blocks | 2 | 📋 | - | Full | - |
| #1393 | `out_err(err):` error postconditions | 3 | 📋 | - | Full | - |
| #1394 | `old(expr)` value snapshots | 4 | 📋 | - | Full | - |
| #1395 | `invariant:` routine invariants (entry + exit) | 3 | 📋 | - | Full | - |

**Note:** Basic contracts (#400-406 in feature.md) are tracked, but advanced features (error contracts, `old()`, invariants) are not listed.

**Example:**
```simple
fn withdraw(amount: i64):
    in:
        amount > 0
        balance >= amount
    out(ret):
        ret == old(balance) - amount
    invariant:
        balance >= 0

    balance -= amount
    return balance
```

---

## K. Mock Library Fluent API (#1396-1403)

**Source:** `doc/spec/mock.md`

| ID | Feature | Diff | Status | Impl | Doc | Tests |
|----|---------|------|--------|------|-----|-------|
| #1396 | `mock Double<T>` type | 3 | 📋 | - | Full | - |
| #1397 | `spy Spy<T>` type (recording wrapper) | 3 | 📋 | - | Full | - |
| #1398 | `.when(method).with(args).returns(value)` DSL | 3 | 📋 | - | Full | - |
| #1399 | `.verify(method).called()` assertions | 2 | 📋 | - | Full | - |
| #1400 | `.calledTimes(n)` exact count verification | 2 | 📋 | - | Full | - |
| #1401 | `.calledWith(args)` argument verification | 3 | 📋 | - | Full | - |
| #1402 | Argument matchers (`any()`, `gt(x)`) | 3 | 📋 | - | Full | - |
| #1403 | Deep call chain mocking | 4 | 📋 | - | Full | - |

**Note:** Mock library (#230-241 in feature.md) exists, but this spec shows RSpec/Mockito-style fluent API not documented.

**Example:**
```simple
let db = mock Database

db.when("query")
  .with(any(), gt(0))
  .returns([{id: 1, name: "Alice"}])

# ... test code ...

db.verify("query").calledTimes(2)
```

---

## Priority Recommendations

### High Priority (Implement Soon):
1. **Contract-First Macros (#1300-1304)** - Fully specified, enables powerful metaprogramming
2. **MCP Integration (#1348-1358)** - Aligns with LLM-friendly goals, 90%+ token reduction
3. **Diagnostic Infrastructure (#1388-1390)** - Architectural improvement, enables better tooling
4. **Advanced Contracts (#1391-1395)** - Completes contract system

### Medium Priority (Next Phase):
5. **LSP (#1359-1365)** - High developer value, essential for adoption
6. **Pattern Matching Safety (#1325-1329)** - Production language requirement
7. **Union Types (#1330-1334)** - Extends existing enum support
8. **DSL Support (#1305-1307)** - Enables framework development
9. **Comprehensions (#1312-1313)** - Common language feature

### Low Priority (Future):
10. **TUI/GUI Frameworks (#1369-1378)** - Large effort, showcase features
11. **Gherkin Extensions (#1343-1347)** - BDD framework already exists
12. **Bitfield Types (#1335-1339)** - Niche use case
13. **Primitive-as-Object (#1382-1387)** - Design refinement

---

## Cross-References

### Features Overlapping with Tracked Features:

**Memory Model (#1096-1106 in feature.md):**
- Reference capabilities (`mut T`, `iso T`) complete
- SC-DRF memory model formally verified
- Happens-before relation implemented

**Mock Library (#230-241 in feature.md):**
- Basic mocking exists
- Fluent API (#1396-1403) not documented

**Contracts (#400-406 in feature.md):**
- Basic blocks exist
- Advanced features (#1391-1395) missing: `old()`, `out_err()`, invariants

**LLM Features (#880-919, #1200-1299 in feature.md):**
- AST/IR export, context pack, Tree-sitter tracked
- Core MCP protocol (#1348-1358) not listed

---

## Implementation Notes

### Self-Hosted Features:
- **Macros (#1300-1304):** Compiler feature (Rust)
- **MCP (#1348-1358):** Can be implemented in Simple (`simple/std_lib/src/mcp/`)
- **LSP (#1359-1365):** Should be implemented in Simple (self-hosted)
- **TUI (#1369-1373):** Stdlib feature (Simple)

### Dependencies:
- **Macros** require: Parser ✅, Type checker (partial)
- **LSP** requires: Parser ✅, Type checker, AST utilities
- **DAP** requires: Interpreter ✅, Runtime introspection
- **Union types** require: Type system redesign

---

## See Also

- `doc/features/feature.md` - Main feature tracking (588 features)
- `doc/features/remain_level_5.md` - Difficulty-5 features only
- `doc/plans/30_pending_features.md` - Pending features (source document)
- `doc/spec/macro.md` - Contract-first macro specification
- `doc/spec/metaprogramming.md` - DSL, decorators, comprehensions
- `doc/spec/basic_mcp.md` - MCP protocol specification
- `doc/design/type_system_features.md` - Union types, bitfields
- `doc/spec/language_enhancement.md` - Memory model, pattern matching

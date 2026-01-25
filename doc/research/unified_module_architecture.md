# Unified Module Architecture - Incremental Migration Plan

## Goal

Migrate Rust code to Simple where Simple code is **shorter** than Rust equivalent.
Simple executables call Rust via FFI for performance-critical operations.

## Current Status (Phase 1 Complete)

**Existing Simple CLI Apps**: 5216 lines (18 apps)
**Existing Rust CLI Modules**: 9044 lines (19 modules)
**Ratio**: Simple is ~42% smaller for CLI layer

The FFI wrapper pattern is already working well:
- `sdn/main.spl` (133 lines) calls `sdn_ffi.rs` (274 lines)
- `cli/main.spl` (319 lines) calls `cli_ffi.rs` (305 lines)

## Size Comparison Model

**Rule**: Simple code MUST be shorter than equivalent Rust code.

| Module Type | Keep in Rust | Migrate to Simple |
|-------------|--------------|-------------------|
| Low-level FFI | Yes | No |
| Date/time logic | No | Yes (see time.spl) |
| Config parsing | Maybe | Yes if simpler |
| Business logic | No | Yes |
| String processing | No | Yes |
| Data transformation | No | Yes |

**Example - time module**:
- Rust FFI: 666 lines (`src/rust/runtime/src/value/ffi/time.rs`)
- Simple wrapper: 130 lines (`simple/std_lib/src/time.spl`)
- **Ratio**: 5.1x shorter in Simple

---

## Current Architecture

```
Simple Executable (.spl)
    │
    ├── calls Rust FFI (extern fn rt_*)
    │   └── src/rust/runtime/src/value/ffi/
    │
    └── uses Simple stdlib
        └── simple/std_lib/src/
```

**Rust Crates (24 total, ~50k lines)**:
| Crate | Lines | Migration Target |
|-------|-------|------------------|
| sdn | 937 | Phase 1 |
| diagnostics | ~500 | Phase 2 |
| todo_db | 979 | Phase 3 |
| feature_db | 1120 | Phase 3 |
| bug_db | 831 | Phase 3 |
| test_db | 1687 | Phase 4 |
| runtime/ffi | ~5000 | Keep (FFI core) |
| parser | ~20000 | Keep (performance) |
| compiler | ~30000 | Keep (performance) |

---

## Incremental Migration Phases

### Phase 1: SDN Config Module (Week 1)

**Target**: `src/rust/sdn/src/parser.rs` (937 lines)

**Migration Strategy**:
1. Create `simple/std_lib/src/sdn.spl`
2. Keep Rust lexer as FFI (`extern fn rt_sdn_tokenize`)
3. Implement parser logic in Simple
4. Size target: < 400 lines Simple

**What to Translate**:
```
Rust (keep as FFI):
  - Lexer (tokenize)
  - Token enum
  - Basic value types

Simple (new):
  - Parser state machine
  - Error recovery
  - Value construction
  - Span tracking
```

**Enhancement**:
- Add schema validation
- Add path expressions (`config["server.port"]`)
- Add merge operations

**Size Report Template**:
```
SDN Module Migration Report
===========================
Rust before:  937 lines
Rust after:   ~200 lines (lexer FFI only)
Simple:       ~350 lines (parser + validation)
Total:        550 lines (-41%)
```

---

### Phase 2: Diagnostics Module (Week 2)

**Target**: Enhance existing i18n modules

**Current State**:
- `i18n/*.spl` - Message translation modules
- Rust diagnostics in `src/rust/diagnostics/`

**Migration Strategy**:
1. Keep Rust severity types as FFI
2. Migrate message formatting to Simple
3. Add log levels 0-10 in Simple

**What to Translate**:
```
Rust (keep as FFI):
  - Severity enum
  - Source location types
  - Terminal colors

Simple (new):
  - LogConfig struct
  - Scope filtering
  - Message formatting
  - I18n lookup
```

**Enhancement**:
```simple
# New log config in Simple
struct LogConfig:
    level: i32           # 0-10
    scopes: Dict<text, i32>  # per-scope levels

fn log(level: i32, scope: text, msg: text):
    if config.scopes[scope] ?? config.level >= level:
        rt_log_emit(level, scope, msg)
```

---

### Phase 3: DB Modules (Week 3)

**Target**: Unify todo_db, feature_db, bug_db

**Current State**:
- `src/rust/driver/src/todo_db.rs` (979 lines)
- `src/rust/driver/src/feature_db.rs` (1120 lines)
- `src/rust/driver/src/bug_db.rs` (831 lines)

**Migration Strategy**:
1. Create unified `simple/std_lib/src/db.spl`
2. Use SDN as storage format (from Phase 1)
3. Keep file I/O as FFI

**What to Translate**:
```
Rust (keep as FFI):
  - File read/write
  - Path operations
  - JSON/SDN parsing (lexer)

Simple (new):
  - Table schema
  - Query operations
  - Report generation
  - Markdown export
```

**Target Structure**:
```simple
# simple/std_lib/src/db.spl

struct Table<T>:
    name: text
    columns: List<text>
    rows: List<T>

impl Table<T>:
    fn from_sdn(path: text) -> Table<T>
    fn filter(pred: fn(T) -> bool) -> Table<T>
    fn to_markdown() -> text

# Specialized tables
type TodoTable = Table<TodoRow>
type FeatureTable = Table<FeatureRow>
type BugTable = Table<BugRow>
```

**Enhancement**:
- Cross-table joins
- Incremental updates
- Watch mode

---

### Phase 4: Test Runner Module (Week 4)

**Target**: `src/rust/driver/src/test_db.rs` (1687 lines)

**Migration Strategy**:
1. Create `simple/std_lib/src/testing/runner.spl`
2. Enhance existing `testing/*.spl` modules
3. Keep parallel execution in Rust FFI

**What to Translate**:
```
Rust (keep as FFI):
  - Process spawning
  - Parallel coordination
  - File I/O

Simple (new):
  - Test discovery
  - Result aggregation
  - Report generation
  - Progress display
```

**Enhancement**:
- Hot reload detection
- Selective re-run
- Coverage integration

---

### Phase 5: DI/AOP Configuration (Week 5)

**Target**: Create Simple-based configuration system

**Current State**:
- No unified DI container
- AOP in `src/rust/runtime/src/aop.rs`

**What to Create**:
```simple
# simple/std_lib/src/di.spl

trait Service

struct Container:
    bindings: Dict<text, fn() -> Service>
    profile: text  # test | dev | prod

impl Container:
    fn bind<T: Service>(factory: fn() -> T)
    fn get<T: Service>() -> T
    fn with_profile(name: text) -> Container
```

**Enhancement**:
- Profile-based configuration
- Lazy initialization
- Scope management

---

## Existing Simple Modules to Enhance

| Module | Current Lines | Enhancement |
|--------|---------------|-------------|
| `time.spl` | 130 | Add Duration type, formatting |
| `set.spl` | ~100 | Add set operations |
| `map.spl` | ~100 | Add merge, filter |
| `testing/mocking.spl` | ~200 | Add auto-mock |
| `testing/benchmark.spl` | ~150 | Add comparison |

---

## FFI Contract

**Naming Convention**:
```
rt_{module}_{operation}

Examples:
  rt_sdn_tokenize(source: text) -> List<Token>
  rt_log_emit(level: i32, scope: text, msg: text)
  rt_db_read_file(path: text) -> text
  rt_db_write_file(path: text, content: text)
```

**Type Mapping**:
| Rust | Simple | FFI Signature |
|------|--------|---------------|
| `String` | `text` | `*const c_char` |
| `i64` | `i64` | `i64` |
| `f64` | `f64` | `f64` |
| `Vec<T>` | `List<T>` | Serialized |
| `HashMap<K,V>` | `Dict<K,V>` | Serialized |

---

## Size Tracking Template

After each module migration, create report:

```markdown
# {Module} Migration Report

## Before
- Rust lines: {N}
- Simple lines: {M}

## After
- Rust FFI lines: {A}
- Simple lines: {B}

## Metrics
- Total reduction: {(N+M) - (A+B)} lines ({percent}%)
- Simple/Rust ratio: {B/A}
- Features added: {list}

## Verification
- [ ] All tests pass
- [ ] Performance acceptable
- [ ] Size target met (Simple < Rust original)
```

---

## Phase 1 Implementation Tasks

### Task 1.1: SDN Tokenizer FFI
- Extract tokenizer from `sdn/src/parser.rs`
- Create `extern fn rt_sdn_tokenize()`
- Target: ~150 lines Rust

### Task 1.2: SDN Parser in Simple
- Create `simple/std_lib/src/sdn.spl`
- Implement `parse()` function
- Target: < 300 lines Simple

### Task 1.3: SDN Validation
- Add schema types
- Add error messages
- Target: ~50 lines Simple

### Task 1.4: Size Report
- Generate migration report
- Verify size reduction
- Update this document

---

## Success Criteria

1. **Size**: Simple code shorter than replaced Rust
2. **Features**: Same or better functionality
3. **Performance**: No regression > 10%
4. **Tests**: All existing tests pass
5. **Documentation**: Migration report for each phase

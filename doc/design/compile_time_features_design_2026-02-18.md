# Compile-Time Features Design & Plan
# 2026-02-18

**Status:** ✅ COMPLETE — Implemented 2026-02-18
**Based on research:** `doc/research/introspection_phantom_types_2026-02-17.md`
**Based on research:** `doc/research/missing_language_features_2026-02-17.md`

---

## Part 1: Implementation Status Audit

### 1.1 Fully Implemented — Parser + Runtime Verified

These keywords exist in `src/core/tokens.spl`, are in `keyword_lookup()`, are parsed, and have test coverage.

| Keyword / Feature | Token | Parser fn | Test file |
|-------------------|-------|-----------|-----------|
| `defer` | TOK_KW_DEFER (186) | `stmt_defer_stmt()` | `test/unit/parser/defer_spec.spl` |
| `errdefer` | TOK_KW_ERRDEFER (187) | `stmt_errdefer_stmt()` | `test/unit/parser/errdefer_spec.spl` |
| `where` | TOK_KW_WHERE (189) | constraint clause in fn decl | `test/integration/mixin_type_inference.spl` |
| `lazy` | TOK_KW_LAZY (194) | delegates to `parse_val_decl_stmt()` | `test/unit/std/given_working_spec.spl` |
| `do` | TOK_KW_DO (195) | `expr_do_block()` | `test/unit/parser/do_block_spec.spl` |
| `extend` | TOK_KW_EXTEND (196) | `parse_impl_decl()` | `test/unit/parser/extend_spec.spl` |
| `newtype` | TOK_KW_NEWTYPE (198) | creates struct wrapper | `test/unit/parser/newtype_spec.spl` |
| `dyn` | TOK_KW_DYN (199) | `TYPE_NAMED_BASE` / `TYPE_ANY` | `test/unit/parser/dyn_trait_spec.spl` |
| `if val` / `while val` | (val token) | pattern binding | `test/feature/parser_control_flow_spec.spl` |
| Numeric separators | (lexer) | `1_000_000`, `0xFF_FF` | — |
| `..spread` | (token) | struct update syntax | — |
| Backtick atoms | TOK_BACKTICK_IDENT (193) | `` `atom `` | — |
| Generics `<T>` | (parser) | monomorphization | `test/unit/*generics*_spec.spl` |

**Conclusion:** All 8 "new" keywords found via token scan are fully implemented. No orphaned tokens.

### 1.2 Annotation Intrinsics — NOT YET Implemented

These use the `@` prefix and need no new keyword tokens, but are not yet resolved to values.

| Annotation | Current state | Needed |
|------------|---------------|--------|
| `@file` | Parses as identifier after `@` | Resolve to `text` at compile time |
| `@line` | Parses as identifier after `@` | Resolve to `i64` at compile time |
| `@function` | Parses as identifier after `@` | Resolve to `text` at compile time |
| `@static_assert(cond, msg)` | Parses as fn call after `@` | Evaluate at type-check time |
| `@must_use` | Parses as annotation on fn | Check call site in type checker |
| `@phantom` | Parses as annotation on struct | Mark struct as zero-size type param |

### 1.3 Proposed Features — Not Implemented

| Feature | New keyword? | Research section |
|---------|-------------|-----------------|
| `keyof T` | YES — `keyof` | Missing features §29 |
| Mapped types `{for K in keyof T: K: T[K]}` | No (uses `keyof`) | Missing features §30 |
| Mode D error return traces | No (uses `?`) | Introspection doc §4 |
| Phantom types | No (uses `@phantom`) | Introspection doc §2 |
| Format string validation | No | Introspection doc §1 |
| Frame pointer traces (Mode B) | No | Introspection doc §4 |
| Exhaustiveness depth | No | Introspection doc §1 |

---

## Part 2: O(1) Parsing Analysis

### 2.1 Current State

`keyword_lookup()` in `src/core/tokens.spl` (lines 313–369) uses **56 sequential string comparisons**:

```
keyword_lookup(name):
    if name == "fn":    return TOK_KW_FN      # comparison 1
    if name == "val":   return TOK_KW_VAL     # comparison 2
    ...
    if name == "dyn":   return TOK_KW_DYN     # comparison 56
    TOK_IDENT                                  # default
```

**Complexity per identifier:**
- Best case: O(1) — `fn` matched on first check
- Worst case: O(56 × len) — unknown identifier, all 56 comparisons fail
- Average case: O(28 × len) — roughly middle of chain

**Parser dispatch** (`par_kind` integer comparison): **O(1)** — already optimal. Once `keyword_lookup` returns an integer token kind, all parser decisions are O(1) integer comparisons.

### 2.2 Impact Assessment

For 56 keywords averaging 5 chars, worst-case per identifier = 280 character comparisons.
At 1 billion char comparisons/sec, 1 million identifiers = **280ms per million identifiers** in worst case.
For typical programs (10K–100K identifiers), the cost is **~3–28ms** — negligible.

**Adding `keyof`** (1 keyword) makes it 57 checks. Impact: +1.8%. Not a concern.

### 2.3 O(1) Optimization — First-Character Dispatch

While not urgently needed, a first-char dispatch reduces the average from O(28) to O(3) comparisons by grouping by first letter. This is the recommended optimization when adding more keywords.

**Keyword distribution by first character (current 56 keywords):**

| First char | Keywords | Count |
|-----------|----------|-------|
| `a` | and, asm, async, await | 4 |
| `b` | break | 1 |
| `c` | case, class, const, continue | 4 |
| `d` | defer, do, dyn | 3 |
| `e` | elif, else, enum, errdefer, export, extend, extern | 7 |
| `f` | false, fn, for | 3 |
| `i` | if, impl, implements, import, in, is | 6 |
| `k` | *(none yet)* keyof proposed | — |
| `l` | lazy, loop | 2 |
| `m` | match, me | 2 |
| `n` | newtype, nil, not | 3 |
| `o` | or | 1 |
| `p` | pass, pass_do_nothing, pass_dn, pass_todo, pub | 5 |
| `r` | return | 1 |
| `s` | self, spawn, static, struct | 4 |
| `t` | trait, true, type | 3 |
| `u` | use | 1 |
| `v` | val, var | 2 |
| `w` | where, while | 2 |
| `y` | yield | 1 |

**Proposed `keyword_lookup` structure:**

```simple
fn keyword_lookup(name: text) -> i64:
    if name.len() == 0: return TOK_IDENT
    val c0 = name[0]        # O(1) — first character
    if c0 == "f":
        if name == "fn":    return TOK_KW_FN
        if name == "for":   return TOK_KW_FOR
        if name == "false": return TOK_KW_FALSE
        return TOK_IDENT
    if c0 == "i":
        if name == "if":         return TOK_KW_IF
        if name == "in":         return TOK_KW_IN
        if name == "impl":       return TOK_KW_IMPL
        if name == "import":     return TOK_KW_IMPORT
        if name == "implements": return TOK_KW_IMPLEMENTS
        if name == "is":         return TOK_KW_IS
        return TOK_IDENT
    # ... etc for each first character
    TOK_IDENT
```

**Result:** Average comparisons drop from O(28) to O(3). Worst case per group (7 keywords for 'e') = O(7).

**Adding `keyof`:** Group 'k' has 1 keyword → single comparison after first-char check = O(1).

### 2.4 Annotation Intrinsics Are O(1) By Design

`@file`, `@line`, `@function`, `@static_assert`, `@must_use`, `@phantom` use the `@` symbol already tokenized separately. The subsequent identifier is parsed as `TOK_IDENT`, then the annotation dispatcher resolves the name. No new keywords added to `keyword_lookup()`. **These are truly O(1)** (fixed string equality after `@`).

---

## Part 3: Phased Implementation Plan

### Phase 1 — Zero-Cost Compile-Time Intrinsics (Do First)

**Goal:** Core introspection primitives with zero runtime overhead. No new keywords.
**Effort:** Medium. All implemented in the type checker / AST lowering stage.

#### 1.1 Source Location Constants (`@file`, `@line`, `@function`)

**What:** Compile-time constants replaced with their string/integer values at compile time.

```simple
fn assert_positive(x: i64):
    @static_assert(x > 0, "Expected positive, got {x} at {@file}:{@line}")
```

**Design:**
- Parser: `@file`, `@line`, `@function` already parse as annotation identifiers
- Type checker: Recognize these 3 annotation names as intrinsic expressions
- Lowering: Replace `@file` → `TEXT_LIT(current_file)`, `@line` → `INT_LIT(current_line)`, `@function` → `TEXT_LIT(current_fn_name)`
- No runtime cost: resolved entirely during compilation
- Integration point: `src/core/parser.spl` annotation handling + `src/core/interpreter/eval.spl` constant folding

**Implementation files:**
- `src/core/parser.spl` — recognize `@file`/`@line`/`@function` in expression position
- `src/core/interpreter/eval.spl` — resolve to constants during eval
- `src/std/intrinsics.spl` — NEW: document the intrinsic set

**Tests:** `test/unit/core/source_location_spec.spl`

#### 1.2 Static Assert (`@static_assert`)

**What:** Compile-time assertion that fails with a human-readable message.

```simple
@static_assert(SIZE_BYTES > 0, "Buffer size must be positive")
@static_assert(keyof Config contains "host", "Config must have 'host' field")
```

**Design:**
- Parser: `@static_assert(cond, msg)` already parses as annotated function call
- Type checker: Evaluate `cond` at compile time; if `false`, emit diagnostic with `msg`
- Constraints: `cond` must be a constant expression (literal, `@file`, `keyof`, `len()` of literal array)
- Soft start: Only evaluate when condition is trivially constant; skip silently if runtime-dependent

**Implementation files:**
- `src/core/interpreter/eval.spl` — constant expression evaluator
- `src/core/compiler/driver.spl` — emit compile error from static assert failure
- `src/std/intrinsics.spl` — export `@static_assert` behavior docs

**Tests:** `test/unit/core/static_assert_spec.spl`

#### 1.3 Exhaustiveness Checking Improvements

**What:** Warn when `match` is not exhaustive over enum variants.

```simple
enum Status: Ok, Warn, Error

fn handle(s: Status):
    match s:
        case Status.Ok: ...
        case Status.Warn: ...
    # COMPILE WARNING: Status.Error not handled
```

**Design:**
- Type checker: collect all enum variants; check all `case` arms; warn on missing
- Integration: `src/core/parser.spl` already builds match AST; add variant coverage check in eval
- `case _:` disables the warning (wildcard = explicit "catch all")
- Error format: `warning: non-exhaustive match on 'Status' — missing: Error`

**Implementation files:**
- `src/core/interpreter/eval.spl` — track enum variants per type
- Add `match_exhaustive_check()` helper

**Tests:** `test/unit/core/exhaustiveness_spec.spl`

---

### Phase 2 — Error Propagation Traces (Mode D, Zig-Style)

**Goal:** Track the exact path `?` propagates through. Zero cost on success path.
**Effort:** Medium-high. Requires changes to `?` operator semantics.

#### 2.1 Design

Zig's approach: each `try`/`?` site records its source location into a **fixed-size stack-allocated buffer** only when an error actually occurs (lazy, error-path only).

```simple
fn read_config(path: text) -> text?:
    val raw = file_read(path)?     # Records site if file_read fails
    val parsed = parse(raw)?       # Records site if parse fails
    parsed

fn main():
    val config = read_config("app.sdn")?  # Records site if read_config fails
```

**On failure, error trace printed:**
```
Error propagation trace:
  src/app/config.spl:14  file_read() returned nil
  src/app/config.spl:15  parse() failed
  src/app/main.spl:8     read_config() returned nil
```

**Data structures:**

```simple
struct ErrorSite:
    file: text         # compile-time constant (zero runtime cost)
    line: i64          # compile-time constant
    function: text     # compile-time constant

struct ErrorTrace:
    sites: [ErrorSite]  # fixed capacity, grows on error path only
    depth: i64

var _current_error_trace: ErrorTrace = ErrorTrace(sites: [], depth: 0)
```

**`?` operator semantics:**
- Current: `expr?` → if nil, propagate nil upward
- New: `expr?` → if nil, append `ErrorSite(@file, @line, @function)` to `_current_error_trace`, then propagate nil

**Key properties:**
- **Zero cost on success:** append only executes when nil is encountered
- **No heap allocation:** sites array has fixed max depth (configurable, default 32)
- **Opt-in at top level:** `error_trace_begin()` / `error_trace_end()` wraps entry points
- **Works in release mode:** compile-time constants need no DWARF

**Implementation files:**
- `src/std/error_trace.spl` — NEW: `ErrorSite`, `ErrorTrace`, trace management
- `src/core/parser.spl` — `?` operator desugaring to include trace append
- `src/core/interpreter/eval.spl` — `?` eval path calls `error_trace_push()`

**Tests:** `test/unit/std/error_trace_spec.spl`

---

### Phase 3 — `@must_use` and Phantom Types

**Goal:** Enforce correct API usage at compile time. Zero runtime cost.
**Effort:** Medium. Annotation-based, no new keywords.

#### 3.1 `@must_use` Annotation

**What:** Functions annotated `@must_use` emit a compile warning when their return value is discarded.

```simple
@must_use
fn parse_int(s: text) -> i64?:
    ...

parse_int("42")       # WARNING: return value ignored, function is @must_use
val n = parse_int("42")  # OK
```

**Design:**
- Parser: Already parses `@must_use` as annotation on `fn` declarations
- Type checker: When a function call appears as a statement (not assigned), check if callee has `@must_use`; if yes, emit warning
- Existing infrastructure: `eval_get_warnings()` in `src/core/interpreter/eval.spl` — already used for ignored return value warnings
- `@must_use` is the **opt-in explicit version** of the existing ignored-return warning system

**Implementation files:**
- `src/core/parser.spl` — store `@must_use` in fn declaration AST node
- `src/core/interpreter/eval.spl` — check annotation in `eval_function_call()`
- `src/std/intrinsics.spl` — document `@must_use`

**Tests:** `test/unit/core/must_use_spec.spl`

#### 3.2 Phantom Types (`@phantom struct`)

**What:** Zero-size type parameter markers for compile-time state tracking.

```simple
@phantom struct Connected
@phantom struct Disconnected

struct Socket<State>:
    fd: i64

fn connect(s: Socket<Disconnected>) -> Socket<Connected>:
    # ... actually connect
    Socket(fd: s.fd)

fn send(s: Socket<Connected>, data: [u8]):
    # ... send data

# Usage:
val raw = Socket<Disconnected>(fd: 0)
val live = connect(raw)
send(live, [1, 2, 3])   # OK
send(raw, [1, 2, 3])    # COMPILE ERROR: Socket<Disconnected> is not Socket<Connected>
```

**Design:**
- `@phantom struct Name` declares a zero-size marker type
- `struct Foo<State>` stores `State` as a type parameter (already supported via generics)
- Functions constrain on specific State via type signatures
- The type checker enforces substitution — already done by generic monomorphization
- `@phantom` annotation tells the compiler: "this struct has no data fields; it exists only as a type tag"

**Key insight:** The existing generic system (`src/core/generic_runtime.spl`) already does monomorphization. `Socket<Connected>` and `Socket<Disconnected>` are already distinct types. The only new work is:
1. `@phantom` annotation declaration — marks struct as zero-size (no fields needed)
2. Error messages using `@state_description` to make type errors human-readable

**State constraint syntax (optional, Phase 3b):**
```simple
@state_set SocketState = Connected | Disconnected

struct Socket<State: SocketState>:
    fd: i64
```

**Implementation files:**
- `src/core/parser.spl` — recognize `@phantom` on struct declarations
- `src/core/generic_runtime.spl` — skip field construction for `@phantom` structs
- `src/std/phantom.spl` — NEW: common phantom marker types (`Owned`, `Borrowed`, `ReadOnly`, etc.)

**Tests:** `test/unit/core/phantom_types_spec.spl`

---

### Phase 4 — `keyof` and Mapped Types

**Goal:** Compile-time type-level field operations. Zero runtime cost.
**Effort:** High. Requires new keyword + type-level evaluation.
**New keyword:** `keyof` — added to `keyword_lookup()` in group 'k' (unique, O(1) after first-char check).

#### 4.1 `keyof T` Type Operator

**What:** Produces a compile-time union of the literal field names of a struct type.

```simple
struct Config:
    host: text
    port: i64
    timeout: i64

keyof Config   # → "host" | "port" | "timeout"  (compile-time text union)

fn get_field(cfg: Config, key: keyof Config) -> text:
    match key:
        case "host":    cfg.host
        case "port":    text(cfg.port)
        case "timeout": text(cfg.timeout)
    # exhaustiveness checker verifies all keyof Config variants are covered
```

**Design:**
- Token: `TOK_KW_KEYOF` — add to `tokens.spl` and `keyword_lookup()` group 'k'
- Parser: `parse_type_expr()` recognizes `keyof` as a prefix type operator
- Type checker: Resolves `keyof T` to a union of `TEXT_LIT(field_name)` for each field in `T`
- Use in match: `match key:` with `case "field_name":` can be exhaustiveness-checked against `keyof T`
- Interaction with `@static_assert`: `@static_assert(keyof Config contains "host", "...")`

**Implementation files:**
- `src/core/tokens.spl` — add `TOK_KW_KEYOF = 200`
- `src/core/tokens.spl` `keyword_lookup()` — add `if name == "keyof": return TOK_KW_KEYOF`
- `src/core/parser.spl` — `parse_type_expr()` handles `keyof` prefix
- `src/core/interpreter/eval.spl` — resolve `keyof T` to field name list at eval time

**Tests:** `test/unit/core/keyof_spec.spl`

#### 4.2 Mapped Types

**What:** Type-level transformations applied to all fields of a struct, producing a new struct type.

```simple
# Standard library mapped types:
type Partial<T>   = struct { for K in keyof T: K: T[K]? }    # All fields optional
type Readonly<T>  = struct { for K in keyof T: K: T[K] }     # Same, but val fields
type Stringify<T> = struct { for K in keyof T: K: text }     # All fields become text
type Pick<T, Keys in keyof T> = struct { for K in Keys: K: T[K] }    # Field subset
type Omit<T, Keys in keyof T> = struct { for K in (keyof T - Keys): K: T[K] }  # Exclude
```

**Design:**
- Requires `keyof` (Phase 4.1)
- Type expression syntax: `struct { for K in keyof T: K: T[K] }` in type position
- Type checker: Expand `for K in keyof T` at compile time into concrete field list
- Standard library: `src/std/types/mapped.spl` — common mapped type definitions
- No runtime cost: all expansion happens at compile time

**Implementation files:**
- `src/core/parser.spl` — type expression parser handles `{ for K in keyof T: K: T[K]? }`
- `src/core/interpreter/eval.spl` — expand mapped types at type-check time
- `src/std/types/mapped.spl` — NEW: `Partial<T>`, `Readonly<T>`, `Stringify<T>`, `Pick`, `Omit`

**Tests:** `test/unit/core/mapped_types_spec.spl`

---

### Phase 5 — Stack Trace Modes (Mode A + Mode B)

**Goal:** Optional stack traces for debugging and error reporting.
**Effort:** High. Requires SFFI to runtime debug facilities.

#### 5.1 Mode A — DWARF Post-Mortem (Zero Runtime Cost)

**What:** Stack trace available on program crash, via DWARF debug info.
- Build with debug symbols: `bin/simple build --debug-symbols`
- On panic: runtime calls `rt_capture_dwarf_trace()` (SFFI to libunwind/libbacktrace)
- Zero runtime cost during normal execution

**Missing piece:** `rt_capture_stack_trace()` extern fn is declared in `src/std/report/runtime/panic.spl` but not yet implemented in the runtime binary.

**Implementation:**
- Add SFFI: `extern fn rt_capture_stack_trace() -> [text]` in runtime binary
- Wire into `panic.spl` `PanicReport.capture()`

#### 5.2 Mode B — Frame Pointer Preservation (~1-3% overhead)

**What:** Preserve frame pointers to enable fast stack unwinding in production.
- Build flag: `bin/simple build --frame-pointers`
- Runtime: `rt_fast_stack_trace()` walks frame pointer chain
- Use case: low-overhead stack traces in `assert_log()` in production

---

## Part 4: Keyword Dispatch Optimization Plan

### 4.1 Recommended Change to `keyword_lookup()`

Rewrite `src/core/tokens.spl` `keyword_lookup()` to dispatch on first character before comparing full strings. This reduces worst-case from 56 to 7 comparisons (worst group is 'e' with 7 keywords).

**When to do this:** When keyword count reaches 70+ OR when a profiler shows keyword lookup is hot (unlikely). For now, document the plan; implement when adding `keyof`.

### 4.2 Adding `keyof` to the Keyword Table

**Minimal change** (when `keyof` is implemented in Phase 4):

1. `src/core/tokens.spl` line ~200: add `val TOK_KW_KEYOF: i64 = 200`
2. `src/core/tokens.spl` `keyword_lookup()`: append `if name == "keyof": return TOK_KW_KEYOF`
3. The 'k' group has zero existing keywords — `keyof` is O(1) to look up after first-char check
4. Optionally apply first-char optimization to the entire function at the same time

### 4.3 Annotation Dispatch (Always O(1))

Features implemented as annotations (`@file`, `@line`, `@function`, `@static_assert`, `@must_use`, `@phantom`) never touch `keyword_lookup()`. The parser handles `@` as `TOK_AT`, then reads the next `TOK_IDENT`. The annotation name is looked up in a fixed table of known intrinsics. This is O(1) regardless of how many annotations exist.

---

## Part 5: Summary Priority Table

| Phase | Feature | New keyword? | O(1)? | Runtime cost | Effort |
|-------|---------|-------------|-------|--------------|--------|
| 1 | `@file`, `@line`, `@function` | No | ✅ O(1) annotation | Zero | Small |
| 1 | `@static_assert` | No | ✅ O(1) annotation | Zero | Small |
| 1 | Exhaustiveness checking | No | ✅ O(1) in type checker | Zero | Medium |
| 2 | Mode D error return traces | No (uses `?`) | ✅ O(1) per site | Zero on success | Medium |
| 3 | `@must_use` | No | ✅ O(1) annotation | Zero | Small |
| 3 | `@phantom struct` | No | ✅ O(1) annotation | Zero | Medium |
| 4 | `keyof T` | YES — `keyof` | ✅ O(1) with first-char | Zero | High |
| 4 | Mapped types | No (uses `keyof`) | ✅ O(1) in type checker | Zero | High |
| 5 | Mode A DWARF traces | No | ✅ O(1) on crash | Zero normal | Medium |
| 5 | Mode B frame pointers | No | ✅ O(1) per frame walk | ~1-3% | Medium |

**All proposed features are O(1) in parser dispatch (par_kind integer comparison).** The only O(n) component is `keyword_lookup()` during lexing, which adds at most 1 comparison per new keyword and is already negligible for current scale.

---

## Part 6: File Creation Plan

### New files to create (in implementation order):

```
src/std/intrinsics.spl          # @file, @line, @function, @static_assert, @must_use docs + impls
src/std/error_trace.spl         # ErrorSite, ErrorTrace, error_trace_begin/end/push
src/std/phantom.spl             # Common @phantom markers: Owned, Borrowed, ReadOnly, WriteOnly
src/std/types/mapped.spl        # Partial<T>, Readonly<T>, Stringify<T>, Pick<T,K>, Omit<T,K>
```

### Existing files to modify (in implementation order):

```
src/core/tokens.spl             # Phase 4: add TOK_KW_KEYOF; optional: first-char optimization
src/core/parser.spl             # Phase 1: @file/@line/@function; Phase 4: keyof type expr
src/core/interpreter/eval.spl   # Phase 1: intrinsic resolution, @static_assert eval, @must_use check
                                 # Phase 2: ? operator trace push; Phase 3: @phantom handling
                                 # Phase 4: keyof expansion
src/core/generic_runtime.spl    # Phase 3: skip field construction for @phantom structs
```

### New test files:

```
test/unit/core/source_location_spec.spl   # @file, @line, @function
test/unit/core/static_assert_spec.spl     # @static_assert
test/unit/core/exhaustiveness_spec.spl    # match exhaustiveness
test/unit/std/error_trace_spec.spl        # Mode D error propagation traces
test/unit/core/must_use_spec.spl          # @must_use annotation
test/unit/core/phantom_types_spec.spl     # @phantom struct + generic state machines
test/unit/core/keyof_spec.spl             # keyof T operator
test/unit/core/mapped_types_spec.spl      # Partial<T> etc.
```

---

## Part 7: Implementation Sequence

```
Week 1: Phase 1 (small, high value)
  - @file, @line, @function constants (2 days)
  - @static_assert evaluation (2 days)
  - Exhaustiveness check improvements (1 day)

Week 2: Phase 2 (medium, highest safety value)
  - ErrorSite / ErrorTrace struct in std (1 day)
  - ? operator desugaring to trace push (2 days)
  - error_trace_begin/end API + tests (2 days)

Week 3: Phase 3 (medium, type safety)
  - @must_use annotation check (1 day)
  - @phantom struct declaration (2 days)
  - Generic state machine patterns + tests (2 days)

Week 4: Phase 4 (high effort, powerful)
  - keyof token + keyword_lookup update (1 day)
  - keyof type expression parsing (2 days)
  - keyof type checking + expansion (2 days)

Week 5: Phase 4 continued
  - Mapped types type expression syntax (2 days)
  - Standard mapped types library (2 days)
  - Integration tests + docs (1 day)

Later: Phase 5 (requires runtime binary changes)
  - rt_capture_stack_trace() SFFI (coordinate with runtime)
  - Mode A + Mode B testing
```

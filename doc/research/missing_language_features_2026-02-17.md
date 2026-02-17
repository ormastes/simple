# Missing Language Features Research
**Date:** 2026-02-17 (Safety Profile Review added 2026-02-17)
**Scope:** Useful language features absent from Simple, compared to Rust, Python, Ruby, Erlang, Zig, TypeScript, Go, Kotlin, Swift, Haskell, Julia
**Excluded (by design):** Exceptions/try-catch, class inheritance
**Companion doc:** Phantom types, introspection tiers, stack traces, compile-time checking → [`introspection_phantom_types_2026-02-17.md`](introspection_phantom_types_2026-02-17.md)

---

## Executive Summary

Simple has a solid foundation: generics, pattern matching, traits, Option/Result, async/await, closures, comprehensions, pipeline operators, effect annotations, and a rich standard library. This document catalogs **useful practical features** missing from Simple that exist in peer languages, organized by impact and implementation complexity.

This document has been reviewed through a **JSF AV C++ (F-35/JSF++)** and **NASA "Power of Ten"** safety-critical lens. Each feature now includes a safety profile note. Features are either safety-profile friendly, must be constrained, or are gated/postponed.

---

## Simple Safety Profile (JSF AV C++ / NASA Power of Ten)

### Baseline Constraints

If the `--profile=safety` (or `@profile(safety)` annotation) is active, the following baseline restrictions apply:

| Constraint | Rationale |
|-----------|-----------|
| No recursion (or bounded + proven) | Stack overflow risk; JSF bans unbounded recursion |
| No heap allocation after init | Determinism; fragmentation; NASA rule |
| No exceptions | JSF AV C++ explicitly bans; use Result/Option instead |
| No hidden global init order | Cross-unit init order undefined in JSF/C++ |
| Bounded loops (statically checkable) | Power of Ten rule 2 |
| Simple, analyzable control flow | No labels/goto/continue/break abuse |
| No dynamic dispatch by default | Harder static reasoning; timing unpredictability |

### Profile-Gated Features Summary

| Category | Safe Profile OK | Must Be Constrained | Disallowed in Safe Profile |
|----------|----------------|--------------------|-----------------------------|
| String formatting | ✅ compile-time checked | alloc-free APIs only | unchecked format strings |
| Labeled break | ⚠️ break-label only | no continue-label | arbitrary label control |
| errdefer | ✅ structured LIFO | side-effect constrained | hidden allocation in body |
| Struct update | ✅ Copy/POD only | explicit clone() for heap | heap-backed struct update |
| @derive | ✅ Eq/Ord/Copy/Debug | emit-expanded audit | derives implying allocation |
| Extension methods | ⚠️ explicit-import only | module-scoped only | global open-class |
| Union types (type-OR) | ✅ tagged sum sugar | exhaustive match required | untagged/implicit coercions |
| C-style memory union | ⚠️ unsafe+private+struct-local | explicit `unsafe` access only | global scope, public fields, implicit coercions |
| Default trait methods | ✅ if alloc-free | explicit @not_safety | allocation/logging in body |
| Associated types | ✅ with complexity limits | monomorphization bounds | type-level computation explosions |
| Atom/symbol | ✅ compile-time fixed set | ROM table only | runtime-created atoms |
| Comptime | ⚠️ total/terminating | step limits enforced | unbounded recursion/I/O |
| Newtype | ✅ strongly recommended | — | — |
| Exhaustiveness | ✅ mandatory default | explicit opt-out annotation | silent partial match |
| Result/Option chains | ✅ bounded length | named helpers for complex lambdas | stringly-typed errors |
| TCO / tailrec | ⚠️ explicit opt-in only | bounded iterations | general recursion |
| Supervision trees | ⚠️ library only | explicit restart budgets | unrestricted restart |
| Pattern guards | ✅ side-effect-free | comparisons/range checks only | stateful guards |
| Multiline strings | ✅ explicit indent rules | no embedded DSLs | invisible whitespace |
| Module aliasing | ✅ explicit + traceable | compiler emits provenance | wildcard re-exports |
| Lazy init | ❌ disallowed | preallocated + single-thread only | runtime heap on first access |
| Keyword-only params | ✅ strongly recommended | — | — |
| String builder | ⚠️ fixed-capacity only | caller-provided buffer | unbounded growth |
| Trait objects (dyn) | ❌ disallowed by default | explicit `dyn` + no downcasts | RTTI/downcasts |
| Numeric separators | ✅ enforced (warn) | mandatory for N+ digit literals | ambiguous grouping |
| Module init/teardown | ⚠️ topological order required | declared dependency graph | implicit ordering |
| Conditional compilation | ⚠️ platform/FFI only | all configs tested in CI | untested paths |
| Phantom types | **POSTPONED** | introspection + compile-time dict | type wizardry |

---

## Grammar & Parser Compatibility Analysis

Simple uses a **hand-written recursive descent LL(1) parser** with LL(2) lookahead in the lexer only. Key constraints:
- Parser commits to a production after seeing **one token** — no backtracking
- All multi-character operator disambiguation (`..`, `|>`, `??`, etc.) happens in the **lexer** using `lex_peek()`
- `|` serves double duty: bitwise OR (prec 4) in expressions, pattern separator in `match` arms
- `@` is the annotation prefix — used in `@derive`, `@tailrec`, `@when`, etc.
- `..` is `TOK_DOTDOT` — infix only (range); prefix `..p` not currently valid
- `as` keyword exists but is **not wired** into `use`/`export` productions (causes parse error)

### Grammar Status by Feature

| Feature | Grammar Status | Issue / Action Required |
|---------|---------------|------------------------|
| 1. String format specifiers | ✅ Clean | Lexer change inside `{…}` string scan; `:` after expr = format spec |
| 2. Labeled break | ⚠️ **Conflict** | `IDENT:` at stmt level is invalid; needs `'label:` syntax — see section |
| 3. errdefer | ✅ Clean | New keyword; same production as `defer` |
| 4. Struct update `..p` | ✅ Clean (scoped) | `..` prefix valid inside `()` arg list only; add prefix branch in arg parser |
| 5. @derive | ✅ Clean | Existing `@IDENT(…)` annotation syntax |
| 6. extend | ✅ Clean | New keyword at module level |
| 7a. Type-OR `\|` | ✅ Clean | `\|` inside `parse_type()` is unambiguous; `parse_type()` never called from expr |
| 7b. unsafe union | ✅ Clean | New keywords `unsafe`/`union`; struct-body parser extension |
| 8. Default trait methods | ✅ Clean | Trait body already accepts `fn` blocks; add optional body |
| 9. Associated types | ✅ Clean | `type` keyword already exists; allow inside trait/impl body |
| 10. Atom `` ` `` | ✅ Clean | Backtick unused in lexer; new token `TOK_BACKTICK_IDENT` |
| 11. comptime/const fn | ✅ Clean | New keywords `const`/`comptime` at declaration level |
| 12. newtype | ✅ Clean | New keyword `newtype IDENT = type` |
| 13. Exhaustiveness | ✅ Clean | Compiler analysis pass; zero grammar change |
| 14. @tailrec | ✅ Clean | Existing annotation syntax |
| 15. Supervision trees | ✅ Clean | Library only; no grammar change |
| 16a. Or-patterns `\|` | ✅ Clean | Already implemented in match (`case X \| Y:`) |
| 16b. Bind `@` pattern | ⚠️ **Conflict** | `@` is annotation prefix; use `as` keyword instead — see section |
| 16c. Guards `if` | ✅ Clean | `case x if cond:` unambiguous after pattern |
| 17. Module aliasing | ⚠️ **Incomplete** | `as` keyword exists but not wired in `parse_use_decl()`; parser fix only |
| 18. const | ✅ Clean | New keyword `const IDENT: type = expr` |
| 19. Multi-line strings | ✅ Clean | Lexer bug fix; no grammar change |
| 20. `do` block expr | ⚠️ **Non-trivial** | Blocks are stmt-level only; `do:` as expression requires block-as-expr support |
| 21. where clauses | ⚠️ **Conflict** | `E: Clone:` — final `:` ambiguous; use `+` for multi-bound, never `,` within one param — see section |
| 22. lazy val | ✅ Clean | New keyword `lazy` before `val`/`var` |
| 23. Keyword-only `~` | ✅ Clean | `~` unused standalone; new param prefix token |
| 24. String builder | ✅ Clean | Pure stdlib; no grammar change |
| 25. dyn trait | ✅ Clean | New keyword `dyn` inside `parse_type()` |
| 26. Numeric separators | ✅ Clean | Lexer: allow `_` between digits in numeric literal scan |
| 27. Module init/teardown | ⚠️ **Conflict** | `init`/`teardown` as keywords break existing code; use `@init`/`@teardown` annotations instead |
| 28. Conditional `@when` | ✅ Clean | Existing annotation syntax |

### Features Requiring Syntax Correction

**Feature 2 — Labeled break:** `outer: for` conflicts — `IDENT ':'` at statement level is currently a parse error. Use `'label` prefix (like Rust) since `'` is not currently a lexer token:
```simple
'outer: for row in rows:       # label declared with ' prefix
    for col in row:
        if found(col): break 'outer   # no continue-label in safety profile
```

**Feature 16b — Pattern binding:** `name @ pattern` conflicts — `@` is the annotation prefix token. Use `as` keyword:
```simple
match value:
    x as large if large > 1000: handle_large(x)   # bind AND guard
    n as (10 | 20 | 30): handle_special(n)
```
> **Future consideration:** Reserve `as` for both pattern binding AND type cast (`x as i64`). Both appear in distinct syntactic positions (match pattern vs expression), so they do not conflict with each other — `as` after a match-arm expression = bind, `as` after a general expression = type cast. O(1) in both contexts.

**Feature 20 — `do` block:** O(1) — `do` keyword is unused and unambiguous as expression start. Non-trivial implementation (block-as-expr in the parser) but no lookahead issue.

**Feature 21 — `where` clauses:** Deeper analysis reveals a `:` ambiguity. In `where T: Display, E: Clone:`, after parsing `Clone`, the parser sees `:` and must decide: is this `Clone: AnotherBound` (bound separator for `Clone` itself) or the body-start `:` for the function? This requires LL(2) **at the parser level**, which Simple does not support.

Fix: use `+` for all multiple bounds on one type parameter, and `,` only between different type parameters. Then `:` never appears mid-constraint — only as bound-start after `where`/`,` and as body-start after the last bound name:
```simple
# WRONG (ambiguous — where does the where clause end?):
fn f<T, E>(x: T, h: E) where T: Display, T: Clone, E: Handler:
#                                                   ↑ is this E's bound or body start?

# CORRECT (O(1) — '+' for multiple bounds, ':' only at body start):
fn f<T, E>(x: T, h: E) where T: Display + Clone, E: Handler:
#                  '+'s = more bounds;  ',' = next param;  final ':' = body start ✅
```
After any bound name (`Clone`, `Handler`), the only valid next tokens are: `+` (more bounds), `,` (next constraint), or `:` (body start — always at end of line). Unambiguous O(1).

**Feature 27 — Module init/teardown:** `init` and `teardown` as new global keywords would break any existing function or variable named `init`/`teardown`. Use annotation syntax instead — no new keywords needed:
```simple
@init
fn database_setup():
    connection = db_connect(config.host)

@teardown
fn database_cleanup():
    db_close(connection)
```
`@init` and `@teardown` follow the existing `@IDENT` annotation pattern. O(1), zero new keywords.

---

## 1. String Formatting Specifiers

**Missing:** Format specifiers inside string interpolation.

**Present in:** Python (`f"{value:.2f}"`), Rust (`"{:.2f}"`), C# (`$"{value:N2}"`), Swift (`String(format:)`), JavaScript (`toFixed(2)`)

**Problem:** Simple's interpolation only does basic `{expr}` substitution. No alignment, width, precision, radix, or padding.

```simple
# Current (verbose workaround needed)
val s = float_to_str_prec(value, 2)     # No native way
print "Result: {s}"

# What other languages offer
print f"Result: {value:.2f}"            # Python
println!("Result: {:.2f}", value)       # Rust
```

**Useful for:** Number formatting, table alignment, debug output, reports.

**Proposed syntax:**
```simple
print "Result: {value:.2f}"             # float, 2 decimal places
print "Name: {name:>20}"                # right-align in 20-char field
print "Hex: {byte:08x}"                 # hex, zero-padded to 8 chars
print "Int: {count:,}"                  # thousands separator
```

> **Safety Profile Note:** Format strings are a classic latent runtime fault surface (wrong spec, wrong type, width/precision edge cases). Safety profile requires:
> - Format parsing validated at **compile time** (type/arity/spec checking)
> - Allocation-free APIs: `format_to(buf, "...", args) -> Result<len, Err>` with explicit buffers
> - No locale-dependent behavior unless explicitly opted in

**Impact:** HIGH. Affects everyday output and debug code.

---

## 2. Labeled Breaks and Continues

**Missing:** Named loop labels to break out of specific outer loops.

**Present in:** Rust (`'label: loop { break 'label; }`), Java (`outer: for`), Kotlin, Go, Perl

**Problem:** Nested loops require awkward flags or early returns to escape multiple levels.

```simple
# Current workaround (ugly):
var done = false
for row in rows:
    for col in row:
        if found(col):
            done = true
            break
    if done:
        break

# What Rust has:
'outer: for row in rows:
    for col in row:
        if found(col):
            break 'outer
```

**Proposed syntax** (`'label` prefix — `'` is currently unused in the lexer, no conflict):
```simple
'outer: for row in rows:
    for col in row:
        if found(col):
            break 'outer        # break only — safety-profile compliant
        if skip(col):
            continue 'outer     # continue-label: disallowed in safety profile
```

> **Grammar note:** `outer: for` (bare `IDENT ':'`) is a parse error at statement level in current grammar — `IDENT` starts an expression, and `:` is unexpected after it. The `'label` syntax avoids this: `'` is a new `TOK_LABEL` lexer token (currently unused), making labels unambiguous at the lexer level with zero parser lookahead increase.

> **Safety Profile Note:** JSF AV C++ bans labels (except in `switch`) and bans `continue` in loops. Labeled `continue` increases non-local reasoning. Policy:
> - **Safety profile:** allow only `break label` (no `continue label`); prefer "extract to function + early return" pattern
> - Compiler can verify `break label` is equivalent to a single structured exit
> - Labeled `continue` is a deviation from JSF; disallow in safety profile

**Impact:** MEDIUM. Comes up frequently in nested iteration, parsing, graph traversal.

---

## 3. `errdefer` — Error-Conditional Cleanup

**Missing:** Deferred cleanup that only runs on error paths (not normal exit).

**Present in:** Zig (`errdefer`), some Go patterns with `defer` + named return values

**Problem:** Simple has `defer` (always runs). But sometimes you only want cleanup if an error occurs — e.g., release a resource if allocation fails later.

```zig
// Zig:
var list = ArrayList(i32).init(allocator);
errdefer list.deinit();  // only runs if we return an error
try list.append(1);
try list.append(2);
return list;  // no deinit here — caller owns it
```

```simple
# Proposed:
fn build_collection() -> Result<[i64], text>:
    val list = list_create()
    errdefer list_free(list)       # only on error
    result = list_append(list, 1)?
    result = list_append(list, 2)?
    Ok(list)                       # errdefer does NOT run
```

> **Safety Profile Note:** Good fit if:
> - `errdefer` bodies are **side-effect constrained** (only resource release calls, no allocation)
> - LIFO, lexically scoped (no dynamic registration)
> - Similar to "assertions must be side-effect free" discipline in Power of Ten

**Impact:** MEDIUM. Important for correct resource management in fallible code.

---

## 4. Struct Update / Spread Syntax

**Missing:** Create a new struct based on another with some fields changed.

**Present in:** Rust (`Point { x: 5, ..other }`), JavaScript (`{...obj, name: "new"}`), Elm, OCaml, F#

**Problem:** To create a modified copy of a struct, you must repeat all unchanged fields.

```simple
# Current (verbose):
val new_point = Point(x: p.x + 1, y: p.y, z: p.z, label: p.label)

# Proposed (struct update syntax):
val new_point = Point(..p, x: p.x + 1)   # copy p, override x
```

**Proposed syntax:**
```simple
val updated = User(..original_user, name: "Bob", age: 31)
val moved = Point(..p, x: p.x + dx, y: p.y + dy)
```

> **Safety Profile Note:**
> - Implicit copying can conceal resource duplication (handles, locks, ownership tokens)
> - **Safety profile:** permit only for `Copy`/POD-like structs (bitwise copy, no heap-backed members)
> - For heap-backed structs: require explicit `clone()` / `copy_from()` returning `Result`
> - Tooling must audit copy costs

**Impact:** HIGH. Immutable-first design makes this critical — every struct modification requires full reconstruction.

---

## 5. Derive / Auto-Implementation

**Missing:** Auto-generating trait implementations for standard capabilities.

**Present in:** Rust (`#[derive(Debug, Clone, PartialEq, Hash)]`), Haskell (`deriving (Show, Eq, Ord)`), Kotlin (`data class`), Swift (`Codable`)

**Problem:** Common behaviors like equality, copying, printing, hashing, and serialization must be hand-implemented for every type.

```simple
# Current: must manually implement for each struct
struct Point:
    x: i64
    y: i64

fn point_equal(a: Point, b: Point) -> bool:
    a.x == b.x and a.y == b.y

# Proposed:
@derive(Eq, Clone, Hash, Display)
struct Point:
    x: i64
    y: i64
```

**Capabilities to derive:**
- `Eq` / `PartialEq` — structural equality via `==`
- `Clone` / `Copy` — explicit copy semantics
- `Hash` — for use as dict/set keys
- `Display` / `Debug` — human-readable string representation
- `Ord` / `PartialOrd` — comparison ordering
- `Default` — zero/empty value construction
- `Serialize` / `Deserialize` — JSON, SDN, binary

> **Safety Profile Note:** "Generated code you didn't read" is a review hazard in regulated environments. Policy:
> - Must provide `--emit-expanded` view for audits (generated code fully visible)
> - **Safety profile allowed set:** `Eq`, `Ord`, `Copy`, `Debug` (with bounded formatting)
> - **Disallow in safety profile** unless explicitly permitted: `Hash` (global table), `Serialize`/`Deserialize` (may allocate), `Clone` on heap-backed types
> - Codegen must be deterministic and spec-defined

**Impact:** HIGH. Reduces boilerplate dramatically. Every non-trivial project needs at least `Eq` and `Display`.

---

## 6. Extension Methods

**Missing:** Adding methods to existing types without modifying their source.

**Present in:** Kotlin (`fun String.isPalindrome()`), Swift (`extension String`), C# (`static class Extensions`), Ruby (open classes), TypeScript (interface merging)

**Problem:** Cannot add methods to `text`, `[T]`, or library types without modifying the stdlib.

```kotlin
// Kotlin:
fun String.isPalindrome(): Boolean = this == this.reversed()
fun List<Int>.sum(): Int = this.reduce(0) { acc, x -> acc + x }
```

```simple
# Proposed:
extend text:
    fn is_palindrome() -> bool:
        self == self.reverse()

extend [i64]:
    fn sum() -> i64:
        self.reduce(0, \acc, x: acc + x)

# Usage:
"racecar".is_palindrome()  # true
[1, 2, 3].sum()             # 6
```

> **Safety Profile Note:** Name resolution becomes non-obvious ("where did this method come from?") hurting code review. Policy:
> - Require **explicit import qualification**: `use ext TextExtras` then `"x".is_palindrome()`
> - Only allow extensions in the **same module/namespace** (no global open-class)
> - `use module.*` wildcard extensions disallowed in safety profile
> - Compiler must emit provenance info for all extension methods

**Impact:** HIGH. Enables domain-specific APIs, keeps code readable (`items.to_csv()` vs `csv_from(items)`), avoids utility function sprawl.

---

## 7. Union Types (Type-Level OR)

**Missing:** A type that can be one of several types at the type-system level, expressed inline in function signatures and type aliases.

**Present in:** TypeScript (`string | number | boolean`), Python (`Union[str, int]` / `str | int`), Haskell (sum types), Ceylon

**Problem:** Simple has `enum` for tagged unions but no lightweight type-OR notation for function signatures. Every ad-hoc multi-type parameter needs a named enum wrapper.

```simple
# Current workaround (verbose):
enum ID:
    Name(text)
    Num(i64)
fn lookup(id: ID) -> Option<User>: ...

# Proposed (type-OR sugar — desugars to anonymous tagged enum):
type ID = text | i64
fn lookup(id: text | i64) -> Option<User>:
    match id:
        text s: find_by_name(s)
        i64 n: find_by_id(n)
```

**Semantics:** Type-OR is always a **tagged sum** (never untagged/unsafe). It is sugar for an anonymous enum — exhaustive `match` is required.

```simple
# More examples:
fn parse(input: text | [u8]) -> Result<Value, text>:
    match input:
        text s: parse_text(s)
        [u8] b: parse_bytes(b)

# Nested / nullable:
type JsonValue = text | i64 | f64 | bool | nil
```

**Distinct from C-style memory unions:** Type-OR has no unsafe memory overlap — see section 7b below.

> **Safety Profile Note:**
> - Always tagged — safe by construction (exhaustive match enforced)
> - Ban implicit coercions between union members (no silent widening)
> - No lossy implicit conversions between variants

**Impact:** MEDIUM. Useful for interop, JSON-like data, public APIs that accept multiple representations.

### 7b. C-Style Unsafe Memory Union

**Missing:** Overlapping-memory union fields inside structs/classes (C/Rust-style `union`).

**Present in:** C (`union`), Rust (`union`), C++ (`union`), Zig (`extern union`, `packed union`)

**Use cases:** Wire protocol parsing, type-punning for bit manipulation, FFI interop with C structs, embedded register layouts.

```c
// C style:
union Payload {
    int64_t as_int;
    double  as_float;
    uint8_t as_bytes[8];
};
```

**Proposed design — unsafe, struct/class-local, always private:**

```simple
struct WireFrame:
    tag: u8
    private unsafe union _payload:
        as_int: i64
        as_float: f64
        as_bytes: [u8; 8]

    fn read_int() -> i64:
        unsafe: self._payload.as_int      # explicit unsafe access

    fn read_float() -> f64:
        unsafe: self._payload.as_float

class NetworkPacket:
    header: u32
    private unsafe union _body:
        raw: [u8; 256]
        parsed: PacketFields
```

**Constraints:**
- `unsafe union` keyword required at declaration
- **Only inside `class` or `struct`** — no module/global-scope union definitions
- Always **`private`** — cannot appear in any public API surface
- All field access requires an explicit `unsafe` block at the call site
- Prefer `enum` for all public-facing multi-type values

> **Safety Profile Note:**
> - Quarantined by design: unsafe + private + struct-local prevents escape into safe code
> - All access sites are explicitly tagged `unsafe` — auditable by grep
> - No pointer arithmetic on union fields
> - Restricted to HAL/FFI layers in safety profile

**Impact:** MEDIUM. Essential for FFI, protocol parsing, and embedded register layout — use cases where type-OR and enum are not sufficient.

---

## 8. Default Method Implementations in Traits

**Missing:** Providing default bodies for trait methods so implementations only need to override non-default ones.

**Present in:** Rust (default method bodies in `trait`), Java 8+ (`default`), Swift (`extension Protocol`), Kotlin (`interface`)

**Problem:** Every trait method must be implemented by every implementing type, even boilerplate ones.

```rust
// Rust:
trait Display {
    fn fmt(&self) -> String;
    fn print(&self) {
        println!("{}", self.fmt());  // default impl
    }
}
```

```simple
# Proposed:
trait Display:
    fn to_string() -> text       # required — no default

    fn print():                   # default implementation
        print self.to_string()

    fn println():                 # another default
        print "{self.to_string()}\n"

# Implementer only needs to_string():
impl Display for Point:
    fn to_string() -> text:
        "({self.x}, {self.y})"
```

> **Safety Profile Note:** Default bodies can accidentally rely on allocation/logging/etc. Policy:
> - Allow, but default methods must be either: inlineable + allocation-free, OR explicitly marked `@not_safety` (excluded by profile)
> - No hidden dynamic dispatch in default implementations

**Impact:** HIGH. Without this, traits are limited to pure interfaces. Reduces the boilerplate explosion from every trait method needing impl in every type.

---

## 8. Associated Types in Traits

**Missing:** Type members defined within a trait, bound per implementation.

**Present in:** Rust (`type Item`), Swift (`associatedtype`), Haskell (type families), Scala

**Problem:** Generic traits with a type parameter (`Iterator<T>`) pollute type signatures everywhere. Associated types let the concrete type pick the associated type once.

```rust
// Rust:
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

impl Iterator for Counter {
    type Item = i32;
    fn next(&mut self) -> Option<i32> { ... }
}
```

```simple
# Proposed:
trait Iterator:
    type Item
    fn next() -> Option<Self.Item>

impl Iterator for Counter:
    type Item = i64
    fn next() -> Option<i64>:
        ...

# Usage: clean — no <T> pollution in calling code
fn sum_iter(it: Iterator) -> i64:
    var total: i64 = 0
    while it.next()?.? as v:
        total = total + v
    total
```

> **Safety Profile Note:** Type system complexity increases tool burden (static analyzers, proof tooling). Policy:
> - Acceptable if strict rules prevent "type-level computation explosions"
> - Enforce stable, predictable monomorphization limits (compiler error if exceeded)
> - Error messages must remain clear and actionable

**Impact:** HIGH. Currently generics and trait bounds interact verbosely. Associated types reduce noise significantly for collection-like APIs.

---

## 9. Atom / Symbol Type

**Missing:** A lightweight, intern-pooled string that compares by identity, not content.

**Present in:** Ruby (`:symbol`), Erlang/Elixir (atoms), Lisp (symbols), Clojure (keywords), JavaScript (Symbol)

**Problem:** Using `text` for categorical values (statuses, event names, mode flags) is both wasteful (heap strings) and error-prone (typos are undetected).

```ruby
# Ruby:
status = :pending
status == :pending   # fast identity comparison
```

```simple
# Proposed: atom literal with backtick prefix
val status = `pending
val mode = `reading

match status:
    `pending: start_processing()
    `done: cleanup()
    `error: handle_failure()

# Type: atom
fn set_status(s: atom): ...
```

> **Safety Profile Note:** Interning often implies global tables + allocation and can become unbounded (DoS-like). Policy:
> - **Safety profile:** atoms are **compile-time only** — fixed, link-time enumerated set stored in ROM tables
> - Reject runtime-created atoms in safety profile (use `enum` instead — most analyzable)
> - Cross-module identity stability must be part of the language spec

**Benefit:** Compile-time checked names, fast O(1) comparison, no heap allocation, readable in pattern matching, good for event systems and state machines.

**Impact:** MEDIUM. Particularly valuable in actor systems, state machines, and protocol implementations.

---

## 10. Compile-Time Evaluation (`comptime` / `const fn`)

**Missing:** Evaluating expressions and functions at compile time.

**Present in:** Zig (`comptime`), Rust (`const fn`), C++ (`constexpr`), D (`enum` constants), Nim (`when`/`static`)

**Problem:** No way to compute constants, array sizes, or type-dependent values at compile time.

```zig
// Zig comptime:
fn fibonacci(n: comptime_int) comptime_int {
    if (n <= 1) return n;
    return fibonacci(n - 1) + fibonacci(n - 2);
}
const fib10 = fibonacci(10);  // computed at compile time
```

```rust
// Rust const fn:
const fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}
const BUFFER_SIZE: usize = max(256, 512);
```

```simple
# Proposed:
const fn fibonacci(n: i64) -> i64:
    if n <= 1: n
    else: fibonacci(n - 1) + fibonacci(n - 2)

const FIB_10 = fibonacci(10)    # evaluated at compile time

# Or Zig-style:
comptime val LOOKUP_TABLE = build_table(256)
```

> **Safety Profile Note:** Turing-complete CT eval can reintroduce recursion, non-termination, and build nondeterminism. Policy:
> - Restrict to a **total, terminating subset** (no unbounded recursion, no unbounded loops; enforce step limits)
> - Disallow CT eval that touches I/O, environment, timestamps, randomness
> - Macro-like power tends to bypass coding standards; require CT code to follow same rules as runtime code

**Impact:** MEDIUM. Important for embedded systems, performance tuning, and avoiding magic numbers.

---

## 11. Newtype / Opaque Type Wrapper

**Missing:** Zero-cost type wrapper that creates a distinct type from an existing one.

**Present in:** Rust (`struct Meters(f64)`), Haskell (`newtype`), Kotlin (value classes), Swift, TypeScript (branded types)

**Problem:** Using primitive types for domain values (ids, measures, money) loses type safety — a `user_id` and `product_id` are both `i64` and can be accidentally swapped.

```rust
// Rust:
struct UserId(i64);
struct ProductId(i64);

fn find_user(id: UserId) -> Option<User> { ... }
// find_user(product_id)  // compile error!
```

```simple
# Proposed (zero-cost at runtime):
newtype UserId = i64
newtype ProductId = i64
newtype Meters = f64
newtype Milliseconds = i64

fn find_user(id: UserId) -> Option<User>: ...
fn find_product(id: ProductId) -> Option<Product>: ...

val uid = UserId(42)
val pid = ProductId(42)
# find_user(pid)   # ERROR: type mismatch UserId != ProductId
# uid + pid        # ERROR: can't mix newtypes
```

> **Safety Profile Note:** **Strongly recommended** — exactly the kind of "prevent bugs by construction" feature safety-critical code needs. Zero runtime overhead is a bonus.

**Impact:** HIGH. Prevents entire classes of subtle bugs (unit confusion, ID mix-ups). Zero runtime overhead.

---

## 12. Exhaustiveness Checking in `match`

**Missing:** Compile-time verification that `match` covers all enum variants.

**Present in:** Rust (compiler error for non-exhaustive match), Haskell (warnings), TypeScript (discriminated unions), OCaml, Elm (hard error)

**Problem:** Simple has `match` but may not enforce that all enum variants are handled. Missing a case silently falls through or panics.

```rust
// Rust: compile error if variant missing
enum Direction { North, South, East, West }
match direction {
    Direction::North => ...,
    Direction::South => ...,
    // ERROR: patterns East and West not covered
}
```

```simple
# Proposed: compile-time exhaustiveness check
enum Status:
    Pending
    Running
    Done
    Failed(msg: text)

match status:
    Pending: start()
    Running: check()
    Done: finish()
    # COMPILE ERROR: Failed(msg) not handled
```

**Also useful:** `@non_exhaustive` annotation to explicitly allow partial matches (for forward-compatible APIs where new variants may be added) — requires explicit `_ =>` default arm.

> **Safety Profile Note:**
> - **Make exhaustiveness the default** — opt-out requires explicit annotation AND an explicit `_ / default` arm
> - Escape hatches (non-exhaustive) must be justified and visible to tooling
> - Aligns with Power of Ten: all paths must be analyzed

**Impact:** HIGH. This is a core safety feature for enum-heavy code. Catches logic bugs at compile time.

---

## 13. `or_else` / Error Chaining (Result Ergonomics)

**Missing:** Ergonomic Result/Option chaining methods like Rust's `?` operator with error context, and chained transforms.

**Present in:** Rust (`?`, `.map_err()`, `.context()`, `.unwrap_or_else()`), Haskell (monadic bind), Swift (`try`, `map`, `flatMap`), Kotlin (`.let { }`)

**Problem:** Handling Result/Option chains is verbose without chaining methods.

```rust
// Rust:
fn read_config(path: &str) -> Result<Config, Error> {
    let text = fs::read_to_string(path)
        .map_err(|e| Error::Io(e))?;
    let config = parse_config(&text)
        .map_err(|e| Error::Parse(e))?;
    Ok(config)
}
```

```simple
# Proposed — Result chaining methods:
fn read_config(path: text) -> Result<Config, text>:
    val text = file_read(path).map_err(\e: "IO: {e}")?
    val config = parse_config(text).map_err(\e: "Parse: {e}")?
    Ok(config)

# Proposed chaining API:
result
    .map(\v: v * 2)                    # transform success
    .map_err(\e: "context: {e}")       # transform error
    .and_then(\v: validate(v))         # chain fallible
    .or_else(\e: use_default(e))       # fallback on error
    .unwrap_or(default_value)          # extract with default
    .unwrap_or_else(\e: compute(e))    # computed default
```

**Missing methods also for Option:**
```simple
option
    .map(\v: transform(v))
    .filter(\v: v > 0)
    .flat_map(\v: might_fail(v))
    .or_else(\: try_alternative())
    .zip(other_option)
    .unzip()
```

> **Safety Profile Note:** Long chains can become review-hostile and debugger-unfriendly. Policy:
> - Permit, but style-guide **cap chain length** (e.g., max 3-4 chained calls)
> - Require **named helper functions** for complex lambdas inside chains
> - Require **explicit error typing** — no stringly-typed errors in safety profile
> - Easy to hide non-trivial work inside lambdas: require non-trivial lambdas to be named functions

**Impact:** HIGH. `Result` and `Option` are the primary error handling mechanism — making them pleasant to work with is essential.

---

## 14. Tail Call Optimization (TCO) — `tailrec` Only

**Missing:** Language-level guarantee for tail recursive calls.

**Present in:** Erlang (mandatory TCO), Haskell (lazy), Scheme (R5RS standard), Lua (guaranteed), Kotlin (`tailrec` keyword)

**Problem:** Recursive algorithms (parsers, tree traversals, state machines) risk stack overflow without TCO.

**Decision:** Only explicit opt-in `tailrec` is allowed. General recursion without `tailrec` is not guaranteed to be optimized. This aligns with JSF/NASA safety constraints.

```kotlin
// Kotlin: explicit opt-in (model for Simple)
tailrec fun factorial(n: Long, acc: Long = 1): Long =
    if (n == 1L) acc else factorial(n - 1, n * acc)
```

```simple
# Proposed: explicit opt-in only
@tailrec
fn factorial(n: i64, acc: i64 = 1) -> i64:
    if n <= 1: acc
    else: factorial(n - 1, n * acc)   # compiler verifies tail position

# Compiler ERROR if @tailrec but call is not in tail position
# No implicit TCO — must opt in explicitly
```

> **Safety Profile Note:** A general TCO guarantee encourages recursive style everywhere, conflicting with "no recursion" rules (NASA + JSF both discourage/ban recursion unless proven safe). Policy:
> - **Safety profile:** `tailrec` requires compiler proof of tail position AND an explicit max-iteration bound annotation: `@tailrec(max_iter: 1000)`
> - Without bound annotation, `tailrec` is disallowed in safety profile
> - Prefer iterative (loop-based) algorithms; recursion is last resort

**Impact:** MEDIUM. Especially important for functional-style programming with recursion instead of mutation.

---

## 15. Process Supervision Trees (Erlang OTP-style)

**Missing:** Structured fault recovery — supervisors that restart failed processes.

**Present in:** Erlang/OTP (`supervisor`, `gen_server`), Elixir (`Supervisor`), Akka (Scala/Java)

**Problem:** Simple has actors but no standard way to build fault-tolerant systems with automatic restart strategies.

```simple
# Proposed (as library, not core language):
supervisor MyApp:
    strategy: one_for_one       # restart only failed child
    max_restarts: 5
    max_seconds: 10

    child WorkerA:
        module: worker_a
        restart: permanent
        shutdown: brutal_kill

    child WorkerB:
        module: worker_b
        restart: transient      # only restart on abnormal exit
```

> **Safety Profile Note:** "Restart on failure" can mask faults and complicate hazard analysis. Concurrency + restarts can violate determinism and bounded-resource assumptions. Policy:
> - **Keep as a library framework, NOT a core language feature** — separation of concerns
> - Safety profile requires: explicit restart budgets, bounded queues, deterministic scheduling model
> - In strictest safety profile: disable restart entirely (faults must be handled, not hidden)

**Impact:** MEDIUM. Critical for building reliable server applications. Erlang's "let it crash" philosophy requires supervision trees.

---

## 16. Pattern Refinements

### 16a. Or-Patterns (Multi-case matching)

**Missing:** Matching multiple patterns in one arm.

**Present in:** Rust (`A | B | C`), Python (`case A | B`), Haskell, OCaml, Swift

```simple
# Proposed:
match status:
    Pending | Waiting: queue()
    Running | Processing: continue_work()
    Done | Succeeded: finish()
    Failed | Error: handle_failure()
```

**Note:** The current workaround `case X, Y:` is noted as non-working — `case X | Y:` is required.

### 16b. Binding in Patterns (`as` bind)

**Missing:** Binding a name to a value while also matching a sub-pattern.

**Present in:** Rust (`name @ pattern`), Haskell (`as@pattern`), ML family

**Syntax decision:** Use `as` keyword instead of `@` — the `@` token is the annotation prefix and appears at expression/statement level, causing a conflict. The `as` keyword already exists in Simple (used in `use`/`export`, currently broken at runtime but the keyword is recognized).

```simple
# Proposed (using 'as' — no grammar conflict):
match value:
    x as large if large > 1000: handle_large(x)   # bind AND guard
    n as (10 | 20 | 30): handle_special(n)         # bind AND or-pattern

# Reads as: "match x, bind it as large, then guard on large"
```

> **Grammar note:** `@` is `TOK_AT` used exclusively for annotations. Using `as` avoids any conflict — `as` after a pattern expression is unambiguous since `as` is not a binary operator in current expression grammar.

### 16c. Negative / Guard Patterns

**Missing:** Matching when a sub-pattern does NOT match.

**Present in:** Rust (via guards `if !condition`), Elixir (guards), Haskell (patterns + guards)

```simple
# Proposed:
match event:
    click if not inside_modal(click.pos): handle_click(click)
    key if key.code not in reserved_keys: handle_key(key)
```

> **Safety Profile Note:**
> - Guards can become mini-programs inside patterns, increasing cognitive load
> - Harder to prove exhaustiveness if guards are arbitrary
> - **Safety profile:** allow only **side-effect-free guard expressions** (comparisons, range checks, boolean combinations)
> - Compiler should conservatively treat guarded arms as not fully covering unless proven

**Impact:** MEDIUM. Reduces boilerplate in complex matching. Or-patterns especially reduce redundant arms.

---

## 17. Module System Improvements

### 17a. Module Aliasing in `use`

**Status:** Currently broken. MEMORY.md notes: "`as` keyword in `use`/`export` breaks runtime parser: `use mod.{name as alias}` causes 'expected expression, found As'."

> **Grammar note:** The `as` token already exists in the lexer (`TOK_AS`). The fix is purely in `parse_use_decl()` — after parsing an import name inside `{…}`, if the next token is `TOK_AS`, consume it and read an alias identifier. O(1): `as` uniquely identifies the alias form. No new tokens needed.

**Present in:** Python (`import numpy as np`), Rust (`use module as alias`), JavaScript (`import * as alias from`)

```simple
# Currently broken: use mod.{name as alias} fails
# Workaround: delegation fn new_name(x): old_name(x)

# Proposed fix:
use std.encoding.json as json
use std.collections.hashmap as HashMap
use very.long.module.name as short
```

### 17b. Re-export with Rename

**Status:** Currently broken. `export foo as bar` causes "expected expression, found As".

**Present in:** TypeScript (`export { foo as bar } from './module'`), Rust (`pub use`), JavaScript

```simple
# Proposed:
export use std.json.{parse as parse_json, encode as to_json}
pub use internal.{InternalType as PublicType}
```

### 17c. Namespace / Package Hierarchy

**Missing:** Explicit package declarations that aren't just directory structure.

**Present in:** Java (explicit `package com.example`), Go (`package main`), Python (explicit `__init__.py` with re-exports), Kotlin, Rust (`mod` tree)

> **Safety Profile Note:**
> - Re-exports can obscure where definitions come from (traceability hazard)
> - **Safety profile:** require all re-exports to be explicit and **machine-traceable** (compiler emits provenance)
> - Disallow wildcard re-exports (`pub use module.*`) in safety profile

**Impact:** MEDIUM. As projects grow, having explicit namespace control (not just implicit directory structure) improves maintenance.

---

## 18. `const` and Compile-Time Constants

**Missing:** A first-class `const` declaration distinct from `val` — computed once, guaranteed at compile time, usable as type arguments.

**Present in:** Rust (`const MAX: usize = 1024`), C++ (`constexpr`), Zig (`const`), TypeScript (`const enum`)

**Problem:** `val` is runtime-immutable. A compile-time constant differs: it can be used as array size, generic parameter, match discriminant, etc.

```simple
# Proposed:
const MAX_BUFFER: i64 = 4096
const VERSION: text = "1.0.0"
const PI: f64 = 3.14159265358979

# Usable as type-level value:
val buffer: [u8; MAX_BUFFER] = []        # fixed-size array
match response.version:
    VERSION: handle_current()
    _: handle_legacy()
```

**Impact:** MEDIUM. Important for embedded, performance-sensitive code, and public APIs that expose versioned constants.

---

## 19. String Multi-line Templates (Fix Triple-Quoted Strings)

**Status:** Already identified as broken in MEMORY.md. "Triple-quoted strings `"""` break parser: Runtime parser fails with 'Unterminated triple-quoted string'. Use `#` comments instead."

**Present in:** Python (`"""..."""`), JavaScript (template literals), Kotlin (raw strings), Ruby (`<<~HEREDOC`), Rust (`r#"..."#`)

```simple
# Proposed (raw heredoc style):
val sql = ~"""
    SELECT *
    FROM users
    WHERE age > 18
    ORDER BY name
    """

val html = ~"""
    <html>
        <body>{content}</body>
    </html>
    """
```

> **Safety Profile Note:** Main risks are tooling issues — indentation, invisible whitespace, line ending normalization; if used for embedded DSLs, can sneak complexity into string literals. Policy:
> - Enforce explicit indentation rules with compiler validation
> - Provide "raw string" syntax with clear, defined escaping rules
> - Disallow embedded DSL processing inside multiline strings (keep them as pure text)

**Impact:** HIGH. Multi-line strings are essential for SQL, HTML, JSON templates, error messages, and documentation examples.

---

## 20. Scoped `let` Expressions / Scope Functions

**Missing:** Evaluating a block as an expression with a locally scoped result.

**Present in:** Kotlin (`run`, `let`, `apply`, `also`, `with`), Swift (`{ ... }()`), Haskell (`let...in`), JavaScript (IIFE), Rust (block expressions)

**Problem:** Complex initialization logic must be broken into multiple statements or extracted into helper functions.

```kotlin
// Kotlin:
val result = run {
    val temp = expensive_computation()
    transform(temp)  // result of block
}
```

```simple
# Proposed: block as expression
val result = do:
    val temp = expensive_computation()
    transform(temp)                       # implicit return

# Also useful for null-safe chains:
val processed = user?.let \u:
    log("Processing {u.name}")
    process(u)
```

> **Safety Profile Note:**
> - Shadowing in nested scopes is a hazard — **ban shadowing** in safety profile
> - Require explicit names for non-trivial patterns
> - Scoped blocks are fine if they reduce hidden state; must not create closure-capture issues

**Impact:** MEDIUM. Reduces function proliferation for short initialization blocks. Natural extension of Simple's expression-oriented design.

---

## 21. `where` Clauses for Generic Constraints

**Status:** Same-type parameter disambiguation is already handled by Simple's named parameter system. When a function has multiple parameters of the same type (e.g., `fn(from: text, to: text)`), named arguments prevent ordering bugs — the primary benefit of keyword-only enforcement for same-type params is already achieved.

**Present in:** Rust (`where T: Display + Clone`), Swift (`where Element: Comparable`), Haskell, C# (`where T : IComparable`)

**Problem:** Complex generic constraints inline in `<>` become unreadable.

```rust
// Rust: where clause
fn largest<T>(list: &[T]) -> T
where
    T: PartialOrd + Copy,
{ ... }
```

```simple
# Current (if generics support constraints):
fn largest<T: Ord + Clone>(list: [T]) -> T:
    ...

# Proposed where clause — MUST use '+' for multiple bounds per type param:
fn process<T, E>(data: T, handler: E) -> Result<text, text>
    where T: Display + Serialize,
          E: EventHandler + Clone:
    ...
```

> **Grammar note:** `+` for multiple bounds on one type param is **required for O(1) parsing**. With `,` between constraints (different type params only), the parser can always determine that `:` after a bound name = body start:
> - After bound name: `+` → more bounds for same param, `,` → next param constraint, `:` → body start
> - `where T: A + B, E: C:` — unambiguous O(1) throughout
> - If `,` were used within one param's bounds (`where T: A, B:`), then `B:` would be ambiguous: is it `B: NextBound` or `B` END `:` body? — LL(2) required. **Disallow this form.**

**Impact:** LOW-MEDIUM. Purely ergonomic. Becomes important when multiple bounded type parameters are involved.

---

## 22. Lazy / One-Time Initialization

**Status:** Check `doc/research/startup_optimization.md` for any existing startup library patterns. Not found in MEMORY.md — needs verification whether a startup-phase initialization library already exists.

**Present in:** Rust (`once_cell`, `lazy_static`), Kotlin (`by lazy`), Swift (`lazy var`), Java (`double-checked locking`)

**Problem:** Module-level initialization often needs FFI calls or expensive computation that should only run once.

```kotlin
// Kotlin:
val config: Config by lazy {
    load_config_from_disk()
}
```

```simple
# Proposed:
lazy val config = load_config_from_disk()   # runs once on first access
lazy val lookup_table = build_table(256)

# Alternatively, explicit API:
use std.lazy.{once}
val get_config = once(\: load_config_from_disk())
```

> **Safety Profile Note:** Hidden state + init order + concurrency races. Can allocate "later", violating "no heap after init." Policy:
> - **Disallow lazy init in safety profile**; require explicit `init()` phase in program startup
> - If allowed: must be single-thread deterministic + preallocated storage (no runtime heap)
> - Use startup lib (if it exists) for structured init sequencing instead

**Impact:** MEDIUM. Currently workaround is manual flag-based initialization or init functions.

---

## 23. Named / Keyword-Only Parameters

**Status:** Simple already requires named arguments for same-type parameters in practice (the primary bug source this prevents). Same-type param disambiguation is already handled by Simple's named param system when callers use named args.

**Present in:** Python (everything after `*` must be keyword-only), Ruby (hash params), Kotlin (named parameters + `required`), Swift (argument labels)

**Problem:** For functions with multiple booleans or similar types, positional calls are bug-prone.

```python
# Python:
def connect(host, *, port, timeout):  # port and timeout MUST be named
    ...
connect("localhost", port=8080, timeout=30)
# connect("localhost", 8080, 30)  # ERROR
```

```simple
# Proposed: mark params as keyword-only with ~
fn connect(host: text, ~port: i64, ~timeout: i64 = 30):
    ...

connect("localhost", port: 8080)              # OK
# connect("localhost", 8080, 30)              # ERROR: port must be named
```

> **Safety Profile Note:** Strongly recommended — improves call-site clarity and reduces parameter-order bugs. Main concern is interop/FFI and API churn.

**Impact:** LOW-MEDIUM. Prevents common call-site bugs for functions with many parameters of the same type. (Same-type disambiguation already addressed by named args.)

---

## 24. String Builder / Efficient Append

**Missing:** A mutable string accumulator that avoids O(n²) concatenation.

**Present in:** Java (`StringBuilder`), Rust (`String::with_capacity` + `push_str`), Python (`.join()`), Go (`strings.Builder`), C# (`StringBuilder`)

**Problem:** `text = text + more_text` inside a loop creates O(n²) copies.

```simple
# Proposed:
val sb = StringBuilder.new()
for item in items:
    sb.push("{item.name}: {item.value}\n")
val result = sb.to_text()

# Or functional style:
val result = items
    |> map(\item: "{item.name}: {item.value}")
    |> join("\n")
```

**Note:** `join` should be in the stdlib as a list method (currently exists but `join` is a reserved keyword per MEMORY.md — this collision should be resolved).

> **Safety Profile Note:** Usually implies allocation and amortized growth strategies — violates "no heap after init" in strict profiles. Policy:
> - Provide `StringBuilder(capacity: N)` with **fixed capacity** + checked writes returning `Result`
> - Or require **caller-provided buffers** (no internal allocation at all)
> - Unbounded `StringBuilder.new()` (auto-grow) disallowed in safety profile

**Impact:** HIGH. Any code generating text in a loop suffers without this.

---

## 25. Trait Objects / Dynamic Dispatch (`dyn`)

**Status:** Needs verification — check whether `dyn Trait` style dynamic dispatch is already implemented in the runtime. Generics (static dispatch) are confirmed working; dynamic dispatch status unclear.

**Present in:** Rust (`dyn Trait`, `Box<dyn Trait>`)

**Problem:** Can't have heterogeneous collections of trait-implementing objects without boxing/enum workarounds.

```rust
// Rust: trait objects
fn display_all(items: &[Box<dyn Display>]) {
    for item in items { println!("{}", item); }
}
```

```simple
# Proposed:
fn display_all(items: [dyn Display]):
    for item in items:
        print item.to_string()

fn process(handler: dyn EventHandler):
    handler.handle(event)
```

> **Safety Profile Note:** Harder static reasoning (which impl runs?), worse timing predictability. Can push people toward downcasts/RTTI-like patterns (JSF mindset: discourage). Policy:
> - **Disallow by default in safety profile**; prefer monomorphization/static dispatch
> - If allowed: require explicit `dyn` keyword (already proposed)
> - **Forbid downcasts** (no RTTI equivalent)
> - Dynamic dispatch must be used only at explicitly designated interface boundaries

**Impact:** MEDIUM. Currently can't have heterogeneous collections of trait-implementing objects without boxing/enum workarounds.

---

## 26. Numeric Literal Improvements (Enforced Format)

**Missing:** Separator for readability. Enforcement required for safety profile.

**Present in:** Rust (`1_000_000`, `0xFF_u8`), Python (`1_000_000`), Ruby, Java, C++, Zig, Swift

**Problem:** Large numbers and bit patterns are hard to read and error-prone.

```simple
# Proposed:
val million = 1_000_000
val hex = 0xFF_A0_B3
val binary = 0b1010_1010
val octal = 0o777

# Type suffixes (if unambiguous):
val byte: u8 = 42u8
val wide: i64 = 100i64
val precise: f64 = 3.14f64
```

> **Safety Profile Note:** Enforce format — do NOT make separators merely optional. Policy:
> - **Warn (or error in safety profile) for numeric literals ≥ 5 digits without `_` separators**
> - Enforce standard grouping conventions (e.g., thousands: `1_000_000`; hex: `0xFF_A0`)
> - Forbid confusing mixes of groupings
> - `0b` binary literals must be supported and encouraged for bit-pattern constants

**Also missing:** `0b` binary literals — unclear if currently supported. Must be verified and added.

**Impact:** LOW-MEDIUM → **MEDIUM** in safety-critical contexts. Misreading a large literal is a real hazard.

---

## 27. Module-Level `init` and `teardown`

**Missing:** Guaranteed initialization and cleanup hooks for modules.

**Present in:** Go (`func init()`), Python (`__init__.py` module code), Ruby (`at_exit`), Erlang (`application:start`), C (`.init` section)

**Problem:** Currently module-level code runs at load time, but there's no guaranteed teardown. For resource management (connections, file handles) in modules, you need explicit init/cleanup APIs.

```simple
# Proposed (annotation syntax — no new keywords, no grammar conflict):
var connection = nil

@init
fn database_setup():
    connection = db_connect(config.host)

@teardown
fn database_cleanup():
    if connection != nil:
        db_close(connection)

fn query(sql: text) -> [Row]:
    db_execute(connection, sql)
```

> **Grammar note:** The earlier proposed `module database: init: ...teardown: ...` syntax introduced `init` and `teardown` as keywords — a conflict with any existing code using them as function/variable names. The `@init`/`@teardown` annotation syntax uses the existing `@IDENT` annotation production with zero new keywords. O(1): `@` uniquely identifies annotations.

> **Safety Profile Note:** Recreates "static initialization order fiasco" class of problems. JSF explicitly warns that cross-unit init order is undefined and problematic. Teardown ordering is equally error-prone. Policy:
> - **Prefer explicit `main_init()` / `main_deinit()` sequencing with declared dependencies**
> - If module hooks exist: require **topologically sorted explicit dependency graph** with declared dependencies visible to tooling
> - Disallow implicit init ordering (no silent cross-module dependency)
> - Make init order fully visible and compiler-verified

**Impact:** LOW-MEDIUM. Particularly useful for FFI wrappers that need C library init/cleanup.

---

## 28. Conditional Compilation

**Missing:** Including/excluding code based on build configuration at compile time.

**Present in:** Rust (`#[cfg(target_os = "linux")]`), Zig (`@import` + `comptime`), C (`#ifdef`), Go (build tags), Nim (`when`)

**Problem:** Can't write cross-platform code that compiles differently per target without runtime checks.

```simple
# Proposed:
@when(os == "linux")
fn get_home() -> text: linux_home_dir()

@when(os == "windows")
fn get_home() -> text: windows_home_dir()

@when(arch == "x86_64")
fn use_simd_ops(): ...

# Or block form:
if comptime os == "linux":
    # linux-specific code (compiled out on other platforms)
```

> **Safety Profile Note:** Fragments the codebase into variants; untested paths accumulate. Harder compliance audits ("which code actually runs?"). Policy:
> - **Strongly limit** conditional compilation to platform/FFI boundaries
> - Require CI to build and test **all supported configurations**
> - Disallow conditional compilation for algorithmic choices (use runtime dispatch instead)
> - Emit configuration manifest as part of build artifact

**Impact:** MEDIUM. Essential for writing cross-platform code and platform-specific optimizations.

---

## 29. `keyof` — Compile-Time Field Name Type

**Missing:** A type operator that produces a union of the literal field names of a struct/class.

**Present in:** TypeScript (`keyof T`), Haskell (`GHC.Generics`), Python (`TypedDict` + `get_type_hints`), Zig (`@typeInfo(T).Struct.fields`)

**Problem:** Cannot write generic functions that accept only valid field names of a given type. Without `keyof`, field name access must use unchecked strings.

```typescript
// TypeScript:
type Point = { x: number; y: number };
type PointKey = keyof Point;   // "x" | "y"

function getField<T>(obj: T, key: keyof T): T[keyof T] {
    return obj[key];
}

// getField(p, "z")  // COMPILE ERROR: "z" is not keyof Point
```

```simple
# Current workaround (unchecked — no compile error for wrong key):
fn get_field(obj: Point, key: text) -> i64:
    if key == "x": obj.x
    elif key == "y": obj.y
    else: 0   # silent failure

# Proposed with keyof:
type PointKey = keyof Point      # compile-time type: "x" | "y" (literal union)

fn get_field(obj: Point, key: PointKey) -> i64:
    match key:
        "x": obj.x
        "y": obj.y
    # Exhaustive — no need for default arm (compiler knows only "x" and "y")
```

**Relationship to compile-time introspection:** `keyof T` is the type-level counterpart of
`@field_names(T)` (a runtime array). `keyof` produces a **type** (union of string literals
usable as parameter type); `@field_names` produces a **value** (array of strings at runtime).

**Use cases:**
- Type-safe generic getter/setter functions
- Type-safe field access in serialization/deserialization
- Generic `pick`/`omit` struct transformations (like TypeScript's `Pick<T, K>`)
- Compile-time checked field name parameters

**Proposed semantics:**
```simple
type Point = struct { x: i64, y: i64 }

keyof Point         # evaluates to type ("x" | "y") at compile time
keyof [i64]         # evaluates to i64 (array index type)
keyof Dict<K, V>    # evaluates to K (dict key type)

# Bounded generic parameter:
fn pick<T, K in keyof T>(obj: T, key: K) -> ...
```

> **Safety Profile Note:** ✅ Pure compile-time — zero runtime cost. Excellent fit for
> safety-critical code: validates field name parameters without any runtime dispatch.
> **Pitfall:** `keyof` must resolve at compile time; cannot be used with runtime-determined types.

**Connection to existing code:** Extends `ConstKeySet`/`ConstKeyValidation` in
`src/std/type/types.spl`. `keyof T` generates a `ConstKeySet` from struct field names.

**Impact:** MEDIUM-HIGH. Enables entire classes of generic type-safe utilities (serialization,
ORMs, form builders) that currently require unchecked string keys.

---

## 30. Mapped Types — Transform All Fields of a Type

**Missing:** A type-level construct that creates a new struct type by applying a transformation
to every field of an existing struct type.

**Present in:** TypeScript (mapped types), Haskell (`GHC.Generics` + `functor`), D (template mixins),
Rust (proc-macro derive), Zig (`comptime` struct construction)

**Problem:** Cannot derive related types (all-optional version, all-readonly, all-serializable)
without manually defining each field. A `Config` struct with 20 fields needs a separate
`PartialConfig` (20 fields, all optional), `ConfigDiff` (20 fields, all optional for delta),
`ConfigProto` (20 fields, all text for wire format) — each maintaining N fields in sync.

```typescript
// TypeScript mapped types:
type Readonly<T> = {
    readonly [K in keyof T]: T[K];
};

type Partial<T> = {
    [K in keyof T]?: T[K];   // ? makes each field optional
};

type Stringify<T> = {
    [K in keyof T]: string;   // all fields become string
};

// Usage:
type Config = { host: string; port: number; timeout: number };
type PartialConfig = Partial<Config>;    // all fields optional
type ReadonlyConfig = Readonly<Config>;  // all fields readonly
```

**Proposed syntax for Simple:**
```simple
# Mapped type syntax: for K in keyof T → new field type
type Partial<T> = struct { for K in keyof T: K: T[K]? }   # all fields become optional

type Stringify<T> = struct { for K in keyof T: K: text }   # all fields become text

type Readonly<T> = struct { for K in keyof T: readonly K: T[K] }   # readonly fields

# Usage:
struct Config:
    host: text
    port: i64
    timeout: i64

type PartialConfig = Partial<Config>
# Equivalent to: struct { host: text?, port: i64?, timeout: i64? }

type ConfigWire = Stringify<Config>
# Equivalent to: struct { host: text, port: text, timeout: text }
```

**Three variants of mapped types:**

### 30a. Field-Value Map (`map_fields`)
Apply a function to every **value** of a struct at runtime:
```simple
# Runtime: map a function over all field values
fn map_fields<T>(obj: T, f: fn(text) -> text) -> Stringify<T>:
    # comptime: for each field K in keyof T:
    #   result.K = f(obj.K.to_string())
```

### 30b. Field-Type Map (compile-time only)
Change the **type** of all fields:
```simple
# Compile-time type transformation:
type Optional<T> = { for K in keyof T: K: T[K]? }  # wrap each field in Option
type Required<T> = { for K in keyof T: K: T[K]! }  # unwrap Option from each field
```

### 30c. Field-Key Map (`pick`, `omit`)
Select or exclude specific fields:
```simple
# TypeScript's Pick<T, K> and Omit<T, K>:
type Pick<T, Keys in keyof T> = struct { for K in Keys: K: T[K] }
type Omit<T, Keys in keyof T> = struct { for K in (keyof T - Keys): K: T[K] }

# Usage:
type HostPort = Pick<Config, "host" | "port">
# Equivalent to: struct { host: text, port: i64 }
```

**Relationship to @derive and generic code generation:**
- `@derive(Partial)` could expand using mapped type rules
- Serialization (`to_json`, `to_sdn`) can be expressed as a mapped type traversal
- ORM field mapping: `type SqlRow<T> = Stringify<T>` maps struct → SQL column values

**Language comparison:**

| Language | Mechanism | Cost | Ergonomics |
|----------|-----------|------|------------|
| TypeScript | Built-in `[K in keyof T]: ...` | Zero (compile-time) | ✅ Very ergonomic |
| Rust | proc-macro derive | Zero (compile-time) | ⚠️ Boilerplate heavy |
| Zig | `comptime @typeInfo` + struct construction | Zero (compile-time) | ⚠️ Verbose |
| Haskell | GHC.Generics + type families | Zero (compile-time) | ❌ Very complex |
| D | Template mixins | Zero (compile-time) | ⚠️ Moderate |
| Go | reflect + code gen | Runtime cost | ❌ Not type-safe |
| **Simple** | Proposed `struct { for K in keyof T: ... }` | Zero (compile-time) | ✅ Target |

> **Safety Profile Note:** ✅ Pure compile-time type transformation, zero runtime overhead.
> Generated struct types are fully analyzable by static tools. No implicit dynamic dispatch.
> **Pitfall:** Type explosion — a library with 5 generic mapped types applied to 10 structs
> produces 50 types; must ensure error messages remain clear.

**Relationship to @derive:** Mapped types are the generalization of `@derive`. Where `@derive(Debug)`
generates a specific implementation, mapped types let users write the transformation rule once
and apply it to any struct. Both serve the same purpose at different power levels.

**Impact:** HIGH for type-safe generic programming. Without mapped types, every "variant" of
a struct (partial, readonly, stringified) must be maintained manually — a common source of
out-of-sync bugs.

---

## 31. Confirmed Implemented Features (Status Update 2026-02-18)

**Previously marked as "Missing" — now implemented:**

### 31a. `if val` / `while val` (Rust's `if let` / `while let`) — ✅ IMPLEMENTED

Simple uses `if val` / `while val` as the equivalent of Rust's `if let` / `while let`.
These are the canonical Simple idiom — `if let` / `while let` are deprecated aliases.

```simple
# Simple's if val (equivalent to Rust's if let):
val opt: Option<i64> = Some(42)
if val Some(x) = opt:
    print "Got: {x}"        # only executes if opt is Some

# while val (equivalent to Rust's while let):
while val Some(value) = queue.pop():
    process(value)

# Also supported:
if var Some(x) = mutable_opt:   # if var for mutable binding
    x = x + 1
```

**Verified in:** `test/feature/parser_control_flow_spec.spl:350-410` — tests for `if val`,
`if var`, `while val`, `while var`. Note in file: "`if let` / `while let` are deprecated;
use `if val` / `while val` instead."

### 31b. Numeric Separators — ✅ IMPLEMENTED (2026-02-18)

`1_000_000`, `0xFF_FF`, `0b1111_0000` now correctly parsed. Parser strips `_` from number tokens.

### 31c. Hex / Binary / Octal Literals — ✅ IMPLEMENTED (2026-02-18)

`0xFF` → 255, `0b101` → 5. Were returning 0 before; now correctly parsed.

### 31d. `newtype Name = Type` — ✅ IMPLEMENTED (2026-02-18)

```simple
newtype UserId = i64
newtype ProductId = i64
# Now distinct types — can't mix UserId with ProductId
```

### 31e. `..spread` Struct Update — ✅ IMPLEMENTED (2026-02-18)

```simple
val new_point = Point(x: 10, ..base)  # copies y, z from base; overrides x
```

### 31f. `do:` Block Expressions — ✅ IMPLEMENTED (2026-02-18)

```simple
val result = do:
    val temp = expensive()
    transform(temp)
```

### 31g. Backtick Atoms — ✅ IMPLEMENTED (2026-02-18)

```simple
val status = `pending
match status:
    `pending: start()
    `done: finish()
```

### 31h. `pack` Feature — NOT A LANGUAGE FEATURE

`pack` is not a language keyword. What exists:
- `src/compiler_core/context_pack.spl` — compiler tool for extracting minimal LLM context
- `src/std/msgpack/pack.spl` — MessagePack binary serialization library
- `*args`/`**kwargs` variadic packing — ✅ already implemented as a language feature

If "pack" means **variadic argument packing** (`*args` spread/gather), that is already
implemented. If it means **struct bit-field packing** (`@packed` attribute for FFI), that
is not yet implemented (needed for `unsafe union` FFI work — see section 7b).

---

## Feature Priority Matrix

| # | Feature | Impact | Complexity | Safety Profile | Status |
|---|---------|--------|------------|---------------|--------|
| 5 | Derive / Auto-implement | HIGH | MEDIUM | ✅ (limited set) | Missing |
| 4 | Struct update syntax | HIGH | LOW | ✅ (Copy-only) | Missing |
| 7 | Default trait methods | HIGH | LOW | ✅ (alloc-free) | Missing |
| 13 | Result/Option ergonomics | HIGH | LOW | ✅ (bounded) | Missing |
| 1 | String format specifiers | HIGH | MEDIUM | ✅ (compile-time) | Missing |
| 6 | Extension methods | HIGH | MEDIUM | ⚠️ (explicit import) | Missing |
| 12 | Exhaustiveness checking | HIGH | MEDIUM | ✅ (mandatory) | Missing |
| 19 | Multi-line strings (fix) | HIGH | LOW | ✅ (clear rules) | **Broken** |
| 24 | String builder | HIGH | LOW | ⚠️ (fixed-cap) | Missing |
| 11 | Newtype wrappers | HIGH | LOW | ✅ (recommended) | Missing |
| 8 | Associated types | HIGH | HIGH | ⚠️ (complexity limit) | Missing |
| 2 | Labeled breaks | MEDIUM | LOW | ⚠️ (break-only) | Missing |
| 3 | errdefer | MEDIUM | LOW | ✅ (constrained) | Missing |
| 9 | Atom / Symbol type | MEDIUM | MEDIUM | ⚠️ (compile-time) | Missing |
| 10 | Comptime evaluation | MEDIUM | HIGH | ⚠️ (total/bounded) | Missing |
| 14 | Tail call (tailrec only) | MEDIUM | MEDIUM | ⚠️ (bounded opt-in) | Missing |
| 15 | Process supervision | MEDIUM | HIGH | ⚠️ (lib, not core) | Missing |
| 16 | Pattern refinements | MEDIUM | LOW | ✅ (pure guards) | Missing |
| 18 | Compile-time constants | MEDIUM | LOW | ✅ | Missing |
| 20 | Scoped let expressions | MEDIUM | LOW | ⚠️ (no shadowing) | Missing |
| 22 | Lazy initialization | MEDIUM | LOW | ❌ (safety profile) | Missing |
| 25 | Trait objects (dyn) | MEDIUM | MEDIUM | ❌ (safety profile) | Needs verification |
| 17 | Module aliasing (fix) | MEDIUM | LOW | ✅ (explicit) | **Broken** |
| 21 | where clauses | LOW | LOW | ✅ | Missing |
| 23 | Keyword-only params | LOW | LOW | ✅ (recommended) | Same-type already handled |
| 26 | Numeric separators | LOW→MED | LOW | ✅ (enforced) | Missing |
| 27 | Module init/teardown | LOW | LOW | ⚠️ (topological) | Missing |
| 28 | Conditional compilation | MEDIUM | MEDIUM | ⚠️ (limited) | Missing |
| 7a | Union types (type-OR) | MEDIUM | MEDIUM | ✅ (tagged only) | Missing |
| 7b | C-style unsafe union | MEDIUM | MEDIUM | ⚠️ (unsafe+private) | Missing |
| 29 | `keyof` type operator | MED-HIGH | MEDIUM | ✅ (compile-time) | Missing |
| 30 | Mapped types | HIGH | HIGH | ✅ (compile-time) | Missing |
| — | Phantom types | LOW | MEDIUM | **RESEARCHED** | See companion doc |
| — | `if val` / `while val` | — | — | ✅ | **✅ IMPLEMENTED** |
| — | Numeric separators | — | — | ✅ | **✅ IMPLEMENTED (2026-02-18)** |
| — | `newtype` declaration | — | — | ✅ | **✅ IMPLEMENTED (2026-02-18)** |
| — | `..spread` struct update | — | — | ✅ | **✅ IMPLEMENTED (2026-02-18)** |
| — | `do:` block expression | — | — | ✅ | **✅ IMPLEMENTED (2026-02-18)** |
| — | Backtick atoms | — | — | ⚠️ compile-time | **✅ IMPLEMENTED (2026-02-18)** |

---

## Quick Wins (Low Complexity, High Value)

These could be implemented with minimal risk:

1. **Struct update syntax** (`Point(..p, x: 5)`) — parser + desugaring only
2. **Default trait method bodies** — already have trait syntax, add optional body
3. **Labeled break** (no continue-label) — lexer + control flow
4. **String multi-line fix** — fix existing broken triple-quote parser
5. **Numeric separator `_` with enforcement** — lexer change + warning pass
6. **`errdefer`** — small addition to defer semantics
7. **`|` or-patterns in match** — `A | B` already partially implied
8. **Result/Option chaining methods** — pure stdlib addition (no syntax change)
9. **Exhaustiveness check warning** — static analysis pass
10. **Module init/teardown syntax** — parser + runtime hook (explicit topological deps)

---

## Feature Gaps by Language

### From Rust
- ✅ Generics (implemented)
- ✅ Pattern matching (implemented)
- ✅ Traits (implemented)
- ✅ Option/Result (implemented)
- ✅ `if let` / `while let` — Simple uses `if val` / `while val` (implemented, `if let` deprecated)
- ✅ `..struct_update` — `Point(x: 10, ..base)` implemented (2026-02-18)
- ✅ `newtype` — `newtype UserId = i64` implemented (2026-02-18)
- ❌ `#[derive(...)]`
- ❌ `'labeled` breaks (continue-label: disallowed by design)
- ❌ `const fn` / `comptime`
- ❌ `where` clauses (parsed but not enforced)
- ❌ `dyn Trait` objects (needs verification)
- ❌ Associated types
- ❌ String format specifiers (`{:?}`, `{:.2}`)
- **RESEARCHED:** `PhantomData` / phantom types → see `introspection_phantom_types_2026-02-17.md` Part 2

### From Zig
- ✅ `defer` (implemented)
- ❌ `errdefer`
- ❌ `comptime`
- ❌ Error unions (`!T`)
- ❌ `@embedFile`

### From TypeScript
- ✅ Generics
- ❌ Union types / type-OR (`A | B` notation) — planned, tagged-sum sugar
- ❌ Discriminated union type narrowing
- ❌ Mapped types — `{ [K in keyof T]: transform(T[K]) }` → see section 30
- ❌ `keyof T` type operator — produces union of field name literals → see section 29
- ❌ Conditional types (`T extends U ? A : B`)
- ❌ Template literal types

### From Python
- ✅ String interpolation (implemented)
- ✅ Comprehensions (implemented)
- ✅ `*args`/`**kwargs` variadic (implemented)
- ❌ Format specifiers (`f"{x:.2f}"`)
- ❌ Keyword-only parameters (`def f(*, kw_only)`) — same-type partially addressed
- ❌ `@property` decorator equivalent

### From Erlang
- ✅ Actors (partially)
- ✅ Pattern matching
- ❌ Supervision trees
- ❌ Tail call guarantee (only explicit `tailrec` planned)
- ❌ Atom type
- ❌ Hot code reload

### From Kotlin/Swift
- ✅ Closures
- ✅ Extension-like methods (via trait impl, but not open extension)
- ❌ Extension methods on existing types
- ❌ Scope functions (`let`, `run`, `apply`)
- ❌ Data classes / record copy
- ❌ Sealed classes (exhaustive hierarchies)

---

## Conclusion

Simple's current feature set is well-rounded for a systems language with functional programming support. The highest-priority gaps fall into three categories:

1. **Ergonomics holes** (struct update, derive, multi-line strings, format specifiers) — daily friction
2. **Type safety gaps** (newtype, exhaustiveness, associated types) — prevent whole bug classes
3. **Standard library completeness** (Result/Option chaining, string builder) — avoid reinventing patterns

The design decisions to exclude exceptions and inheritance are sound and align with Rust/Zig's philosophy. The language would most benefit from filling the ergonomics holes first, as they affect every program written in Simple.

The JSF/NASA safety profile review confirms that Simple's direction — no exceptions, no inheritance, explicit error handling, strong types — is fundamentally aligned with safety-critical requirements. Implementing `--profile=safety` as a compiler flag to enforce the constraints noted above would make Simple viable in regulated environments.

---

## Appendix: Postponed Features

These features have been deferred for later consideration.

### A1. Phantom / Marker Types

**Decision: RESEARCHED — see companion document**

**Full research in:** [`introspection_phantom_types_2026-02-17.md`](introspection_phantom_types_2026-02-17.md) — Part 2 (Phantom Types) and Part 5 (Proposed Design).

**Summary of research findings:**
- Phantom types: zero-cost state encoding via type parameters (`@phantom struct Connected`)
- Use cases: API state machines, type-safe IDs, builder patterns, physical units, capability markers
- Key pitfalls: state explosion, cryptic error messages, data-dependent state limitations
- Design: `@phantom struct`, `struct Foo<State>` with state set constraints
- Integration with existing `ConstKeySet` dict validation in `src/std/type/types.spl`
- Error message design using `@state_description` annotations

**Proposed syntax (from research):**
```simple
@phantom struct Connected
@phantom struct Disconnected

struct Connection<State>:
    socket: i64

fn connect(c: Connection<Disconnected>) -> Connection<Connected>: ...
fn send(c: Connection<Connected>, msg: [u8]): ...
# send(disconnected_conn, data)  # COMPILE ERROR with helpful message
```

### A2. Safe Raw Pointers

**Decision: POSTPONED / NOT ADDED**

**Rationale:** Pointer escape hatches are where most safety properties die. In safety-critical contexts (JSF profile), pointer arithmetic and raw access belong in quarantined `unsafe` blocks restricted to HAL/FFI layers. Adding a "safe raw pointer" abstraction risks creating a false sense of safety. Defer until a full ownership/borrow model is designed.

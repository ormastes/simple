# Modern Introspection, Phantom Types & Compile-Time Error Checking

**Date:** 2026-02-17
**Status:** Research / Design Phase
**Relates to:** `missing_language_features_2026-02-17.md` (Appendix A1 — Phantom Types)
**Scope:** Deep research into compile-time checking, phantom types, introspection tiers, stack traces

---

## Executive Summary

This document expands the postponed "phantom types" item in the missing features list into a
comprehensive framework for **modern type-level safety and observability**. The three pillars are:

1. **Compile-Time Error Checking** — extending what already exists (dict key validation,
   closure warnings, ignored returns) with deeper type-level enforcement.
2. **Phantom Types** — zero-cost type-level state encoding (state machines, units, IDs,
   capabilities). Research across Rust, Zig, Haskell, TypeScript, F#, D, Nim.
3. **Tiered Introspection** — a graduated framework from zero-overhead to full reflection,
   covering stack traces for `assert`/`error_log`.

### What Already Exists in Simple

| Feature | Status | File |
|---------|--------|------|
| Generic monomorphization (runtime) | ✅ Complete | `src/compiler_core/generic_runtime.spl` |
| Closure capture warnings | ✅ Complete | `src/compiler_core/closure_analysis.spl` |
| Ignored return value warnings | ✅ Complete | `src/compiler_core/interpreter/eval.spl` |
| Effect system (async/sync inference) | ✅ Complete | `src/lib/type/effects.spl` |
| ConstKeySet dict validation | ✅ Complete | `src/lib/type/types.spl` |
| Debug support (StackFrame, DebugLevel) | ✅ Design | `src/lib/debug.spl` |
| Panic report with StackTrace | ✅ Design | `src/lib/report/runtime/panic.spl` |
| Error trait with backtrace() | ✅ Design | `src/lib/error.spl` |
| Structural type checking (duck typing) | ✅ Runtime | `src/compiler_core/interpreter/eval.spl` |
| **Phantom types** | ❌ Missing | — |
| **Compile-time @comptime reflection** | ❌ Missing | — |
| **@derive / code generation** | ❌ Missing | — |
| **TypeId (runtime type identity)** | ❌ Missing | — |
| **Stack trace actual capture** | ❌ Missing | — |
| **Static assertions** | ❌ Missing | — |

---

## Part 1: Compile-Time Error Checking

### 1.1 What Currently Exists

Simple already has several compile-time and near-compile-time checks:

#### 1.1a ConstKeySet — Dict Key Validation (`src/lib/type/types.spl`)

The `Type` enum includes `ConstKeySet(keys: [text])` and `DependentKeys(source: text)`, plus
`ConstKeyValidation` and `validate_dict_keys_against_const_set()`. This enforces that dict
literals only use keys from a pre-declared set — a targeted compile-time check.

```simple
# Current: ConstKeySet validates key names against a declared set
enum Type:
    ...
    ConstKeySet(keys: [text])      # Fixed, known key set

struct ConstKeyValidation:
    unknown_keys: [text]
    missing_keys: [text]
    non_literal_keys: bool
```

**Strength:** Catches typo keys and missing required keys at compile time.
**Gap:** Only works for dict literals with known keys. Not extensible to general contracts.

#### 1.1b Closure Capture Analysis (`src/compiler_core/closure_analysis.spl`)

Detects when nested functions try to modify outer `var` variables (which fails at runtime).
Produces `WARN:` messages, 22 tests passing.

#### 1.1c Ignored Return Value Detection (`src/compiler_core/interpreter/eval.spl`)

Detects and warns when a non-void function's return value is silently discarded.

#### 1.1d Effect System (`src/lib/type/effects.spl`)

Tracks `@pure`, `@io`, `@net`, `@fs`, `@unsafe`, `@async` effect annotations. Validates
that declared effects match inferred effects. Uses Tarjan SCC for mutual recursion.

---

### 1.2 More Compile-Time Error Checking — Feature Proposals

#### 1.2a Static Assertions (`@static_assert`)

**What it is:** Evaluate a condition at compile time; emit a compiler error if false.

**Present in:**
- C++: `static_assert(sizeof(T) == 4, "T must be 4 bytes")`
- Zig: `comptime { std.debug.assert(T == u32); }`
- Rust: `const _: () = assert!(size_of::<T>() == 4);`
- Nim: `static: assert T.sizeof == 4`

**Proposed syntax:**
```simple
@static_assert(MAX_BUFFER > 0, "MAX_BUFFER must be positive")
@static_assert(@size_of(i64) == 8, "Expected 64-bit platform")
@static_assert(@fields(Config).len() > 0, "Config must have fields")
```

**When evaluated:** Before code generation. Errors are emitted as type-check errors.
**Safety profile:** ✅ Strongly recommended — catches configuration errors at build time.
**Pitfalls:**
- Must be restricted to side-effect-free expressions
- Error messages must include the failing expression text
- Cannot depend on runtime values

---

#### 1.2b Type-Level State Machines (via Phantom Types)

See Part 2 (Phantom Types) — the full phantom type design integrates here.

---

#### 1.2c Compile-Time Dimension / Unit Checking

**What it is:** Attach physical units to numeric types; prevent mixing incompatible units.

**Present in:**
- F# Units of Measure: `let speed = 5.0<m/s>` — compile error if you add `m` to `s`
- Rust `dimensioned` crate: similar via type system
- Julia (units package): runtime only

**Proposed syntax:**
```simple
@unit Meters
@unit Seconds
@unit MetersPerSecond = Meters / Seconds

fn speed(dist: f64<Meters>, time: f64<Seconds>) -> f64<MetersPerSecond>:
    dist / time

val d: f64<Meters> = 100.0
val t: f64<Seconds> = 9.58
val s = speed(d, t)    # f64<MetersPerSecond>

# val bad = d + t      # COMPILE ERROR: Meters + Seconds is not valid
```

**Implementation approach:** Phantom type parameters on numeric wrappers. Units form an
algebra — the compiler validates dimension equations at type-check time.

**Safety profile:** ✅ Perfect fit — eliminates Mars Climate Orbiter class of unit errors.
**Pitfalls:**
- Dimension algebra can become complex (m/s², kg·m/s²)
- Dimensionless ratios need special handling
- Interop with untagged C/FFI numbers requires explicit annotation
- Not suitable for embedded DSLs requiring unit inference

---

#### 1.2d Checked Format Strings (Extend Section 1 of missing_features)

**What it is:** Validate format spec against argument types at compile time.

**Present in:**
- Rust: `format!("{}", x)` is macro-checked at compile time
- Zig: `std.fmt.format()` uses comptime type inspection
- C: `printf` (static-analysis tools only, not spec)
- Python: `f"{x:.2f}"` checked by type checkers (mypy, pyright)

**Current gap:** Simple's `print "Result: {value:.2f}"` — `.2f` is not validated.

**Proposed check levels:**
1. **Arity check** (easy): count `{}` vs count of args — compile error if mismatch
2. **Type check** (medium): `{x:d}` requires integer; `{x:.2f}` requires float
3. **Width/precision** (hard): validate that width/precision args are non-negative integers

**Implementation:** The lexer already tokenizes `{expr}` in strings. Extend the type-checker
pass to parse format specifiers and validate against the inferred type of `expr`.

**Safety profile:** ✅ Eliminates a class of runtime format errors.
**Pitfalls:**
- Locale-dependent formats (`{:,}` for thousands) need locale-neutral safe defaults
- Dynamic format strings (format spec from a variable) cannot be statically checked

---

#### 1.2e Linear / Affine Type Checking (Must-Use Annotation)

**What it is:**
- **Linear types:** a value must be used exactly once (consumed)
- **Affine types:** a value must be used at most once (either used or dropped, not duplicated)

**Present in:**
- Rust: ownership model (affine by default) — move semantics
- Linear Haskell: explicit linear arrows `a %1-> b`
- Clean (language): uniqueness types
- Rust `#[must_use]` attribute: warn if return value discarded

**Simple already has (partial):** `eval_get_warnings()` for ignored returns. This is the
soft-enforcement version of must-use.

**Proposed:**
```simple
@must_use
fn file_open(path: text) -> File:   # Warn if returned File is discarded
    ...

@linear
struct Transaction:                  # COMPILE ERROR if copied or dropped without commit()
    conn: Connection

fn commit(t: Transaction):           # Consumes t
    t.conn.execute("COMMIT")
    # t is consumed — cannot be used after this call
```

**Safety profile:** ✅ Prevents resource leaks (unclosed files, uncommitted transactions).
**Pitfalls:**
- Increases type system complexity significantly
- @linear may require checking all paths (including error paths with errdefer)
- Hard to retrofit onto existing APIs

---

#### 1.2f API Usage Constraint Checking

**What it is:** Enforce correct call ordering/sequencing via the type system.

**Motivation:** Without this, API misuse (call `connect()` before `send()`) is only caught
at runtime. With type-state encoding, the compiler rejects invalid sequences.

**Present in:**
- Rust: Session types in research; builder pattern enforced via phantom types
- Haskell: ST monad for sequenced state
- TypeScript: State-machine types via discriminated unions

**Example (connection lifecycle):**
```simple
struct Socket<State>:               # State is a phantom parameter
    fd: i64

fn create_socket() -> Socket<Disconnected>: ...
fn connect(s: Socket<Disconnected>) -> Socket<Connected>: ...
fn send(s: Socket<Connected>, data: [u8]): ...
fn close(s: Socket<Connected>) -> Socket<Disconnected>: ...

val s = create_socket()
val c = connect(s)
send(c, data)       # OK
# send(s, data)     # COMPILE ERROR: Socket<Disconnected> != Socket<Connected>
```

See Part 2 (Phantom Types) for full design.

**Safety profile:** ✅ Highly recommended — prevents API misuse by construction.
**Pitfalls:**
- Type error messages become unwieldy: `Socket<Disconnected>` vs `Socket<Connected>`
- Cannot encode all state (data-dependent transitions need runtime checks)
- Each valid state = a separate type; state explosion for complex protocols

---

#### 1.2g Exhaustiveness Checking (Deepen Existing Proposal)

Already in `missing_language_features_2026-02-17.md` Section 12. Key addition here:

**Variant addition tracking:** When an enum gains a new variant, all `match` expressions
that don't have `_` catch-all should produce compile errors. This requires tracking enum
definitions across modules and invalidating all `match` sites.

**Three levels:**
1. **Mandatory exhaustive** (default): all variants must be covered or `_` explicit
2. **`@non_exhaustive` enums**: adding new variants is backward-compatible; callers must have `_`
3. **Sealed variants**: only variants from this module — exhaustive match always valid

```simple
enum Status:
    Pending
    Running
    Done

@non_exhaustive
enum HttpMethod:   # Future: PATCH, TRACE may be added
    Get
    Post
    Put
    Delete

# Callers of HttpMethod MUST include _: arm
```

---

#### Summary: Compile-Time Error Checking Features

| Feature | Present? | Location | Priority | Safety |
|---------|----------|----------|----------|--------|
| ConstKeySet dict validation | ✅ | `std/type/types.spl` | Done | ✅ |
| Closure capture warnings | ✅ | `compiler_core/closure_analysis.spl` | Done | ✅ |
| Ignored return warnings | ✅ | `compiler_core/interpreter/eval.spl` | Done | ✅ |
| Effect system | ✅ | `std/type/effects.spl` | Done | ✅ |
| Static assertions | ❌ | — | HIGH | ✅ |
| Format string validation | ❌ | — | HIGH | ✅ |
| Exhaustiveness checking | ❌ | — | HIGH | ✅ |
| Phantom types (API state) | ❌ | — | MEDIUM | ✅ |
| Dimension/unit checking | ❌ | — | MEDIUM | ✅ |
| Must-use / linear types | ❌ | — | MEDIUM | ✅ |
| @non_exhaustive variants | ❌ | — | LOW | ✅ |

---

## Part 2: Phantom Types

### 2.1 What Are Phantom Types?

Phantom types are type parameters that exist only in the type system — they carry zero-bit
information at runtime. The runtime representation is identical regardless of the phantom
parameter; only the compiler knows (and enforces) the distinction.

**Core property:** `sizeof(Foo<A>) == sizeof(Foo<B>)` — they are the same at runtime.
The phantom parameter is purely a compile-time tag.

### 2.2 Phantom Types in Peer Languages

#### Rust — PhantomData<T>

```rust
use std::marker::PhantomData;

struct Meters;
struct Feet;

struct Length<Unit> {
    value: f64,
    _unit: PhantomData<Unit>,   // zero-size field, exists only for type system
}

fn add_lengths<U>(a: Length<U>, b: Length<U>) -> Length<U> { ... }

let a: Length<Meters> = ...;
let b: Length<Feet> = ...;
// add_lengths(a, b)  // COMPILE ERROR: Meters != Feet
```

`PhantomData<T>` is the Rust mechanism: a zero-size type that tells the compiler "this struct
is logically parameterized by T, even though T appears nowhere in the fields."

**Key Rust pitfalls:**
1. `PhantomData` is awkward boilerplate — every phantom struct needs it explicitly
2. Variance (covariant vs invariant vs contravariant in T) is subtle and tricky
3. Auto-traits (Send, Sync) are affected by phantom parameters
4. Must be included to prevent "unused type parameter" compile errors

---

#### Haskell — Tagged / Type-Level Proof Tokens

```haskell
newtype Tagged t a = Tag { unTag :: a }

type UserId = Tagged UserTag Int
type ProductId = Tagged ProductTag Int

-- Functions that accept UserId cannot receive ProductId
lookupUser :: UserId -> Maybe User
lookupUser (Tag uid) = ...
```

Haskell phantom types are "free" — newtypes have zero runtime cost. The phantom parameter
is just a type parameter that constrains how values can be used.

**Haskell strength:** Type classes + phantom types = type-level proof system.
**Haskell pitfall:** Requires type-class machinery; error messages are often cryptic.

---

#### TypeScript — Branded Types (Structural Type System Workaround)

TypeScript has structural typing — two objects with the same shape are the same type.
Phantom branding adds a unique, impossible-to-construct field to force nominal typing:

```typescript
type UserId = string & { readonly __brand: 'UserId' };
type ProductId = string & { readonly __brand: 'ProductId' };

function createUserId(raw: string): UserId {
    return raw as UserId;  // explicit assertion at boundary
}

function findUser(id: UserId): User { ... }
// findUser(someProductId)  // COMPILE ERROR
```

**TypeScript limitation:** This is a workaround, not a first-class feature. The `__brand`
field is erased at runtime (it doesn't exist), but the type system believes it does.
**Pitfall:** Requires explicit casting at creation sites; no generic phantom parameter.

---

#### F# — Units of Measure (Specialized Phantom)

F# has built-in language support for phantom dimensions:

```fsharp
[<Measure>] type meters
[<Measure>] type seconds
[<Measure>] type m_s = meters / seconds  // derived unit

let distance: float<meters> = 100.0<m>
let time: float<seconds> = 9.58<s>
let speed: float<m_s> = distance / time  // compile-time dimension check
```

**F# strength:** First-class unit arithmetic — the compiler knows that `m/s × s = m`.
**F# limitation:** Only works for numeric types; not a general phantom type system.

---

#### Zig — Type Parameters + comptime (No PhantomData Needed)

Zig doesn't need `PhantomData` because types are first-class `comptime` values:

```zig
fn Tagged(comptime T: type, comptime Tag: type) type {
    return struct {
        value: T,
        // Tag is purely compile-time; zero runtime overhead
        fn tag_type() type { return Tag; }
    };
}

const UserId = Tagged(i64, struct {});
const ProductId = Tagged(i64, struct {});
// These are distinct types — can't mix them
```

**Zig strength:** Type parameters are just comptime values; no special mechanism needed.
**Zig limitation:** No standard phantom type pattern; each team invents their own.

---

#### D — Template Parameters + AliasSeq

```d
struct Length(Unit) {
    float value;
    // Unit is never instantiated — it's a phantom
}

alias Meters = struct {};
alias Feet = struct {};

Length!Meters add(Length!Meters a, Length!Meters b) { ... }
// add(Length!Meters(1.0), Length!Feet(1.0))  // compile error
```

---

### 2.3 Key Use Cases for Phantom Types

#### Use Case 1: Type-Safe IDs

**Problem:** `user_id: i64` and `product_id: i64` are the same type — can be accidentally swapped.

```simple
# With phantom types:
struct Id<Entity>:
    raw: i64

type UserId = Id<User>
type ProductId = Id<Product>

fn find_user(id: UserId) -> Option<User>: ...
# find_user(ProductId(raw: 42))  # COMPILE ERROR
```

**Runtime cost:** Zero — `UserId` and `ProductId` both store one `i64`.

---

#### Use Case 2: API State Machines (Connection/Transaction Lifecycle)

**Problem:** Calling `send()` before `connect()` is a runtime error. With phantom types, it's a compile error.

```simple
struct Disconnected   # phantom state markers (zero-size types)
struct Connected

struct TcpSocket<State>:
    fd: i64             # only real field

fn new_socket() -> TcpSocket<Disconnected>:
    TcpSocket(fd: -1)

fn connect(s: TcpSocket<Disconnected>, addr: text) -> Result<TcpSocket<Connected>, text>:
    ...

fn send(s: TcpSocket<Connected>, data: [u8]) -> Result<i64, text>:
    ...

fn close(s: TcpSocket<Connected>) -> TcpSocket<Disconnected>:
    ...

# Usage:
val s = new_socket()
val c = connect(s, "127.0.0.1:8080")?
send(c, b"hello")?
val s2 = close(c)
# send(s2, b"world")    # COMPILE ERROR: TcpSocket<Disconnected> != TcpSocket<Connected>
```

---

#### Use Case 3: Builder Pattern with Compile-Time Validation

**Problem:** Ensure required fields are set before building.

```simple
struct HasName
struct NoName
struct HasPort
struct NoPort

struct ServerBuilder<N, P>:
    name: text
    port: i64

fn builder() -> ServerBuilder<NoName, NoPort>:
    ServerBuilder(name: "", port: 0)

fn with_name(b: ServerBuilder<NoName, P>, name: text) -> ServerBuilder<HasName, P>:
    ServerBuilder(name: name, port: b.port)

fn with_port(b: ServerBuilder<N, NoPort>, port: i64) -> ServerBuilder<N, HasPort>:
    ServerBuilder(name: b.name, port: port)

fn build(b: ServerBuilder<HasName, HasPort>) -> Server:
    ...

# val s = build(builder())  # COMPILE ERROR: need HasName and HasPort
val s = build(builder().with_name("main").with_port(8080))   # OK
```

---

#### Use Case 4: Physical Units

```simple
struct Meters
struct Seconds
struct Kilograms

struct Quantity<Unit>:
    value: f64

fn add<U>(a: Quantity<U>, b: Quantity<U>) -> Quantity<U>:
    Quantity(value: a.value + b.value)

# mul requires dimension algebra — more complex; see section 2.4
```

---

#### Use Case 5: Capability/Permission Markers

```simple
struct ReadOnly
struct ReadWrite

struct File<Mode>:
    fd: i64

fn open_read(path: text) -> Result<File<ReadOnly>, text>: ...
fn open_write(path: text) -> Result<File<ReadWrite>, text>: ...

fn read(f: File<ReadOnly>, buf: [u8]): ...    # both modes can read
fn read(f: File<ReadWrite>, buf: [u8]): ...
fn write(f: File<ReadWrite>, data: [u8]): ...  # only ReadWrite can write
# fn write(f: File<ReadOnly>, data: [u8]): ... # would not compile
```

---

### 2.4 Pitfalls and Anti-Patterns

#### Pitfall 1: Type Parameter Explosion

States multiply: `Socket<Connected, Authenticated, Encrypted>` grows combinatorially.
For `n` independent binary states, you get `2^n` type combinations.

**Mitigation:** Only use phantom types for sequential state machines with few states.
Complex state should use explicit validation functions returning `Result`.

---

#### Pitfall 2: Cryptic Error Messages

```
error: expected TcpSocket<Connected>, found TcpSocket<Disconnected>
   --> main.spl:42:5
    |
42  |     send(s, data)
    |     ^^^^ type mismatch
```

This is an excellent error! But for complex phantom stacks:
```
error: expected ServerBuilder<HasName, HasPort>, found ServerBuilder<HasName, NoPort>
```

This requires good IDE tooling and diagnostic messages that name the missing state.

**Mitigation:** Include a `@state_description` annotation that produces human-readable
error messages. Design convention: phantom state names are nouns, not types.

---

#### Pitfall 3: Data-Dependent State

Phantom types only work for state that the compiler can track through the type system.
If state depends on runtime data, phantom types don't help:

```simple
fn authenticate(s: TcpSocket<Connected>, creds: Credentials) -> TcpSocket<Connected>:
    if verify(creds):
        # Can't return TcpSocket<Authenticated> based on runtime result!
        ...
```

**Mitigation:** Use `Result<TcpSocket<Authenticated>, Error>` to wrap the runtime check.
The phantom parameter changes only on success.

---

#### Pitfall 4: Covariance/Contravariance

In Rust, phantom type variance must be explicit via `PhantomData<T>` vs
`PhantomData<fn(T)>` vs `PhantomData<*const T>`. Incorrect variance can introduce
unsoundness (lifetime holes).

**Mitigation for Simple:** Until a borrow checker is added, treat all phantom parameters
as invariant by default (not covariant or contravariant). Document this explicitly.

---

#### Pitfall 5: Orphan Rules and External Types

Cannot add phantom parameters to types from external modules. Must wrap with a newtype.

---

#### Pitfall 6: Debugging Complexity

Runtime inspection doesn't reveal the phantom state. A debugger showing `TcpSocket` can't
tell you if it's `<Connected>` or `<Disconnected>` without source-level debug info.

**Mitigation:** Include phantom state in `@debug_display` implementation if present.

---

### 2.5 Proposed Design for Simple

#### Core Mechanism: Zero-Size State Markers

```simple
# Declare phantom state marker (zero bytes at runtime)
@phantom struct Connected
@phantom struct Disconnected
@phantom struct Authenticated

# Generic struct with phantom parameter
struct Connection<State>:
    socket: i64
    # State is not stored — phantom only

# State-specific functions
fn connect(c: Connection<Disconnected>, addr: text) -> Result<Connection<Connected>, text>: ...
fn send(c: Connection<Connected>, msg: text) -> Result<(), text>: ...
fn authenticate(c: Connection<Connected>, token: text) -> Result<Connection<Authenticated>, text>: ...
fn close(c: Connection<Connected>) -> Connection<Disconnected>: ...
```

#### Compiler Rules for @phantom Structs

1. `@phantom struct Foo` — zero-size type; no fields allowed
2. May only appear as type parameters, not as standalone values
3. Compiler errors include the phantom state name in the message
4. `@describe_state("Connection is not yet established")` for better error messages

#### Const State Dictionaries (Extend ConstKeySet)

The existing `ConstKeySet` in `src/lib/type/types.spl` can be extended to support
**phantom state keys** — a compile-time checked set of valid states:

```simple
@state_set(Disconnected, Connected, Authenticated)
struct Connection<State in ConnectionState>:
    socket: i64

# Compiler validates: State must be one of {Disconnected, Connected, Authenticated}
# This catches: Connection<Typo> at compile time
```

---

## Part 3: Introspection Framework — Three Tiers

The design principle: **pay only for what you use**. Three independent tiers, each
adding overhead but also capability.

### Tier 0: Zero-Overhead (Compile-Time + Binary Metadata)

**Runtime cost: ZERO**. All information is resolved at compile time. Binary-embedded
metadata is read-only and only accessed on crash/error.

#### What's in Tier 0

**Compile-time queries** (resolved to constants by the compiler):
```simple
val name = @type_name(Point)           # "Point" — text literal at compile time
val fields = @field_names(Point)       # ["x", "y"] — array literal at compile time
val field_types = @field_types(Point)  # ["i64", "i64"]
val is_struct = @is_struct(Point)      # true — bool at compile time
val has_field = @has_field(Point, "x") # true
val num_fields = @field_count(Point)   # 2
```

**Conditional compilation based on type:**
```simple
@when(@is_struct(T))
fn default_display(v: T) -> text:
    "@{@type_name(T) }}{ ... }}"  # auto-generate from fields

@when(@implements(T, Display))
fn show(v: T) -> text:
    v.to_string()
```

**DWARF debug info** — embedded in binary during compilation, zero CPU cost at runtime.
Used only when a crash/assert fires:
- Function names and addresses → function name lookup in stack traces
- Source file + line numbers → file:line in stack traces
- Variable names → local variable lookup in debugger

**Safety profile:** ✅ Zero overhead, all information read-only in binary.

---

#### Language Comparison — Zero-Overhead Reflection

| Language | Mechanism | Overhead |
|----------|-----------|----------|
| Zig | `comptime @typeInfo(T)` | Zero (compile-time) |
| D | `__traits(getMember, T, "field")` | Zero (compile-time) |
| Nim | `typetraits` + `when` | Zero (compile-time) |
| C++ | `std::type_traits`, `constexpr if` | Zero (compile-time) |
| Rust | proc-macro + `any::TypeId` | TypeId has tiny runtime cost |
| TypeScript | `typeof`, template literal types | Zero (compile-time) |
| Go | N/A — no comptime | N/A |
| Java | N/A — all runtime | N/A |

---

### Tier 1: Low-Overhead (Frame Pointer + Symbol Table)

**Runtime cost: ~1-3%** (frame pointer register preserved, small symbol table in binary).
Enables fast stack unwinding when assert/error fires. Suitable for production builds.

#### Mechanism

**Frame pointer preservation:** Compiler keeps `rbp` register on every function entry/exit.
Enables O(depth) stack walk without DWARF lookup (just follow the `rbp` chain).

```
Stack frame layout (with frame pointer):
[return address]
[saved rbp]  ← rbp points here
[local vars...]
```

Walking: `rbp → saved rbp → saved rbp → ...` gives return addresses for each frame.

**Compact symbol table:** Binary section `.simple_syms` maps address ranges to function
names. Much smaller than full DWARF:
```
[0x401000, 0x401050) -> "fn main"
[0x401050, 0x4010A0) -> "fn parse_config"
...
```

**Stack trace on assert:**
```simple
# When assert fires:
assert x > 0, "x must be positive"
# Output:
# assertion failed: x must be positive
# Stack trace (frame pointers):
#   0: fn validate_input at config.spl:42
#   1: fn load_config at main.spl:18
#   2: fn main at main.spl:5
```

**CLI flag:** `--keep-frame-pointers` (implied by `--debug`, optional in `--release`).
Go uses frame pointers by default (since Go 1.7). Linux perf tools require them.

---

#### Language Comparison — Frame Pointer Stack Traces

| Language | Default | Flag | Notes |
|----------|---------|------|-------|
| Go | ✅ Always | — | Frame pointers since 1.7 |
| Rust | ❌ Stripped in release | `-C force-frame-pointers=yes` | Must opt in |
| Python | N/A | — | Interpreter maintains stack |
| C++ | ❌ Stripped with -O2 | `-fno-omit-frame-pointer` | Perf tooling needs this |
| Zig | ❌ | `--single-threaded` + debug | DWARF in debug mode |
| Java | N/A | — | JVM maintains stack |

**Simple recommendation:** Keep frame pointers on by default (matching Go). The 1-3%
overhead is acceptable given the debugging benefit.

---

### Tier 2: Full Runtime Introspection (Opt-In)

**Runtime cost: ~5-15%** depending on usage. Requires explicit opt-in annotation or build flag.
Enables field enumeration, method lookup, dynamic dispatch, serialization.

**Only use when needed:** Serialization/deserialization, debuggers, test frameworks, REPL.

#### What's in Tier 2

**Runtime type registry** — built during program startup:
```simple
# Auto-registered by @reflect annotation
@reflect
struct Config:
    host: text
    port: i64
    timeout: f64

# Runtime reflection API:
val info = reflect_type("Config")?
for field in info.fields():
    print "{field.name}: {field.type_name}"
# Output:
# host: text
# port: i64
# timeout: f64
```

**Dynamic field access:**
```simple
val cfg = Config(host: "localhost", port: 8080, timeout: 30.0)
val host_field = reflect_get(cfg, "host")?  # → "localhost" as AnyValue
val port_field = reflect_get(cfg, "port")?  # → 8080 as AnyValue
reflect_set(cfg, "port", 9090)              # Dynamic set
```

**Use cases:** JSON serialization, REPL, test assertion printing, debugger watches.

#### Language Comparison — Full Reflection

| Language | Mechanism | Cost per use | Notes |
|----------|-----------|-------------|-------|
| Go | `reflect.TypeOf()` / `reflect.ValueOf()` | ~100-500ns | Heap alloc per call |
| Java | `Class.getDeclaredFields()` | ~10-50µs | JIT can inline some cases |
| Python | `inspect.getmembers()` | ~1-10µs | Everything is a dict |
| Swift | `Mirror(reflecting: x)` | ~200-500ns | Used by debugger/tests |
| Rust | `bevy_reflect` crate (opt-in) | ~50-200ns | Not in stdlib; game-engine focused |
| C# | `Type.GetProperties()` | ~500ns-5µs | JIT-cached after first call |
| Zig | None (comptime only) | N/A | No runtime reflection |

**Simple approach:** Follow Zig/Rust direction — prefer comptime (Tier 0) for
serialization. Add Tier 2 as an explicit opt-in library (`use std.reflect`) for
cases that genuinely need it.

---

## Part 4: Stack Traces — Zero to Full Coverage

### 4.1 The Three Stack Trace Modes

#### Mode A: Zero-Overhead (DWARF Post-Mortem)

**How it works:**
1. Compiler embeds DWARF debug sections in the binary (`.debug_info`, `.debug_line`, `.debug_frame`)
2. During normal execution: no overhead whatsoever (DWARF is in static read-only pages)
3. When assert/panic fires: signal handler reads DWARF to unwind the stack
4. DWARF lookup can take 10-100ms on first call (acceptable for crash reporting)

**Implementation for Simple:**
- Native backend already targets ELF — add `.debug_info` section generation
- On `assert` failure: call `rt_panic_with_dwarf(msg, pc, sp)` runtime function
- Runtime uses `libunwind` or `libdwfl` to unwind from the PC/SP registers
- Format trace with file:line from DWARF `.debug_line` section

**Binary size impact:** DWARF adds 20-100% to binary size. Stripping (`--strip-debug`)
removes it for release deployments (but no stack traces then).

**CLI flag:** `--debug-info` (default: on for debug, off for release)
**Opt back in for release:** `--release --keep-debug-info` (traces in production)

---

#### Mode B: Low-Overhead (Frame Pointers, ~1-3%)

Already described in Tier 1 of introspection. Add symbol table lookup:

```
On assert:
1. Read %rbp register (or equivalent)
2. Walk rbp chain: rbp[0] = saved_rbp, rbp[1] = return_address
3. For each return_address, binary-search `.simple_syms` for function name
4. Print: "  frame N: fn_name (approx — no file:line)"
```

For file:line accuracy, combine with a minimal line-number table (much smaller than full DWARF):
```
.simple_lines section:
fn_addr  file_id  start_line  end_line
0x4010   1        42          67
```

---

#### Mode C: Full Runtime Stack (Debug Only, ~5-10%)

Already designed in `src/lib/debug.spl` (StackFrame, Debugger.call_stack).
The missing piece is the **automatic push/pop instrumentation**:

```simple
# Current design (manual):
debugger.push_frame(StackFrame(fn_name: "my_fn", file: "foo.spl", line: 42, locals: []))
...body...
debugger.pop_frame()

# Proposed: compiler-instrumented automatically
@instrument_stack    # per-function annotation
# OR
--profile=debug-stack   # global flag adds instrumentation to all functions
```

**Implementation:** The compiler inserts push/pop calls around every function body when
the flag is active. Uses thread-local storage for the stack to avoid contention.

---

#### Mode D: Zig-Style Error Return Traces (Recommended for `?` Operator)

**Runtime cost on success path: ZERO. Cost on error path: O(depth) array writes.**

This is a fundamentally different approach from stack traces. Instead of capturing the
*call stack at the moment of error*, error return traces capture the *path an error takes
as it propagates back up through `?`/`try` expressions*.

**How Zig's error return traces work:**

1. A fixed-size trace buffer (`ErrorTrace { frames: [32]SourceLocation, depth: i64 }`)
   is allocated on `main`'s stack frame (not the heap — bounded, deterministic).
2. A thread-local pointer references the active trace buffer.
3. Every `try expr` is compiled to:
   ```zig
   // Instead of: try foo()
   // Compiles to:
   const result = foo();
   if (result == error.Something) {
       trace_buffer.push(@src());   // @src() is compile-time: file+line+column
       return result;               // propagate upward
   }
   ```
4. At the error handler (catch block, `main`, or test runner), the trace buffer holds
   the exact source locations where the error was propagated, innermost-first.

```zig
// Zig example:
fn inner() !void {
    return error.Fail;
}

fn middle() !void {
    try inner();    // if error: records "middle.zig:7" in trace buffer, then returns
}

fn outer() !void {
    try middle();   // if error: records "outer.zig:11" in trace buffer, then returns
}

pub fn main() !void {
    try outer();    // if error: records "main.zig:15", then runtime prints trace
}
```

**Output — "error return trace" (not a call stack):**
```
error: Fail
/src/inner.zig:2:5: note: called from here
/src/middle.zig:7:5: note: called from here
/src/outer.zig:11:5: note: called from here
/src/main.zig:15:5: note: called from here
```

This shows exactly which `try` expressions the error passed through — often more useful
than a full call stack because it directly traces the error's journey.

---

**Key advantages over traditional stack traces:**

| Property | Stack Trace (Modes A/B/C) | Error Return Trace (Mode D) |
|----------|--------------------------|------------------------------|
| Captures | Full call stack at crash | Only `?`/`try` propagation sites |
| Normal path overhead | 0–10% (DWARF/frame ptrs/instrumentation) | **Zero** |
| Error path overhead | High (DWARF lookup / frame walking) | **O(depth) array writes** |
| Heap allocation | Sometimes (DWARF resolver) | **Never** (stack-allocated buffer) |
| Deterministic size? | No | **Yes** (fixed buffer depth) |
| Works without DWARF? | Only with frame pointers | **Yes** (comptime `@file`/`@line`) |
| Works in release? | DWARF stripped by default | **Yes** always |
| Source location quality | Depends on debug info | **Always exact** (compile-time) |
| Shows full call chain? | Yes | No — only error path |
| Safety profile | ⚠️ DWARF may bloat binary | ✅ Bounded, stack-allocated |

---

**Perfect fit for Simple's `?` operator:**

Simple already has `?` which desugars to early return on `Err`. Every `?` site is where
an error return trace entry would be recorded:

```simple
fn parse_config(path: text) -> Result<Config, text>:
    val raw = file_read(path)?          # ← Mode D records this line on error
    val parsed = json_parse(raw)?       # ← Mode D records this line on error
    val config = validate_config(parsed)?  # ← records this line on error
    Ok(config)

fn main():
    val cfg = parse_config("config.json")?   # ← records this line on error
    run_server(cfg)
```

If `json_parse` returns an `Err`, the output is:
```
error: invalid JSON: unexpected token at column 42
  returned from: fn json_parse at parser.spl:88
  propagated at: fn parse_config at config.spl:3
  propagated at: fn main at main.spl:2
```

No frame walking. No DWARF. No heap. Just a thread-local pointer and array writes.

---

**Implementation design for Simple:**

```simple
# Trace buffer — stack-allocated in main, pointer stored thread-local
struct ErrorTrace:
    frames: [[text; 3]; 32]   # [file, line, function] × 32 slots
    depth: i64
    overflow: bool             # true if > 32 frames were propagated

extern fn rt_error_trace_push(file: text, line: i64, func: text)
extern fn rt_error_trace_get() -> ErrorTrace?
extern fn rt_error_trace_clear()
extern fn rt_error_trace_init()   # called at main entry
```

The `?` operator desugaring changes from:
```simple
# Current desugaring of `expr?`:
match expr:
    Ok(v): v
    Err(e): return Err(e)
```

To (with Mode D active):
```simple
# Mode D desugaring of `expr?`:
match expr:
    Ok(v): v
    Err(e):
        rt_error_trace_push(@file, @line, @function)
        return Err(e)
```

**CLI flags:**
- `--error-tracing` — enable Mode D (error return traces via `?`)
- `--error-trace-depth=N` — max trace depth (default 32)
- Implied by `--debug`; optional in `--release --error-tracing`

**Safety profile:** ✅ Ideal — bounded buffer, stack-allocated, zero overhead on success,
no heap, no DWARF dependency, deterministic behavior.

---

**Mode D vs. other modes — when to use which:**

| Scenario | Best Mode | Reason |
|----------|-----------|--------|
| Error propagation via `?` | **Mode D** | Exact error path, zero success-path cost |
| Assertion failures (`assert`) | **Mode A** or `@file/@line` | Panic, not a `?` site |
| Profiling / perf debugging | **Mode B** (frame ptrs) | Full call context |
| Development debugging | **Mode C** or **Mode D** | Both useful |
| Production + safety profile | **Mode D** | Bounded, no DWARF, zero overhead |
| Post-mortem crash analysis | **Mode A** (DWARF) | Full context without runtime cost |

**Recommendation:** Use Mode D as the **primary error tracing mechanism** for `?`-based
error propagation. Combine with `@file`/`@line` constants for `assert` panics (which
are not `?` sites). Mode A (DWARF) remains valuable for post-mortem crash dumps.

---

### 4.2 assert() and error_log() Design

```simple
# Zero-overhead assert — compiler knows file:line at call site
fn assert(condition: bool, msg: text):
    @inline_if(!condition):
        rt_panic(msg, @file, @line, @function)  # comptime source location
```

`@file`, `@line`, `@function` are compile-time constants at the call site, similar to C's
`__FILE__`, `__LINE__`, `__FUNCTION__`. They are baked into the binary as string literals.

```simple
# Low-overhead error_log — always prints with file:line, no stack trace unless Mode B/C
fn error_log(msg: text):
    rt_error_log(msg, @file, @line)  # always fast — just string lookup

# High-overhead error_log — adds stack trace in Mode B/C
fn error_log_traced(msg: text):
    rt_error_log_with_trace(msg, @file, @line)  # frame walk if frame-pointers enabled
```

---

### 4.3 Language Comparison — Error Traces

#### Stack Traces on Assertion/Panic

| Language | Default | Zero-overhead? | Production traces? |
|----------|---------|----------------|-------------------|
| Rust | DWARF (debug), none (release) | ✅ (DWARF) | opt-in with RUST_BACKTRACE=1 |
| Go | Always — goroutine stack | ⚠️ (frame ptrs ~2%) | ✅ Always |
| Zig | DWARF in debug + error return trace | ✅ (DWARF + Mode D) | Error return trace always |
| C++ | OS crash dump (no stdlib support) | ✅ (DWARF) | Manual libunwind |
| Java | JVM always maintains stack | ❌ | ✅ Always |
| Python | Interpreter always has stack | ❌ | ✅ Always |
| Swift | DWARF + dyld | ✅ | Crash reporter |
| Kotlin/JVM | JVM exception stack | ❌ | ✅ Always |

#### Error Return Traces (for `?`/`try` propagation) — Zig Comparison

| Property | Zig `try` error trace | Simple `?` (proposed Mode D) | Rust `?` |
|----------|----------------------|------------------------------|----------|
| Trace mechanism | comptime `@src()` + thread-local buffer | comptime `@file`/`@line` + thread-local | RUST_BACKTRACE (full stack) |
| Buffer allocation | Stack-allocated in `main` | Stack-allocated in `main` | Heap (Backtrace::capture) |
| Buffer size | Fixed (configurable) | Fixed 32 slots (configurable) | Unbounded |
| Success path cost | **Zero** | **Zero** | Zero (unless RUST_BACKTRACE=1) |
| Error path cost | One array write per `try` | One array write per `?` | Full stack capture |
| DWARF required | No | No | Yes |
| Works in release | ✅ Always | ✅ Always | ⚠️ Only with debug info |
| Safety profile | ✅ Bounded | ✅ Bounded | ⚠️ Unbounded heap |

**Simple recommendation:**
- **`?` error propagation:** Mode D (error return traces) — zero success-path cost, exact path
- **`assert` / panics:** `@file`/`@line` compile-time constants — no frame walk needed
- **Profiling/production optional:** `--keep-frame-pointers` for ~1-3% full context
- **Debug builds:** Mode C (full runtime stack) or Mode D — both useful
- **Post-mortem crash analysis:** Mode A (DWARF) — zero runtime cost, full context on crash

---

## Part 5: Modern Introspection Framework — Proposed Design

### 5.1 Design Principles

1. **Zero-overhead by default** — no runtime cost unless opted in
2. **Layered** — each tier is independent; use only what's needed
3. **Stable, minimal API** — avoid the Java reflection trap (reflection of everything)
4. **Source-mapped** — all errors include file:line from compile-time constants
5. **Safety-profile compatible** — Tier 0 always OK; Tier 1 with flag; Tier 2 explicit opt-in

### 5.2 Proposed Compile-Time Introspection API (Tier 0)

```simple
# Type queries — all resolved at compile time, zero runtime cost
@type_name(T)          # text — "Point", "Config", etc.
@is_struct(T)          # bool
@is_enum(T)            # bool
@is_class(T)           # bool
@has_field(T, "name")  # bool
@field_count(T)        # i64
@field_names(T)        # [text]
@field_types(T)        # [text] — as type name strings
@implements(T, Trait)  # bool — does T implement Trait?
@size_of(T)            # i64 — size in bytes

# Source location constants — embedded as literals at call site
@file                  # "src/main.spl"
@line                  # 42
@function              # "fn parse_config"
@module                # "app.config"

# Conditional compilation:
@when(@is_struct(T)):
    fn debug_print(v: T):
        print "@{@type_name(T) }}{ display_fields(v) }}"  # auto-generated

@when_not(@implements(T, Display)):
    fn safe_to_string(v: T) -> text:
        "{@type_name(T) }} (no Display)"
```

### 5.3 Proposed Runtime Introspection API (Tier 1 / Tier 2)

```simple
# Tier 1 — type name only (always available with frame pointers)
use std.introspect.{type_name_of}

val name = type_name_of(value)   # → "Config" — runtime string lookup

# Tier 2 — full reflection (requires @reflect annotation or --reflect flag)
use std.reflect.{reflect_type, reflect_get, reflect_set}

@reflect
struct Config:
    host: text
    port: i64

val info = reflect_type("Config")?  # → TypeInfo
for field in info.fields():
    print "  {field.name}: {field.type_name} = {reflect_get(cfg, field.name)}"
```

### 5.4 Stack Trace and Error Return Trace API

```simple
# Zero-overhead assert (comptime file:line baked in — Mode A equivalent)
assert x > 0              # → rt_panic("assertion failed", @file, @line, @function)
check x > 0               # same thing

# Error logging with source location (always fast — no stack walk)
error_log "Connection failed"   # → prints "[ERROR] src/db.spl:42: Connection failed"

# Mode D — error return trace via ? (zero success-path cost)
# This is automatic when --error-tracing is active:
fn load(path: text) -> Result<Data, text>:
    val raw = file_read(path)?      # on error: records this line in trace buffer
    val data = parse(raw)?          # on error: records this line in trace buffer
    Ok(data)

# Access the error return trace after a ? propagates to the handler:
use std.error_trace.{get_error_trace, format_error_trace, clear_error_trace}

fn main():
    clear_error_trace()             # reset trace buffer at handler
    match load("data.json"):
        Ok(d): run(d)
        Err(msg):
            val trace = get_error_trace()
            print "Error: {msg}"
            print format_error_trace(trace)

# Mode B — full call stack (frame pointers, ~1-3%)
use std.stack.{capture_trace, format_trace}

fn risky_operation():
    if something_wrong:
        val trace = capture_trace()  # walks rbp chain
        error_log "Error: {format_trace(trace)}"
```

### 5.5 Integration with Phantom Types

```simple
# Phantom types use compile-time introspection for error messages:
@phantom struct Connected
@phantom struct Disconnected

struct Socket<State>:
    fd: i64
    @phantom_field state: State   # zero bytes, pure type info

fn send(s: Socket<Connected>, data: [u8]):
    # Compiler error when called with Socket<Disconnected>:
    # error[E0308]: phantom state mismatch
    #   expected: Socket<Connected>
    #   found:    Socket<Disconnected>
    #   help: call connect() first to get a Socket<Connected>
    ...
```

The `@state_description` annotation provides the "help" text:
```simple
@phantom struct Disconnected:
    @state_description "call connect() to obtain Socket<Connected>"
```

---

## Part 6: Language Comparison Summary

### Compile-Time Checking

| Feature | Rust | Zig | Haskell | TypeScript | F# | D | Swift | Go | **Simple** |
|---------|------|-----|---------|------------|----|----|-------|----|----|
| Static assert | ✅ (const) | ✅ (comptime) | ✅ | ✅ (type-level) | ✅ | ✅ | ✅ | ❌ | Proposed |
| Phantom types | ✅ (PhantomData) | ✅ (comptime) | ✅ (newtype) | ⚠️ (branding) | ✅ (units) | ✅ | ⚠️ | ❌ | Proposed |
| Exhaustiveness | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ❌ | Proposed |
| Must-use | ✅ (#[must_use]) | ✅ (error union) | ✅ (linear) | ⚠️ | ✅ | ⚠️ | ⚠️ | ❌ | Proposed |
| Format strings | ✅ (macro) | ✅ (comptime) | ⚠️ | ⚠️ | ✅ | ✅ | ⚠️ | ⚠️ | Proposed |
| Unit checking | ⚠️ (crate) | ⚠️ | ⚠️ | ❌ | ✅ | ⚠️ | ❌ | ❌ | Proposed |

### Introspection

| Feature | Rust | Zig | Go | Java | Swift | TypeScript | **Simple** |
|---------|------|-----|----|------|-------|------------|------------|
| Compile-time type info | proc-macro | ✅ @typeInfo | ❌ | ❌ | ❌ | ✅ types | Proposed Tier 0 |
| Runtime type name | TypeId | ❌ | reflect | ✅ | Mirror | ❌ | Proposed Tier 1 |
| Full runtime reflection | bevy_reflect (opt-in) | ❌ | reflect | ✅ | Mirror | ❌ | Proposed Tier 2 |
| Stack traces (assert) | DWARF | DWARF + @src() | Frame ptr | JVM | DWARF | Source maps | Mode A (DWARF) + @file/@line |
| Error return traces (`?`) | RUST_BACKTRACE (heavy) | ✅ `try` + @src() | ❌ | Exceptions | ❌ | ❌ | **Mode D (Zig-style) — primary** |

---

## Part 7: Pitfalls & Anti-Patterns Catalog

### Category A: Phantom Type Pitfalls

1. **State explosion:** `n` boolean states → `2^n` types. Keep phantom state to ≤4 states.
2. **Cryptic errors:** Type names in errors must be designed to be readable, not just correct.
3. **Data-dependent state:** Phantom types can't encode state that depends on runtime values.
4. **Covariance unsoundness:** Incorrect variance can create lifetime holes (Rust-specific).
5. **No runtime recovery:** Can't inspect phantom state at runtime (by design).
6. **Orphan types:** Can't add phantom params to external types without newtype wrappers.

### Category B: Compile-Time Check Pitfalls

7. **Increased compile time:** Type-level computation can be expensive (Haskell is infamous).
8. **Turing-complete types:** Rust trait recursion can loop forever; need termination checks.
9. **Complexity cliff:** Simple code becomes unreadable when CT checks accumulate.
10. **False positives:** Overly strict CT checks reject valid programs (annoying).
11. **Error cascade:** One type error can produce 50 downstream errors.
12. **Maintenance burden:** CT constraints must be updated when APIs change.

### Category C: Reflection Pitfalls

13. **Breaks encapsulation:** Reflection can read private fields, violating access control.
14. **ABI fragility:** Reflected field names break when renamed (no rename-safe names).
15. **Performance surprises:** Reflection allocates; developers don't expect this.
16. **Prevents optimization:** Compiler can't inline or devirtualize reflected calls.
17. **Security risks:** Reflection can bypass access controls in security-sensitive contexts.
18. **Hidden errors:** Reflected code fails at runtime, not compile time.

### Category D: Stack Trace Pitfalls

19. **DWARF bloat:** Full DWARF doubles binary size; must support strip-debug for release.
20. **Inlined functions:** Inlining removes frames — traces miss intermediate calls.
21. **TCO removes frames:** Tail-call optimization eliminates frames from traces.
22. **Debug info in production:** If release strips DWARF, production traces are useless.
23. **First-unwind latency:** DWARF lookup can take 10-100ms on first crash — acceptable but notable.
24. **Thread-unsafe stack walker:** Frame pointer walking must handle concurrent modification.
25. **DWARF correctness:** Generated DWARF must be correct or debuggers crash.

### Category E: Error Return Trace (Mode D) Pitfalls

26. **Shows propagation path, not call path:** If `foo()` returns `Err` without a `?`, it's not in the trace.
    The error return trace only shows `?` sites — not all callers. Can be confusing initially.
27. **Buffer overflow for deep chains:** If `?` chains exceed the buffer depth (default 32), oldest
    entries are dropped. Must tune `--error-trace-depth` for very deep call chains.
28. **Interop with non-Result APIs:** SFFI / C functions that return error codes (not `Result`)
    won't appear in the trace. Need explicit `?` wrapping at FFI boundary to participate.
29. **Multiple concurrent traces:** Multi-threaded programs need per-thread trace buffers
    (thread-local). Must ensure `rt_error_trace_init()` is called per thread.
30. **Clear/reset discipline:** If `clear_error_trace()` isn't called before each `?`-chain entry
    point, old frames contaminate new errors. Requires structured handler discipline.
31. **Not useful for panics/asserts:** Error return traces only record `?` propagation.
    For assertion failures and panics, `@file`/`@line` + Mode A/B/C are still needed.

---

## Part 8: Priority Matrix

| Feature | Impact | Complexity | Zero-Cost? | Safety Profile | Recommended |
|---------|--------|------------|-----------|----------------|-------------|
| @file/@line/@function constants | HIGH | LOW | ✅ | ✅ | **Do First** |
| Static assert (@static_assert) | HIGH | LOW | ✅ | ✅ | **Do First** |
| **Mode D: Error return trace (`?`)** | **HIGH** | **LOW** | **✅ on success** | **✅ bounded** | **Do First** |
| Exhaustiveness checking | HIGH | MEDIUM | ✅ | ✅ | **Do First** |
| Frame pointer preservation (Mode B) | HIGH | LOW | ⚠️ ~1-3% | ✅ | Next phase |
| DWARF stack traces on panic (Mode A) | MEDIUM | MEDIUM | ✅ | ✅ | Next phase |
| Phantom types (basic) | MEDIUM | MEDIUM | ✅ | ✅ | Next phase |
| Format string validation | HIGH | MEDIUM | ✅ | ✅ | Next phase |
| @must_use annotation | MEDIUM | LOW | ✅ | ✅ | Next phase |
| Compile-time type introspection (@type_name, etc.) | MEDIUM | HIGH | ✅ | ✅ | Medium-term |
| Physical unit checking | MEDIUM | HIGH | ✅ | ✅ | Future |
| API state machines (builder phantom) | MEDIUM | HIGH | ✅ | ✅ | Future |
| Full runtime reflection (Tier 2) | LOW | HIGH | ❌ | ❌ | Future (opt-in only) |
| Linear/affine types | MEDIUM | VERY HIGH | ✅ | ✅ | Future (research first) |

**Mode D elevated to "Do First"** because:
- Zero code changes to normal code paths — only the `?` desugaring changes
- Runtime cost bounded and deterministic (stack-allocated fixed buffer)
- No DWARF, no frame walkers, no heap allocation
- Works in release builds out of the box
- Directly addresses the most common debugging scenario (error propagation through `?`)

---

## Appendix: Connection to Existing Code

### A1. Extending ConstKeySet (existing `src/lib/type/types.spl`)

The current `ConstKeySet(keys: [text])` type can be extended to support phantom state
validation:

```simple
# Current (in types.spl):
ConstKeySet(keys: [text])          # dict key validation

# Proposed extension:
PhantomStateSet(valid_states: [text])  # phantom type parameter validation

# validate_phantom_state checks T is in the declared state set
fn validate_phantom_state(type_param: text, valid_states: [text]) -> ConstKeyValidation:
    ...
```

### A2. Stack Trace Infrastructure (existing `src/lib/debug.spl`, `src/lib/report/runtime/panic.spl`)

Both files have the data structures but lack the capture implementation:
- `debug.spl`: `StackFrame` struct (fn_name, file, line, locals)
- `panic.spl`: `StackTrace` and `PanicReport` classes — fully designed

**For Mode D (error return traces — recommended primary approach):**
The existing `StackTrace`/`StackFrame` can be reused with compile-time source locations:
```simple
# New SFFI for error return trace buffer
extern fn rt_error_trace_push(file: text, line: i64, func: text)
extern fn rt_error_trace_get_frames() -> [[text]]   # [[file, line, func], ...]
extern fn rt_error_trace_clear()
extern fn rt_error_trace_init(max_depth: i64)       # call at main() start

# Desugaring of `expr?` with --error-tracing:
# match expr: Ok(v): v  Err(e): rt_error_trace_push(@file, @line, @function); return Err(e)
```

**For Mode A (DWARF post-mortem stack trace):**
```simple
extern fn rt_capture_stack_trace_frames(max_depth: i64) -> [[text]]
# Returns array of [fn_name, file, line_str] tuples via DWARF lookup
```

### A3. Effect System (existing `src/lib/type/effects.spl`)

The effect system already enforces `@io`, `@pure`, etc. Phantom types integrate naturally:
functions that transition socket state should be `@io`. The effect checker can validate
that state-transition functions aren't used in `@pure` contexts.

---

## Conclusion

The path forward for Simple's type safety and observability:

### Immediate (Quick Wins)
1. Add `@file`, `@line`, `@function` compile-time constants — foundation for all error messages
2. Implement `assert` using these constants — zero overhead, file:line always present
3. Implement **Mode D (Zig-style error return traces)** for `?` desugaring — highest value, lowest cost
   - `rt_error_trace_push/get/clear/init` SFFI functions in the runtime
   - `--error-tracing` flag; implied by `--debug`
   - Reuse `StackTrace`/`StackFrame` from `src/lib/report/runtime/panic.spl`
4. Add `@static_assert` for compile-time condition checking

### Short-Term (Next Quarter)
5. Enable frame pointer retention by default (`--keep-frame-pointers` / Mode B)
6. Add phantom type support (`@phantom struct`, `struct Foo<State>` with state constraints)
7. Validate format strings in interpolation (`{x:.2f}` type-checked)
8. Add exhaustiveness checking to `match` (compile error for missing enum variants)
9. Add `@must_use` annotation (extends existing ignored-return-value warning)

### Medium-Term (Research Required)
10. Compile-time type introspection (`@type_name`, `@fields`, `@has_field`)
11. DWARF generation in the native backend (Mode A — for post-mortem crash analysis)
12. Physical unit checking (F#-style `@unit` system)

### Long-Term (Careful Design Required)
12. Full API state machine phantom types with good error messages
13. Linear/affine types for resource safety
14. Optional full reflection library (Tier 2) for serialization/REPL use cases

Simple's direction — no exceptions, no inheritance, explicit error handling, strong types —
aligns perfectly with this framework. Each proposed feature strengthens that philosophy
without compromising the language's simplicity.

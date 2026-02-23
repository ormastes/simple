# Sentinel-Terminated Types for Simple

**Date:** 2026-02-18
**Status:** Design Research
**Author:** Zig Embedded Features Initiative
**Related docs:**
- `doc/research/zig_embedded_features_2026-02-18.md` — overview of 10 Zig embedded features (sentinel = item #10)
- `doc/research/missing_language_features_2026-02-17.md` — grammar analysis, safety profiles
- `doc/research/introspection_phantom_types_2026-02-17.md` — phantom types (relevant to sentinel marker design)
- `doc/research/baremetal_embedded_research_2026-02-05.md` — embedded context: bitfields, volatile, ISR

---

## Overview

A **sentinel-terminated type** is a type where the end of a sequence is marked by a distinguished value (the sentinel) rather than by an explicit length field. The canonical example is the C null-terminated string: a sequence of bytes ended by a `\0` (NUL, byte value 0). The type system, rather than programmer convention, guarantees the sentinel is present.

Sentinel-terminated types matter for several reasons in embedded and systems programming:

1. **C interoperability.** The vast majority of C APIs take `char*` or `const char*` — null-terminated strings. Calling `strlen`, `strcpy`, `puts`, `printf`, or any POSIX file-path function requires a null-terminated byte sequence. Without a type-level guarantee, the programmer must manually append `\0` and hope it survives the API boundary.

2. **Hardware protocol framing.** Many communication protocols and hardware descriptors use sentinel bytes to delimit records — NMEA GPS sentences end with `\r\n`, some DMA ring buffers use a sentinel descriptor to mark the end of the ring, and serial protocol frames often end with an end-of-frame byte.

3. **Read-until-sentinel loops.** Loops of the form "read bytes until you see byte X" are common in parsers, deserialization, and firmware. If the type system knows the sentinel is present, it can statically rule out infinite-loop failure modes.

4. **Binary size.** Storing a length word alongside every string costs 8 bytes per string on a 64-bit platform. For ROM tables with hundreds of short strings, null termination costs one byte per string instead.

**Zig's design principle:** Sentinel values are part of the *type*, not a runtime contract. `[:0]u8` and `[*:0]u8` are different types from `[]u8` and `[*]u8`, and the compiler enforces the distinction statically. This document analyzes how to bring this concept to Simple.

---

## Zig's Sentinel Type Syntax

Zig provides four related constructs for sentinel-terminated types. Understanding these precisely is essential before designing Simple equivalents.

### 2.1 `[:0]u8` — Sentinel-Terminated Slice (Known Length)

```zig
const hello: [:0]u8 = "hello";   // string literal is [:0]u8 by default
// hello.len == 5, but hello[5] == 0 (sentinel is guaranteed)

fn greet(name: [:0]const u8) void {
    const len = std.mem.len(name);  // scans for \0, returns 5
    // OR use name.len (the known length, excludes sentinel)
}
```

Key properties:
- `.len` is the count of *non-sentinel* elements (known, stored)
- `ptr[len]` is guaranteed to equal the sentinel value
- Creating a `[:0]u8` from a plain `[]u8` requires an explicit cast that adds the sentinel
- The type parameter `0` is the sentinel value — it can be any `u8` comptime constant

### 2.2 `[:0]const u8` — Const Sentinel-Terminated Slice

```zig
const msg: [:0]const u8 = "immutable string";
// Equivalent to C's `const char*` with null termination guaranteed
```

String literals in Zig have type `*const [N:0]u8` (pointer to array with sentinel). They coerce to `[:0]const u8` automatically.

### 2.3 `[*:0]u8` — Many-Pointer with Sentinel (Unknown Length)

```zig
extern fn strlen(s: [*:0]const u8) usize;
// s is a pointer to an unknown number of bytes, terminated by \0
// The compiler knows nothing about the length — iterating requires scanning

fn c_to_zig(c_str: [*:0]const u8) [:0]const u8 {
    return c_str[0..std.mem.len(c_str) :0];  // converts to known-length form
}
```

This is analogous to C's `char*`. It is less safe than `[:0]u8` because:
- No `.len` field — must scan to find length, O(N)
- Can't slice without first finding the sentinel
- Useful for extern declarations wrapping C APIs

### 2.4 Arbitrary Sentinel Values

The sentinel does not have to be 0. The sentinel value is a comptime constant of the element type:

```zig
// Slice terminated by newline
const line: [:'\n']u8 = get_line();

// Terminated by 0xFF (common in some hardware protocols)
const frame: [*:0xFF]u8 = read_uart_frame();

// Terminated by a custom sentinel struct value
const records: [*:end_record]Record = get_records();
```

### 2.5 How Zig Verifies the Sentinel

At a **slice creation site**, Zig's compiler emits a safety check (in debug mode):

```zig
const s: [:0]u8 = some_buf[0..len :0];
// Debug mode: assert(some_buf[len] == 0), panic if not
// Release mode: unchecked (trusts programmer)
```

For **string literals**, the compiler guarantees the sentinel — no runtime check needed. For **extern declarations**, the programmer asserts the C code upholds the contract.

---

## Current Simple Language Status

### 3.1 The `text` Type

Simple's `text` type is the primary string type. From examining `src/compiler_core/types.spl` and `src/app/io/mod.spl`:

```simple
# text is a built-in opaque type
# Internally stored as a length-prefixed UTF-8 string in the runtime heap
# Built-in methods: .len(), .starts_with(), .ends_with(), .contains(), []
val greeting = "Hello, world!"
val n = greeting.len()          # returns i64 (byte count)
val ch = greeting[0]            # returns text (single character slice)
val sub = greeting[0:5]         # slice notation (requires s[0:end] not s[:end])
```

Key facts about `text`:
- It is **length-prefixed**, not null-terminated, internally. The runtime stores `(length, data_ptr)`.
- It is **not a byte array** — it is an opaque runtime value. You cannot take a raw pointer to `text` contents.
- There is no `i8` or `u8` type in Simple (bytes are represented as `i64` or `text` of length 1).
- String literals are always `text`, never `[:0]u8`.

**Consequence:** Simple's `text` cannot be passed directly to C APIs that expect `char*`, because:
1. The internal representation may not be null-terminated.
2. There is no mechanism to take a pointer to the underlying bytes.
3. The runtime may move objects (depending on GC strategy).

### 3.2 Current Slice Syntax

Simple uses `[Type]` for slice/array types:

```simple
val bytes: [i64] = [72, 101, 108, 108, 111]   # array of i64
val names: [text] = ["Alice", "Bob", "Carol"]   # array of text
```

There is no distinction between "slice" (fat pointer: ptr + length) and "array" (owned buffer) at the syntax level. Both use `[Type]`.

Fixed-size arrays use `[Type; N]` (proposed, not yet fully implemented).

### 3.3 C Interop — Current SFFI Mechanism

From `src/app/io/mod.spl`, the current SFFI pattern for C strings is:

```simple
extern fn rt_env_get(key: text) -> text
extern fn rt_read_volatile_i64(addr: i64) -> i64
extern fn rt_write_volatile_i64(addr: i64, value: i64)
```

The runtime bridges `text` ↔ `const char*` internally at the SFFI boundary. This works for the built-in runtime functions because the Simple runtime itself is written in C/C++ and knows the `text` memory layout. It does **not** work for arbitrary third-party C libraries, because:

1. There is no way to declare "this `text` must be null-terminated when passed to C"
2. There is no way to express `[*:0]u8` as a type for an `extern fn` parameter
3. The runtime conversion may copy the string and add a null terminator — but this is an internal implementation detail, not a language guarantee

### 3.4 Current Newtype Syntax

From `MEMORY.md` and `test/unit/parser/newtype_spec.spl`, `newtype` is implemented as a parser feature:

```simple
newtype CStr = [i64]      # Would create a wrapper struct with a single `value` field
```

The `newtype` feature creates a zero-overhead wrapper with a single `value` field. This is the foundation for the Option B design below.

### 3.5 Existing `phantom.spl` Pattern

From `src/lib/phantom.spl`, Simple already has phantom type markers:

```simple
struct Validated:
    """Phantom marker: data has been validated."""
    _phantom: i64

struct Unvalidated:
    """Phantom marker: data has NOT been validated yet."""
    _phantom: i64
```

This pattern — using struct wrappers to carry compile-time guarantees — is directly applicable to sentinel types.

---

## Grammar Interaction Analysis

This is the critical blocking issue. Any syntax for sentinel types in Simple must avoid conflicting with existing grammar productions.

### 4.1 Dict/Map Syntax Conflict: `[key: value]`

Simple uses `[key: value]` syntax for map/dict literals:

```simple
val point = [x: 3, y: 4]         # dict literal
val config = [host: "localhost", port: 8080]
```

The parser, when it sees `[`, looks ahead for a `:` to determine if this is a dict literal or an array literal. If `[:0]u8` were parsed, the token sequence would be:

```
TOK_LBRACKET  TOK_COLON  TOK_INT(0)  TOK_RBRACKET  TOK_IDENT(u8)
```

The parser would attempt to interpret `[:` as the beginning of a dict literal with an empty key — which is a parse error. Even if the parser were extended to handle this, `[:0]` looks like a dict with key = symbol `:0` (see conflict 4.2 below).

**Verdict:** Zig's exact `[:0]u8` syntax cannot be adopted without significant grammar surgery.

### 4.2 Symbol Literal Conflict: `:ident`

In Simple, `:ident` is a symbol/atom literal:

```simple
val sym = :ok           # symbol literal
val mode = :read_write  # symbol literal
match status:
    :ok: handle_ok()
    :error: handle_error()
```

The colon-prefix creates a symbol. Applied to a numeric literal: `:0` would be attempting to create a symbol named `0`, which is invalid (symbols must be identifiers). The tokenizer would reject `:0` as a symbol, or produce a confusing error.

**Verdict:** Even if map literal conflict (4.1) were resolved, `:0` is not a valid Simple token sequence for a sentinel value.

### 4.3 Slice Range Conflict: `s[0:end]`

Simple slice notation uses `[start:end]`:

```simple
val sub = greeting[0:5]    # slice from index 0 to 5 (exclusive)
val tail = greeting[2:]    # slice from index 2 to end
```

The `s[:end]` form (no start index) causes a known parser bug documented in `MEMORY.md`:

> **`[:var]` parsed as symbol:** `s[:idx]` fails — colon before identifier = symbol literal. Use `s[0:idx]` always.

This means `[:0]` in a *value context* already fails. In a *type context*, the same ambiguity applies.

### 4.4 Current Slice Type Production

The current type grammar (from examining `src/compiler_core/parser.spl` implicitly via docs) handles:

```
type_expr  ::= "[" type_expr "]"           # slice type: [T]
             | "[" type_expr ";" expr "]"   # fixed-size array: [T; N]
             | ...
```

Adding `[:S]T` would require:

```
type_expr  ::= "[" ":" expr "]" type_expr   # sentinel slice: [:S]T  (CONFLICTS)
             | "[" type_expr ":" expr "]"   # sentinel slice: [T:S]   (new syntax)
             | "[" type_expr "]"            # plain slice: [T]
             | ...
```

The first form `[:S]T` conflicts with all three grammar issues above (4.1, 4.2, 4.3). The second form `[T:S]` avoids the leading-colon problem but may conflict with the dict literal grammar if the parser sees `[ident:` and expects dict.

### 4.5 Summary of Grammar Conflicts

| Syntax | Conflict | Severity |
|--------|----------|----------|
| `[:0]u8` (Zig style) | Dict literal `[key: val]`, symbol `:0`, slice bug `[:var]` | FATAL — three separate conflicts |
| `[u8:0]` (postfix) | Potential dict literal `[ident: val]` confusion | MODERATE — parser disambiguable |
| `[*:0]u8` (pointer form) | Same as `[:0]u8` plus pointer-to-many confusion | FATAL |
| `SentinelSlice<u8, 0>` | None — fits existing generics syntax | NONE |
| `newtype CStr = [i64]` | None — existing newtype syntax | NONE |
| `@sentinel(0) [i64]` | None — annotation syntax | NONE |

---

## Proposed Syntax Options

### Option A: `SentinelSlice<T, N>` Generic Type

Define `SentinelSlice` as a built-in or standard-library generic type:

```simple
# Type declarations
val cstr: SentinelSlice<i64, 0> = cstr_from_text("hello")
fn greet(name: SentinelSlice<i64, 0>):
    extern_puts(name)

# C interop declaration
extern fn rt_puts(s: SentinelSlice<i64, 0>) -> i64
extern fn rt_strlen(s: SentinelSlice<i64, 0>) -> i64

# With type alias for convenience
type CStr = SentinelSlice<i64, 0>
fn greet(name: CStr):
    extern_puts(name)
```

**Pros:**
- Zero grammar conflicts. Fits the existing `<>` generics syntax exactly.
- The sentinel value `N` is expressed as a type parameter — naturally a compile-time constant.
- Can be implemented as a library type without compiler changes (Phase 1/2).
- Works with current generics implementation (`MEMORY.md`: generics fully working in interpreter + compiler).
- `type CStr = SentinelSlice<i64, 0>` gives ergonomic shorthand for the common case.
- Self-documenting: `SentinelSlice<u8, '\n'>` clearly conveys "terminated by newline".

**Cons:**
- Verbose at the use site. `SentinelSlice<i64, 0>` is 22 characters vs Zig's `[:0]u8` (6 characters).
- The sentinel value `N` in `SentinelSlice<T, N>` requires the type parameter to be a *value*, not a type. This is a value-in-type-position, which most type systems handle separately from type parameters. Simple's current generics (`<T>`) are type parameters. Passing `0` as a type parameter requires value generics (similar to Rust's `const generics` or C++ NTTP).
- Without value generics, `SentinelSlice<i64, 0>` and `SentinelSlice<i64, 255>` would be the same type — losing the type-level distinction.

**Compatibility:** Works with current generics if `SentinelSlice` is defined as a struct with a `data: [i64]` field and the sentinel is stored as metadata (not a type parameter). Loses type-safety between different sentinels but remains safe for the null-termination use case.

**Workaround for missing value generics:**

```simple
# Approach A1: Separate types for common sentinels (no value generics needed)
struct CStr:          # null-terminated byte sequence (sentinel = 0)
    data: [i64]
    length: i64

struct LineStr:       # newline-terminated (sentinel = '\n' = 10)
    data: [i64]
    length: i64

struct FrameBytes:    # 0xFF-terminated (common in some protocols)
    data: [i64]
    length: i64
```

This loses generality but is immediately implementable.

---

### Option B: `CStr` / `ZStr` Newtype

Use the `newtype` feature to define a named wrapper that encodes the null-termination invariant:

```simple
newtype CStr = [i64]
# Creates: struct CStr: value: [i64]
# With a single `value` field holding the underlying byte array

# Constructor enforces invariant
fn cstr(s: text) -> CStr:
    val bytes = text_to_bytes(s)    # convert text to [i64]
    val with_null = bytes + [0]     # append null terminator
    CStr(value: with_null)

# Length (excluding null terminator)
fn cstr_len(s: CStr) -> i64:
    s.value.len() - 1

# Convert back to text
fn cstr_to_text(s: CStr) -> text:
    bytes_to_text(s.value[0:cstr_len(s)])

# C interop — SFFI boundary
extern fn c_puts(s: CStr) -> i64
extern fn c_strlen(s: CStr) -> i64
extern fn c_strcpy(dst: CStr, src: CStr) -> CStr
```

**Pros:**
- Immediately implementable with *zero* compiler changes. `newtype` already works.
- Clean, readable API: `fn greet(name: CStr):` is as ergonomic as Zig's `fn greet(name: [:0]const u8)`.
- The type name (`CStr`, `ZStr`, `NullTermBytes`) is self-documenting.
- Constructor (`cstr(s)`) is the single enforcement point — invariant maintained in one place.
- Works within the existing runtime limitations documented in `MEMORY.md`.
- Follows the existing `phantom.spl` pattern of using struct wrappers for compile-time guarantees.

**Cons:**
- Limited to one sentinel value per named type. `CStr` = null-terminated; a newline-terminated type needs a separate `LineTermBytes` newtype.
- Not general: cannot write `fn read_until<S: sentinel>(buf: SentinelSlice<i64, S>)` — no abstraction over sentinel values.
- The runtime does not know that `CStr.value` is null-terminated — it is a programmer promise. No static verification that the null is actually appended.
- `newtype CStr = [i64]` means `CStr` wraps `[i64]` (array of i64). For real C interop, you need actual `u8` bytes, not i64. Simple lacks a `u8` type, so `i64` is the closest (with values clamped to 0-255).

**Example full implementation:**

```simple
newtype CStr = [i64]

fn cstr_from_text(s: text) -> CStr:
    var bytes: [i64] = []
    var i = 0
    while i < s.len():
        bytes.push(char_code(s[i]))
        i = i + 1
    bytes.push(0)              # null terminator
    CStr(value: bytes)

fn cstr_len(s: CStr) -> i64:
    var i = 0
    while i < s.value.len():
        if s.value[i] == 0:
            return i
        i = i + 1
    s.value.len()              # malformed: no null found, return full length

fn cstr_equals(a: CStr, b: CStr) -> bool:
    val la = cstr_len(a)
    val lb = cstr_len(b)
    if la != lb:
        return false
    var i = 0
    while i < la:
        if a.value[i] != b.value[i]:
            return false
        i = i + 1
    true

export CStr, cstr_from_text, cstr_len, cstr_equals
```

---

### Option C: Postfix Sentinel Marker `[i64:0]`

Use a suffix syntax where the sentinel value follows the element type inside the brackets:

```simple
val cstr: [i64:0]   # slice of i64 terminated by 0
val line: [i64:10]  # slice of i64 terminated by 10 (LF = newline)
val frame: [i64:255] # slice of i64 terminated by 0xFF
```

The grammar change required:

```
type_slice ::= "[" type_expr "]"              # plain slice [T]
             | "[" type_expr ":" expr "]"     # sentinel slice [T:N]
             | "[" type_expr ";" expr "]"     # fixed-size array [T;N]
```

**Pros:**
- Shorter than Option A at use sites: `[i64:0]` vs `SentinelSlice<i64, 0>`.
- Postfix avoids the leading-colon conflicts (4.1, 4.2, 4.3).
- Generalizes naturally: any sentinel value, any element type.
- Consistent with the existing `[T; N]` fixed-size array syntax (uses same bracket pair).
- Visually similar to Zig's `[:0]T` but rearranged to avoid conflicts.

**Cons:**
- New grammar production required — parser change in `src/compiler_core/parser.spl`.
- Risk of conflict: `[ident:expr]` could be parsed as a single-element dict literal `{ident: expr}`. The parser must distinguish `[i64:0]` (sentinel type) from `["key": 0]` (dict literal). This requires lookahead: if the first token after `[` is a type name (uppercase or primitive keyword), treat as type; if it is a string literal or lowercase identifier, treat as dict/array.
- In expression context, `arr[i64:0]` would be ambiguous with indexing. Sentinel types should only appear in *type positions*, not expression positions, but the parser would need to know which context it is in.
- The `0` in `[i64:0]` is a value in a type position — requires the type checker to evaluate it as a compile-time constant.
- Range expressions like `s[0:n]` already use `expr:expr` inside brackets. The type position `[i64:0]` uses `type:expr`. The parser must distinguish based on context (type context vs expression context).

**Grammar change needed:** Add to `parse_type()`:

```
parse_type():
    if peek() == LBRACKET:
        consume LBRACKET
        inner_type = parse_type()
        if peek() == COLON:
            consume COLON
            sentinel_val = parse_expr()    # must be compile-time constant
            consume RBRACKET
            return SentinelSliceType(inner_type, sentinel_val)
        elif peek() == SEMICOLON:
            consume SEMICOLON
            size_expr = parse_expr()
            consume RBRACKET
            return FixedArrayType(inner_type, size_expr)
        else:
            consume RBRACKET
            return SliceType(inner_type)
```

**Risk assessment:** MODERATE. The grammar change is localized to `parse_type()`. Expression parsing (slicing) is unaffected because slicing is parsed in expression context, not type context.

---

### Option D: Annotation-Based `@sentinel(0) [i64]`

Use Simple's annotation system to attach sentinel metadata to a type or declaration:

```simple
# On variable declarations
@sentinel(0)
val cstr: [i64] = bytes

# On function parameters
fn greet(@sentinel(0) name: [i64]):
    extern_puts_bytes(name)

# On extern declarations
extern fn c_puts(@sentinel(0) s: [i64]) -> i64
extern fn c_strlen(@sentinel(0) s: [i64]) -> i64
```

**Pros:**
- Zero grammar changes. Annotation syntax (`@name(args)`) is already parsed and handled.
- Completely backward-compatible — `[i64]` retains its existing semantics; `@sentinel(0)` adds intent metadata.
- Can be used today without any implementation: serves as documentation until the type system enforces it.
- Consistent with other annotation usage: `@volatile`, `@repr(C)`, `@link_section`.

**Cons:**
- Sentinel is NOT part of the type. `[i64]` and `@sentinel(0) [i64]` are the same type — the compiler cannot reject passing a plain `[i64]` where `@sentinel(0) [i64]` is expected.
- Cannot be enforced at compile time without adding type-system support (which negates the grammar simplicity advantage).
- Awkward for function parameters — `@sentinel(0)` applies to the declaration, not the type, making it hard to use in `type` aliases.
- Does not compose: `type CStr = @sentinel(0) [i64]` is not valid syntax.

**Use case:** Option D is best treated as a *transitional notation* — use `@sentinel(0)` as a documentation annotation today, and upgrade to Option B (`newtype CStr`) or Option C (`[i64:0]`) once a richer type system is in place.

---

## Interaction with Comptime

### 5.1 Why Sentinel Values Must Be Compile-Time Constants

The sentinel value must be known at compile time for two reasons:

1. **Type identity.** `SentinelSlice<i64, 0>` and `SentinelSlice<i64, 10>` are different types. Type identity requires the sentinel value to be fixed at compile time, not determined at runtime.

2. **Code generation.** The comparison `element == sentinel` in a "read until sentinel" loop must use a constant operand. The compiler can optimize this to a `SCAS` instruction (x86 string scan) or equivalent — but only if the sentinel is a compile-time constant.

### 5.2 Simple's Current Comptime Status

From `doc/research/zig_embedded_features_2026-02-18.md` (item #1):

> **Status: SYNTAX_ONLY** — parsed as runtime val/fn. No actual compile-time evaluation. `comptime val` evaluates at module load time (runtime), not compile time.

This means Simple cannot currently guarantee that `0` in `SentinelSlice<i64, 0>` is a compile-time constant in the strong Zig sense. However:

```simple
val SENTINEL_NULL = 0       # Module-level val — effectively a constant
val SENTINEL_NEWLINE = 10   # Standard newline byte

type CStr = SentinelSlice<i64, SENTINEL_NULL>
```

Module-level `val` bindings in Simple are evaluated once at module load time and never change. For practical purposes (interpreter mode, JIT, native compilation), they behave as compile-time constants for the sentinel use case.

### 5.3 Interaction with `const fn`

Once `const fn` evaluation is implemented (it is currently SYNTAX_ONLY), sentinel values could be computed by `const fn`:

```simple
const fn ascii(c: text) -> i64:
    char_code(c[0])

type NewlineTerminated = SentinelSlice<i64, ascii("\n")>
```

For now (pre-comptime), sentinel values should be:
- Integer literals (`0`, `255`, `10`)
- Module-level `val` or `const` bindings

### 5.4 `cstr_len` Without Comptime

A length function for a sentinel-terminated slice cannot use a compile-time loop bound without comptime:

```simple
# Without comptime: O(N) scan at runtime
fn cstr_len(s: CStr) -> i64:
    var i = 0
    while i < s.value.len():
        if s.value[i] == 0:
            return i
        i = i + 1
    s.value.len()    # fallback if sentinel missing
```

The `while` loop limitation (documented in `MEMORY.md` — `while` fails inside `it` blocks) does not apply here since `cstr_len` is a module-level function, not a closure. The pattern is valid.

---

## Safety Analysis

### 6.1 The Buffer Overrun Risk

Sentinel-terminated types introduce a specific safety hazard not present with length-prefixed types: if the sentinel is missing or corrupted, a "read until sentinel" loop will overrun the buffer. For length-prefixed types (`text` in Simple), the `.len()` bound prevents this. Sentinel-terminated types shift the safety burden.

| Failure Mode | Length-Prefixed (`text`) | Sentinel-Terminated (`CStr`) |
|-------------|--------------------------|------------------------------|
| Missing terminator | Not possible (length is authoritative) | Buffer overrun — reads until random `\0` found |
| Length corruption | Read wrong number of bytes (bounded) | N/A |
| Buffer too small | Can detect: `src.len() > dst.capacity` | Cannot detect without max-length param |
| C API misuse | Runtime string copy handles it | Caller must guarantee null terminator present |

### 6.2 Comparison with Zig's Safety Model

Zig takes a two-tier approach to sentinel type safety:

- **Debug mode:** Runtime assertion at slice creation — `assert(buf[len] == sentinel)`. Panics if violated.
- **Release mode:** Assertion elided. Trusts the programmer (or type system) that the sentinel is present.

Simple's current runtime has no equivalent debug-mode assertion mechanism for slices. There is no panic-on-sentinel-missing checking. This places Simple closer to C's model (trust the programmer) than Zig's (verify in debug, trust in release).

**Recommendation for Simple:** For `CStr` newtype (Option B, immediate path), the constructor function `cstr_from_text(s: text) -> CStr` is the single invariant-enforcement point. It unconditionally appends `\0`. Any `CStr` created through the public API is guaranteed to have the sentinel. Corruption (e.g., via direct `value` field mutation) is the programmer's responsibility.

### 6.3 Max-Length Parameter Recommendation

For safety in embedded contexts (where buffers are fixed-size), any function that reads a sentinel-terminated sequence should accept an optional maximum length:

```simple
fn cstr_len_bounded(s: CStr, max_len: i64) -> i64:
    var i = 0
    while i < s.value.len() and i < max_len:
        if s.value[i] == 0:
            return i
        i = i + 1
    i    # returns max_len if sentinel not found within bound

fn cstr_copy_bounded(src: CStr, max_len: i64) -> CStr:
    val copy_len = cstr_len_bounded(src, max_len - 1)  # -1 for null terminator
    var out: [i64] = []
    var i = 0
    while i < copy_len:
        out.push(src.value[i])
        i = i + 1
    out.push(0)
    CStr(value: out)
```

This mirrors POSIX's `strncpy`/`strnlen` design — provide both unbounded and bounded variants, and prefer bounded in safety-critical code.

### 6.4 Safety Profile Compatibility

From `doc/research/missing_language_features_2026-02-17.md` — safety profile analysis:

| Aspect | Safety Profile Policy |
|--------|----------------------|
| `CStr` newtype | Recommended — explicit, type-safe, no hidden allocation |
| Unbounded `cstr_len` | Disallowed in `--profile=safety` — must use `cstr_len_bounded` |
| Sentinel-terminated slices in FFI | Allowed — explicit `extern fn` boundary |
| Sentinel slice mutation after creation | Disallowed — invariant must be maintained |
| `[i64:0]` grammar syntax | Acceptable if sentinel value is compile-time constant |

---

## Zig Comparison Table

| Feature | Zig | Simple (Current) | Simple (Proposed) |
|---------|-----|-----------------|-------------------|
| Null-terminated string | `[:0]u8` | `text` (opaque, length-prefixed) | `CStr` newtype (Option B) |
| Sentinel slice | `[:N]T` | Not supported | `SentinelSlice<T, N>` generic (Option A) or `[T:N]` syntax (Option C) |
| Sentinel pointer (unknown length) | `[*:0]T` | Not supported | Future work (requires pointer type) |
| C string interop | `@ptrCast([:0]u8, ptr)` | `extern fn rt_*(s: text)` (opaque bridge) | `CStr` + `extern fn c_*(s: CStr)` |
| Arbitrary sentinel value | `[:'\n']u8`, `[*:0xFF]u8` | Not supported | `SentinelSlice<i64, 10>` or named newtypes |
| Sentinel in type | Yes — part of type identity | No | Option A (partial), Option C (full) |
| Compile-time sentinel verification | Yes (debug assertions) | No | Constructor-level check (Option B) |
| Length excluded from sentinel | `s.len` excludes sentinel | N/A | `cstr_len(s)` scans to sentinel |
| Grammar conflict with existing syntax | None in Zig | Fatal for `[:0]T` | None for Options A, B, D; moderate for C |
| Ergonomics at use site | High (`[:0]u8`) | N/A | Moderate (Option B: `CStr`), lower (Option A: `SentinelSlice<i64, 0>`) |
| Runtime safety check | Debug: panic on missing sentinel | None | Constructor guarantee (Option B) |

---

## Implementation Roadmap

### Phase 1 — Immediate: `CStr` Newtype in `src/lib/`

**Effort:** Low (1-2 hours)
**Requires:** No compiler changes. Uses existing `newtype` syntax, `[i64]` arrays, `while` loops.
**Deliverable:** `src/lib/cstr.spl` module with:

```simple
newtype CStr = [i64]

fn cstr_from_text(s: text) -> CStr: ...
fn cstr_len(s: CStr) -> i64: ...
fn cstr_len_bounded(s: CStr, max_len: i64) -> i64: ...
fn cstr_to_text(s: CStr) -> text: ...
fn cstr_equals(a: CStr, b: CStr) -> bool: ...
fn cstr_copy_bounded(src: CStr, max_len: i64) -> CStr: ...
fn cstr_concat(a: CStr, b: CStr) -> CStr: ...
fn cstr_from_bytes(bytes: [i64]) -> CStr: ...    # validates null terminator present
```

Test file: `test/unit/std/cstr_spec.spl`

**SFFI declarations for C interop (`src/app/io/mod.spl` addition):**
```simple
extern fn rt_cstr_puts(s: CStr) -> i64
extern fn rt_cstr_strlen(s: CStr) -> i64
```

**Limitation:** The runtime must be updated to understand `CStr` at the SFFI boundary. Until then, pass `s.value` (the raw `[i64]`) to existing runtime functions.

### Phase 2 — Medium-Term: `SentinelSlice<T, N>` via Struct + Constants

**Effort:** Low-to-Medium (no compiler changes for struct approach)
**Strategy:** Define `SentinelSlice` as a standard library struct rather than a true generic with value parameters.

```simple
# src/lib/sentinel_slice.spl

struct SentinelSlice:
    """A slice with a sentinel value at the end.
    The `sentinel` field stores the expected terminator byte.
    The `data` field stores the payload including the sentinel.
    """
    data: [i64]
    sentinel_val: i64
    length: i64       # number of non-sentinel elements

fn sentinel_slice_new(data: [i64], sentinel: i64) -> SentinelSlice:
    """Construct a SentinelSlice. Validates that sentinel is present."""
    var len = 0
    var i = 0
    while i < data.len():
        if data[i] == sentinel:
            len = i
            return SentinelSlice(data: data, sentinel_val: sentinel, length: len)
        i = i + 1
    # Sentinel not found — append it
    var with_sentinel = data + [sentinel]
    SentinelSlice(data: with_sentinel, sentinel_val: sentinel, length: data.len())

# Type aliases for common cases
fn null_terminated(data: [i64]) -> SentinelSlice:
    sentinel_slice_new(data, 0)

fn newline_terminated(data: [i64]) -> SentinelSlice:
    sentinel_slice_new(data, 10)
```

**Limitation:** `SentinelSlice` with different sentinel values are the same type — the compiler cannot distinguish `null_terminated` from `newline_terminated` by type alone. This is an ergonomic limitation, not a safety regression (compared to current no-sentinel state).

### Phase 3 — Long-Term: Grammar-Level `[T:N]` Syntax

**Effort:** Medium-High. Requires changes to:
- `src/compiler_core/parser.spl` — add sentinel slice to `parse_type()`
- `src/compiler_core/ast.spl` — add `EXPR_SENTINEL_SLICE_TYPE` AST node
- `src/compiler_core/entity/ast/arena.spl` — storage for sentinel AST nodes
- `src/compiler_core/interpreter/eval.spl` — evaluate `[T:N]` types
- `src/compiler_core/types.spl` — sentinel type representation

**Grammar addition to `parse_type()` in `src/compiler_core/parser.spl`:**

```
parse_type_slice():
    consume LBRACKET
    inner_type = parse_type()
    if peek() == COLON:
        consume COLON
        sentinel_expr = parse_primary_expr()    # must be integer literal or const name
        consume RBRACKET
        return mk_sentinel_slice_type(inner_type, sentinel_expr)
    elif peek() == SEMICOLON:
        consume SEMICOLON
        size_expr = parse_expr()
        consume RBRACKET
        return mk_fixed_array_type(inner_type, size_expr)
    consume RBRACKET
    return mk_slice_type(inner_type)
```

**Risk:** The `[T:N]` form with `T` being an identifier creates an ambiguity with `[key: value]` dict syntax. The parser must be updated to distinguish type context from expression context. This is manageable because `parse_type()` is only called when the parser knows it is parsing a type (after `:` in a declaration, after `->` in a function signature, in `newtype` declarations, etc.).

**AST node addition:**
```simple
# In src/compiler_core/ast.spl
val EXPR_SENTINEL_SLICE_TYPE = 47   # [T:N] sentinel-terminated slice type node
```

**When to implement:** After Phase 2 validates the concept and use cases, and after comptime evaluation (feature #1) is available to verify sentinel values at compile time.

---

## Conclusion

### Summary of Findings

1. **Zig's exact syntax (`[:0]u8`) is incompatible with Simple's grammar** due to three independent conflicts: dict literal syntax `[key: val]`, symbol literals `:ident`, and the documented `[:var]` parser bug. This syntax cannot be adopted without breaking changes.

2. **The `CStr` newtype approach (Option B) is immediately implementable** using the existing `newtype` and `[i64]` features. It provides ergonomic, type-safe null-terminated strings for C interop without any compiler changes. This is the recommended first step.

3. **The `SentinelSlice<T, N>` generic approach (Option A)** is implementable as a library struct but loses type-level distinction between different sentinel values without value generics support. It is a stepping stone toward full sentinel type support.

4. **The `[T:N]` postfix syntax (Option C)** is the cleanest long-term design. It avoids the leading-colon conflicts, fits the existing slice type grammar pattern, and generalizes naturally to any element type and sentinel value. It requires a grammar change (parser, AST, eval) and should be deferred to Phase 3.

5. **The annotation approach (Option D)** is useful as transitional documentation but provides no compile-time enforcement. Use `@sentinel(0)` as a comment on intent until Phase 1 or Phase 2 is in place.

6. **Comptime dependency is real but manageable.** Sentinel values should be compile-time constants, but Simple's module-level `val` bindings serve this role adequately until true comptime evaluation (feature #1) is implemented.

7. **Safety requires bounded variants.** Any `CStr` or `SentinelSlice` API should provide bounded-length variants (`cstr_len_bounded`, `cstr_copy_bounded`) for use in safety-critical or embedded contexts where buffers are fixed-size.

### Recommended Path Forward

| Phase | Action | Effort | Compiler Change? |
|-------|--------|--------|-----------------|
| 1 (now) | Create `src/lib/cstr.spl` — `CStr` newtype + API | Low | None |
| 1 (now) | Create `test/unit/std/cstr_spec.spl` | Low | None |
| 2 (soon) | Create `src/lib/sentinel_slice.spl` — generic struct | Low | None |
| 2 (soon) | Add `@sentinel(N)` annotation support in SFFI layer | Low | Annotation wiring only |
| 3 (later) | Grammar-level `[T:N]` syntax | Medium-High | Parser + AST + Eval |
| 3 (later) | Value generics for `SentinelSlice<T, N>` | High | Type system change |

**Immediate action:** Implement `src/lib/cstr.spl` as a `newtype CStr = [i64]` with a complete API for null-terminated byte sequences. This unblocks C interop use cases today and provides a reference implementation for the future grammar-level design.

### Related Design Docs

- `doc/research/zig_embedded_features_2026-02-18.md` — item #10 (sentinel types) + item #1 (comptime, prerequisite for value-generic sentinel)
- `doc/research/introspection_phantom_types_2026-02-17.md` — phantom type patterns (newtype wrapper technique)
- `doc/research/missing_language_features_2026-02-17.md` — grammar analysis, safety profiles
- `doc/research/baremetal_embedded_research_2026-02-05.md` — embedded context motivating sentinel types
- `doc/design/compile_time_features_design_2026-02-18.md` — comptime design (value-in-type-position prerequisite)

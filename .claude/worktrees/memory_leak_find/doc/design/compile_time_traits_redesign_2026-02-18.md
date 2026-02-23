# Compile-Time Traits System — Redesign after D Language Research
# 2026-02-18

**Status:** ✅ COMPLETE — Implemented 2026-02-18
**Supersedes:** `compile_time_features_design_2026-02-18.md` (Phase 4+)
**Based on:** D language `__traits` research — see `doc/research/introspection_phantom_types_2026-02-17.md`

---

## Executive Summary

The original design proposed `keyof T` (TypeScript-inspired) as the primary compile-time introspection tool.
After researching D's `__traits` system, we redesign around a unified `@traits(query, T, ...)` interface
that is **significantly more powerful**:

| Capability | Original plan | New design (D-inspired) |
|-----------|--------------|------------------------|
| Field names | `keyof T` → `["x", "y"]` | `@traits(fields, T)` → `[text]` |
| All members | ❌ Not designed | `@traits(all_members, T)` → `[text]` |
| Capability test | ❌ Not designed | `@traits(compiles, expr)` → `bool` |
| Enum variants | `exhaustiveness check` (implicit) | `@traits(enum_members, E)` → `[text]` |
| Field access by name | ❌ Not designed | `@traits(get_member, obj, "f")` → value |
| Annotation query | `@must_use` check only | `@traits(get_annotations, sym)` → `[text]` |
| Compile-time iteration | ❌ Not designed | `static_for K in @traits(fields, T):` |
| Compile-time code gen | ❌ Not designed | `mixin(code_text)` |
| CTFE | ❌ Not designed | `comptime expr` |
| Compile-time debug print | `@static_assert` only | `pragma_msg(expr)` |

**`keyof T`** is kept as syntax sugar for `@traits(fields, T)` (the token was already added).
Everything else is now part of the `@traits` system.

---

## Part 1: Architecture — Three Layers Like D

```
Layer 1: @traits(query, T, ...) — compiler built-ins
    fields, methods, all_members, has_member, get_member, compiles,
    enum_members, is_struct, is_class, is_enum, is_fn,
    get_annotations, identifier, member_type, ...

Layer 2: is_*(T) type predicates — pattern matching
    is_struct(T), is_class(T), is_enum(T), is_fn(T),
    is_integral(T), is_text(T), is_bool(T), is_array(T),
    converts_to(From, To), has_interface(T, Trait)

Layer 3: std.traits — ergonomic library wrappers
    field_names(T), method_names(T), member_type(T, field), has_field(T, f),
    field_count(T), has_annotation(sym, name), get_annotation(sym, name)

Orchestration: static_for, comptime, mixin, pragma_msg
    — compose layers into code generation
```

---

## Part 2: `@traits` Built-In Queries (Layer 1)

### 2.1 Member Enumeration

```simple
# Field names (memory-occupying fields only, like D's tupleof)
@traits(fields, Point)           # → ["x", "y"]
@traits(fields, Config)          # → ["host", "port", "timeout"]

# Method names (fn/me methods on the type)
@traits(methods, Debugger)       # → ["add_breakpoint", "remove_breakpoint", ...]

# All members: fields + methods + static fns + constants
@traits(all_members, Config)     # → ["host", "port", "timeout", "connect", "disconnect"]

# Check existence
@traits(has_member, Config, "host")    # → true
@traits(has_member, Config, "missing") # → false

# Get field value by name at runtime
@traits(get_member, config_obj, "host")  # → text value of host field
@traits(set_member, config_obj, "host", "localhost")  # set field by name
```

### 2.2 Capability Testing

```simple
# Does this expression compile? (like D's __traits(compiles, ...) / Rust's trait bounds)
@traits(compiles, x + 1)         # → true if x is numeric
@traits(compiles, obj.save())    # → true if obj has a save() method
@traits(compiles, T(field: 0))   # → true if T has a field named 'field'

# Check if a type constraint holds
@traits(has_interface, T, Serialize)   # → true if T implements Serialize trait
@traits(has_interface, T, Comparable) # → true if T has compare(other: T) -> i64
```

### 2.3 Type Classification

```simple
@traits(is_struct, T)    # → bool
@traits(is_class, T)     # → bool
@traits(is_enum, T)      # → bool
@traits(is_fn, T)        # → bool
@traits(is_array, T)     # → bool
@traits(is_dict, T)      # → bool

# Enum variant names
@traits(enum_members, Status)   # → ["Ok", "Warn", "Error"]
@traits(enum_count, Status)     # → 3

# Numeric type predicates
@traits(is_integral, T)   # → bool (i64, u8, i32, etc.)
@traits(is_float, T)      # → bool (f64, f32)
@traits(is_numeric, T)    # → bool (integral or float)
```

### 2.4 Member Metadata

```simple
# Type of a field (returns type name as text)
@traits(member_type, Config, "port")     # → "i64"
@traits(member_type, Config, "host")     # → "text"

# Annotations on a symbol
@traits(get_annotations, my_fn)          # → ["@must_use", "@pure"]
@traits(has_annotation, my_fn, "must_use") # → bool

# Symbol identity
@traits(identifier, Config.host)         # → "host"
@traits(type_name, Config)               # → "Config"
@traits(module_name, Config)             # → "app.config"
```

### 2.5 Source Location (from Phase 1 — unchanged)

```simple
@traits(file)       # → text: current file path  (alias: @file)
@traits(line)       # → i64: current line number  (alias: @line)
@traits(function)   # → text: current function name  (alias: @function)
```

---

## Part 3: `keyof T` — Kept as Syntax Sugar

`keyof T` is syntax sugar for `@traits(fields, T)`. The token `TOK_KW_KEYOF=200` was already added.

```simple
keyof Config         # exactly equivalent to @traits(fields, Config)
# → ["host", "port", "timeout"]
```

**Design decision:** Keep `keyof` because it's ergonomic for the common case of field name access,
consistent with TypeScript familiarity, and does NOT conflict with `@traits(fields, T)`.

---

## Part 4: `static_for` — Compile-Time Loop Unrolling

D's `static foreach` iterates at compile time, generating a copy of the loop body for each element.
Simple's equivalent: `static_for K in expr:` (a new statement type).

```simple
# Iterate over all field names — generate code for each
static_for field in @traits(fields, T):
    val v = @traits(get_member, obj, field)
    result.push("{field}: {v}")

# Equivalent to (with T = Point having fields x, y):
#   val v0 = @traits(get_member, obj, "x"); result.push("x: {v0}")
#   val v1 = @traits(get_member, obj, "y"); result.push("y: {v1}")
```

**Key property:** The loop body is generated ONCE per element, at compile time.
`field` is a compile-time constant text in each copy. This enables generic serialization
without any annotations on the target type.

### Generic Serialization Example (the killer use case)

```simple
# Zero-annotation serializer — works on ANY struct
fn to_json<T>(obj: T) -> text:
    var parts = []
    static_for field in @traits(fields, T):
        val v = @traits(get_member, obj, field)
        parts.push("{field}: {v}")
    "{" + parts.join(", ") + "}"

struct Point: x: i64, y: i64
struct Config: host: text, port: i64

print to_json(Point(x: 3, y: 4))   # → {x: 3, y: 4}
print to_json(Config(host: "localhost", port: 8080))  # → {host: localhost, port: 8080}
```

---

## Part 5: CTFE — Compile-Time Function Execution

Like D and Zig's `comptime`, allow ordinary Simple functions to run at compile time
when their inputs are compile-time constants.

### 5.1 `comptime` Expression

```simple
# comptime forces evaluation at compile/module-load time
val LOOKUP_TABLE: [i64] = comptime build_table(256)
val OPTIMAL_SIZE: i64 = comptime compute_size()

fn build_table(n: i64) -> [i64]:
    var result = []
    for i in 0..n:
        result.push(i * i % 97)
    result

fn compute_size() -> i64:
    # Runs at compile time — pure computation
    if PLATFORM_64BIT: 64 else: 32
```

**Restrictions (like D's CTFE):**
- Function must be "pure" (no I/O, no mutable globals)
- No extern fn calls inside comptime expressions
- Infinite recursion → compile error

### 5.2 `comptime` Block

```simple
# Block-level comptime: run setup code at module load time (before any fn call)
comptime:
    @static_assert(@traits(has_member, Config, "host"), "Config must have 'host' field")
    @static_assert(@traits(fields, Config).len() > 0, "Config must have at least one field")
    pragma_msg("Loaded module with " + text(@traits(fields, Config).len()) + " Config fields")
```

### 5.3 `pragma_msg` — Compile-Time Debug Print

```simple
pragma_msg("Compiling module...")
pragma_msg(@traits(fields, Config))       # prints: ["host", "port", "timeout"]
pragma_msg(@traits(type_name, T))         # prints: "Config"
pragma_msg(sizeof(T))                     # prints: 24
```

Like D's `pragma(msg, ...)` — output appears during compilation, zero runtime cost.

---

## Part 6: `mixin(code_text)` — Compile-Time Code Generation

The most powerful D feature: compile a string as source code at compile time.
Simple's version uses `mixin` with a text expression (CTFE-evaluatable).

```simple
# Generate getter/setter pairs
fn gen_property(type_name: text, name: text) -> text:
    "fn get_{name}(self) -> {type_name}: self.{name}\n" +
    "me set_{name}(v: {type_name}): self.{name} = v"

class Person:
    name: text
    age: i64
    mixin(gen_property("text", "name"))
    mixin(gen_property("i64", "age"))
# Equivalent to manually writing get_name(), set_name(), get_age(), set_age()
```

**Auto-implement `to_text()` for any struct:**
```simple
fn gen_to_text<T>() -> text:
    var parts = []
    static_for field in @traits(fields, T):
        parts.push('parts.push("{field}=" + text(self.{field}))')
    'fn to_text(self) -> text:\n    var parts = []\n' + parts.join("\n") + '\n    parts.join(", ")'

class Config:
    host: text
    port: i64
    mixin(gen_to_text<Config>())  # Generates to_text() automatically
```

---

## Part 7: `is_*(T)` Type Predicates — Layer 2

Higher-level type predicates (like D's `std.traits` boolean templates):

```simple
# Basic structural checks
is_struct(T)     # @traits(is_struct, T) — field-based aggregate
is_class(T)      # @traits(is_class, T) — method + fields
is_enum(T)       # @traits(is_enum, T) — variant type
is_fn(T)         # @traits(is_fn, T) — function type

# Numeric kinds
is_integral(T)   # i64, i32, i8, u8, ...
is_float(T)      # f64, f32
is_numeric(T)    # integral or float

# Collection types
is_array(T)      # [T]
is_dict(T)       # {K: V}
is_option(T)     # T? / Option<T>

# Conversion / compatibility
converts_to(From, To)       # implicit conversion available
has_interface(T, Trait)     # T has all methods required by Trait

# Compound — used for template constraints
static_if is_struct(T) and @traits(has_member, T, "id"):
    fn find_by_id(coll: [T], id: i64) -> T?:
        for item in coll:
            if @traits(get_member, item, "id") == id:
                return item
        nil
```

---

## Part 8: `std.traits` Library Module — Layer 3

Ergonomic wrappers built on `@traits`, like D's `std.traits`:

```simple
# src/lib/traits.spl
use core.traits.*

fn field_names<T>() -> [text]:
    @traits(fields, T)

fn method_names<T>() -> [text]:
    @traits(methods, T)

fn all_member_names<T>() -> [text]:
    @traits(all_members, T)

fn field_count<T>() -> i64:
    @traits(fields, T).len()

fn has_field<T>(name: text) -> bool:
    val fields = @traits(fields, T)
    for f in fields:
        if f == name: return true
    false

fn member_type_name<T>(field: text) -> text:
    @traits(member_type, T, field)

fn has_annotation<T>(sym_name: text, annotation: text) -> bool:
    val anns = @traits(get_annotations, sym_name)
    for a in anns:
        if a == annotation: return true
    false

fn get_annotation<T>(sym_name: text, annotation: text) -> text?:
    val anns = @traits(get_annotations, sym_name)
    for a in anns:
        if a.starts_with(annotation): return a
    nil

# Like D's getSymbolsByUDA — find all fields with an annotation
fn fields_with_annotation<T>(annotation: text) -> [text]:
    var result = []
    static_for field in @traits(fields, T):
        if @traits(has_annotation, T.field, annotation):
            result.push(field)
    result
```

---

## Part 9: Revised Implementation Plan

### Phase 1 (unchanged — already partially implemented)
- `@file`, `@line`, `@function` (alias: `@traits(file)`, `@traits(line)`, `@traits(function)`)
- `@static_assert`
- `@must_use`
- Exhaustiveness checking (uses `@traits(enum_members, T)` internally)

### Phase 2 (unchanged — already partially implemented)
- `src/lib/error_trace.spl`
- `src/lib/phantom.spl`

### Phase 3 — Core `@traits` System (NEW, replaces old Phase 4)

**Priority order:**

#### 3.1 `@traits(fields, T)` — Most Critical
- Returns `[text]` of field names for any struct/class
- `keyof T` desugars to `@traits(fields, T)`
- Implementation: struct definition is stored in AST; field names accessible at eval time
- **This single feature unlocks generic serialization**

#### 3.2 `@traits(has_member, T, "name")` — Essential
- Boolean check: does T have a field/method named "name"?
- Used in template constraints and `static_if`

#### 3.3 `@traits(get_member, obj, "name")` — High Value
- Runtime field access by string name
- Unlocks: generic display, generic comparison, serialization
- Implementation: look up field name in struct's field map at runtime

#### 3.4 `@traits(compiles, expr)` — Capability Detection
- Try to type-check `expr`; return `true` if it compiles
- Used for: optional interface detection, SFINAE-like template constraints

#### 3.5 `@traits(enum_members, E)` — Exhaustiveness Foundation
- Returns `["Ok", "Warn", "Error"]` for an enum
- Powers exhaustiveness checking in match statements

#### 3.6 `@traits(is_struct/class/enum/fn, T)` — Type Classification
- Boolean predicates for structural type dispatch

#### 3.7 `@traits(get_annotations, sym)` — Annotation Query
- Returns `["@must_use", "@pure"]` for annotated symbols
- Enables metadata-driven generic code

### Phase 4 — `static_for` Compile-Time Iteration

**The second most critical feature** — without it, `@traits(fields, T)` is hard to USE.

```simple
static_for field in @traits(fields, T):
    # field is a compile-time constant text in each loop body copy
    val v = @traits(get_member, obj, field)
    result.push("{field}: {text(v)}")
```

Implementation:
- New token: `TOK_KW_STATIC_FOR`
- Parser: `static_for IDENT in EXPR:` → `STMT_STATIC_FOR` with body
- Eval: expand body N times with field = fields[0], fields[1], ..., fields[N-1]
- Each expansion is type-checked independently

### Phase 5 — CTFE and `pragma_msg`

- `comptime expr` — evaluate any pure expression at module-load time
- `pragma_msg(expr)` — print during compilation for debugging generics

### Phase 6 — `mixin(code_text)` — Code Generation

- Most powerful feature but highest complexity
- Enables: auto-derive, ORM mapping, route registration

### Phase 7 — `std.traits` Library

- Build ergonomic wrappers on top of core `@traits` system

---

## Part 10: Token Additions

The following new tokens need to be added:

| Token | Constant | In keyword_lookup | Parser |
|-------|---------|-----------------|--------|
| `keyof` | TOK_KW_KEYOF = 200 | ✅ Done | ❌ Needs parser |
| `static_for` | TOK_KW_STATIC_FOR = 201 | ❌ Needed | ❌ Needed |
| `comptime` | TOK_KW_COMPTIME = 202 | ❌ Needed | ❌ Needed |
| `mixin` | TOK_KW_MIXIN = 203 | ❌ Needed | ❌ Needed |
| `pragma_msg` | (fn, not keyword) | N/A | N/A |

**`@traits`** uses existing `@` + identifier dispatch — NO new keyword needed.

---

## Part 11: O(1) Analysis Update

All new keywords (`static_for`, `comptime`, `mixin`) go into their first-character groups:
- `static_for` → group 's' (already has `static`, `struct`, `self`, `spawn`) → +1 comparison
- `comptime` → group 'c' (already has `class`, `case`, `const`, `continue`) → +1 comparison
- `mixin` → group 'm' (already has `match`, `me`) → +1 comparison

**`@traits(...)` requires ZERO new keywords** — uses the `@` annotation dispatch (already O(1)).
This is the biggest advantage of the `@traits(query, ...)` design over individual keywords per feature.

---

## Part 12: Comparison with Original Design

| Feature | Original plan | Redesign | Change |
|---------|--------------|----------|--------|
| Field names | `keyof T` | `@traits(fields, T)` + `keyof` sugar | Same power, more unified |
| Mapped types | `{ for K in keyof T: K: T[K] }` | Use `static_for` + `mixin` | More general |
| Capability test | ❌ | `@traits(compiles, expr)` | **NEW** |
| Generic serializer | ❌ | `static_for` + `@traits(get_member, ...)` | **NEW** |
| Enum variant list | Exhaustiveness only | `@traits(enum_members, E)` | Promoted to first-class |
| Annotation query | `@must_use` hardcoded | `@traits(get_annotations, sym)` | **NEW** |
| Code generation | ❌ | `mixin(code_text)` | **NEW** |
| CTFE | ❌ | `comptime expr` | **NEW** |
| Debug print | `@static_assert` only | `pragma_msg(expr)` | **NEW** |
| `std.traits` module | ❌ | Full library module | **NEW** |

---

## Conclusion

D's compile-time reflection system is more unified and powerful than TypeScript's type-level system.
The key architectural insight is: **one mechanism (`@traits`) subsumes dozens of special cases**.

The minimum viable set to unlock generic serialization (the highest-value use case) is:
1. `@traits(fields, T)` — enumerate field names ← **implement first**
2. `@traits(get_member, obj, "name")` — access field by name
3. `static_for K in list:` — compile-time loop unrolling

With these three, any Simple programmer can write a zero-annotation JSON serializer,
a generic equality comparator, a debug printer, an ORM mapper — all without modifying the target type.

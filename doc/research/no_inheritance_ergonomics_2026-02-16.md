# No-Inheritance Ergonomics: Forwarding Sugar, Aliases, and Composition Patterns

**Date:** 2026-02-16 (Updated: 2026-02-17)
**Status:** IMPLEMENTATION COMPLETE
**Scope:** Alias-based forwarding sugar, class header design, delegation, default methods, game engine integration
**Decision:** H5 Hybrid (header declares WHAT, body declares HOW via `alias`). No inheritance.
**Not implementing:** Extension methods (explicitly excluded from Simple), implementation inheritance
**Implementation:** All 4 phases complete, 49 tests passing (0 failures)

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Delegation / Forwarding Sugar](#2-delegation--forwarding-sugar)
3. [Default Methods in Interfaces/Traits](#3-default-methods-in-interfacestraits)
4. [Extension Methods -- NOT IMPLEMENTING](#4-extension-methods----not-implementing)
5. [Go's Promoted Methods (Embedding)](#5-gos-promoted-methods-embedding)
6. [Languages Without Implementation Inheritance](#6-languages-without-implementation-inheritance)
7. [Game Engine Integration Without Inheritance](#7-game-engine-integration-without-inheritance)
8. [Performance: Alias vs Delegation](#8-performance-alias-vs-delegation)
9. [Current Type System Inventory](#9-current-type-system-inventory)
10. [Alias-Based Forwarding Designs](#10-alias-based-forwarding-designs)
11. [Class Header Line Design -- DECIDED: H5](#11-class-header-line-design----decided-h5)
12. [Creative Approaches (Evaluated, Not Chosen)](#12-creative-approaches-evaluated-not-chosen)
13. [Implementation Plan](#13-implementation-plan)
14. [References](#14-references)

---

## 1. Executive Summary

Languages without implementation inheritance need ergonomic alternatives for code reuse. Two core mechanisms are adopted for Simple:

| Mechanism | What It Does | Key Example | Simple Status |
|-----------|-------------|-------------|---------------|
| **Delegation/forwarding sugar** | Auto-generates method forwarding to a composed field | Kotlin `by`, Go embedding | **Implementing (H5)** |
| **Default methods** | Interface/trait provides implementation that conformers inherit | Java 8 `default`, Rust trait defaults | **Future (trait system)** |
| ~~Extension methods~~ | ~~Add methods to existing types~~ | ~~C#, Kotlin~~ | **Not implementing** |

### Design Decision: H5 Hybrid

```simple
class Logger with Printable, Clickable:       # WHAT traits are satisfied
    printer: Printer
    handler: Handler
    alias Printable = printer                  # HOW: forwarded to field
    alias Clickable = handler                  # HOW: forwarded to field
    fn on_click(event: Event): ...             # HOW: implemented directly (overrides alias)
```

**Why H5:**
- Header `with Trait1, Trait2` already parses (existing mixin syntax)
- Body `alias Trait = field` reuses existing `alias` keyword consistently
- Explicit `fn` in body overrides forwarded method (no surprises)
- No extension methods needed -- forwarding + traits + mixins cover all use cases

**Why NOT extension methods:**
- Simple has `impl` blocks for adding methods to types
- Simple has traits/mixins for shared behavior
- Extension methods add static-dispatch-only methods that can't override, can't access private fields -- limited value when `impl` blocks exist
- Avoids the Swift protocol extension dispatch bug (static vs dynamic confusion)

**Codebase context:**
- 34 traits, ~1,315 classes, ~2,287 structs, ~1,204 impl blocks
- 7 classes + 26 structs use legacy `(ParentType)` syntax (compiler-internal only, NOT part of language design)
- 13+ mixin definitions with `class X with Mixin`
- **Inheritance is NOT supported** -- users should use composition + forwarding instead
- **`alias` is the unifying concept**: type alias, class alias, function alias, trait forwarding alias

---

## 2. Delegation / Forwarding Sugar

### 2.1 The Problem It Solves

When type `A` contains `b: B` and wants to "act like a B", you write boilerplate:

```simple
class Derived:
    b: Base

    fn f():
        self.b.f()
    fn g(x: i64) -> i64:
        self.b.g(x)
    # ... dozens more forwards
```

### 2.2 Language Survey

#### Kotlin: `by` keyword

```kotlin
class Derived(b: Base) : Base by b
```

Compiler generates hidden `$$delegate_0` field and forwarding methods. HotSpot JIT inlines trivial forwarding methods.

**Critical limitations:**
1. **Self-reference not forwarded:** Delegate's internal `this` goes to its own implementations, NOT to the wrapper's overrides. This is *forwarding*, not *true delegation*.
2. **Immutable delegate binding:** Hidden delegate field is set once at construction.
3. **Interface-only:** Only interface methods can be delegated.
4. **Kotlin's lead designer called this "the worst feature in Kotlin"** due to self-reference limitation.

#### Go: Struct Embedding

```go
type Container struct {
    Base        // anonymous embedding
    Name string
}
c.Describe()  // promoted from Base
```

Zero memory overhead, NOT inheritance (receiver is always the embedded type). **Critical backwards-compat problem (2024):** New methods on embedded types break outer types silently.

#### Rust: `delegate` Crate + RFC 3530

```rust
delegate! { to self.inner { pub fn push(&mut self, value: T); } }
```

RFC 3530 introduces `reuse` keyword (nightly): `reuse Trait::foo { self.inner }`.

#### D Language: `alias this`

```d
struct SafeInt { private int theInt; alias theInt this; }
```

Zero overhead, compile-time, enables implicit conversion to underlying type.

### 2.3 Design Knobs

| Knob | Options |
|------|---------|
| **Selective vs wholesale** | Forward specific methods OR all of a trait OR everything |
| **Conflict resolution** | Leftmost wins / compile error / require override |
| **Self binding** | Forwarding (self = inner) vs delegation (self = wrapper) |
| **Visibility** | Forward public only / allow narrowing |

### 2.4 Forwarding vs True Delegation

| | Forwarding | True Delegation |
|---|---|---|
| **`self` in callee** | Inner object | Outer object |
| **Override visible to inner** | No | Yes (open recursion) |
| **Encapsulation** | Strong | Weak (fragile base class) |
| **Languages** | Kotlin `by`, Go embed, Rust | Self, JavaScript prototype |

**Recommendation for Simple:** Forwarding (simpler, more predictable, stronger encapsulation).

---

## 3. Default Methods in Interfaces/Traits

### Java 8+
```java
default boolean isEmpty() { return size() == 0; }
```
Diamond resolution: class wins > most specific interface > compile error.

### Rust Traits
```rust
trait Iterator {
    fn next(&mut self) -> Option<Self::Item>; // Only required
    fn count(self) -> usize { /* 50+ default methods */ }
}
```
No diamond problem (no inheritance). Conditional defaults via trait bounds.

### Swift Protocol Extensions
```swift
extension Collection { var isEmpty: Bool { count == 0 } }
```
**Critical dispatch bug:** Methods only in extension (not protocol) use static dispatch, not dynamic.

### C++ CRTP + Concepts
Zero runtime overhead. CRTP benchmarks: 7.2x to 100x faster than virtual dispatch.

---

## 4. Extension Methods -- NOT IMPLEMENTING

> **Decision:** Simple will NOT implement extension methods. The `impl` block system, traits, and mixins already cover these use cases.

| Language | Syntax | Dispatch | Can Add State? |
|----------|--------|----------|----------------|
| C# | `static void Ext(this string s)` | Static | No |
| Kotlin | `fun String.wordCount()` | Static | No |
| Swift | `extension Int { }` | Static | Computed only |
| Scala 3 | `extension (c: Circle) def circ` | Static | No |

Extensions cannot access private fields, do not participate in dynamic dispatch.

**Why excluded for Simple:**
- `impl Type:` blocks already add methods to existing types (same capability, better integrated)
- Traits with default methods provide reusable behavior across types
- Mixins inject fields AND methods (more powerful than extensions)
- Extension methods create static/dynamic dispatch confusion (Swift's well-known bug)
- Extensions cannot override virtual methods -- limited value in a trait-based system
- Simple prefers explicit composition over implicit method injection

---

## 5. Go's Promoted Methods (Embedding)

Struct embedding promotes fields and methods. Zero memory overhead but NOT inheritance. **2024 breakage:** `image.Gray` added `SetRGBA64`, breaking all structs embedding `*image.Gray`. Recommendation: avoid embedding external types.

---

## 6. Languages Without Implementation Inheritance

| Language | Reuse Mechanism |
|----------|----------------|
| Go | Embedding + interfaces |
| Rust | Traits with defaults |
| Erlang/Elixir | Modules, processes |
| Haskell | Typeclasses, modules |
| **Simple** | **No inheritance.** Composition + aliases + traits + mixins + forwarding sugar |

---

## 7. Game Engine Integration Without Inheritance

If engine requires subclassing (Unity MonoBehaviour, Unreal AActor):
1. Generate tiny engine-facing wrapper in host language that inherits required base
2. Wrapper holds your composition-based logic object
3. Wrapper forwards lifecycle callbacks into your object

Constraints: reflection/serialization, engine-owned lifecycle, hot path forwarding cost.

---

## 8. Performance: Alias vs Delegation

| Mechanism | Cost | When |
|-----------|------|------|
| **True alias** (`fn x = y`) | Zero (same symbol at link time) | Always |
| **Delegation** (`fn x(a): y(a)`) | ~1-3ns per call | JIT inlines to zero for monomorphic sites |
| **Virtual dispatch** | ~7ns + cache effects | Tight loops, game engines, HFT |
| **Megamorphic IC** | Significant degradation | 5+ types at one call site |

**Practical conclusion:** For 99% of code, delegation = alias after JIT. The priority for `fn x = y` is **ergonomics**, not performance.

### Detailed Comparison for Simple

| Aspect | True Alias (`fn x = y`) | Delegation (`fn x(a): y(a)`) |
|--------|------------------------|------------------------------|
| Lines of code | 1 | 2-3 |
| Runtime cost | Zero | ~1-3ns (JIT-eliminable) |
| Arity transparency | Automatic (any args) | Must match signature |
| Overload support | Forwards all overloads | Each overload separately |
| Stack frame | Single | Extra frame (unless inlined) |

---

## 9. Current Type System Inventory

### 9.1 Statistics

| Type | Count |
|------|-------|
| Classes | ~1,315 |
| Structs | ~2,287 |
| Traits | 34 |
| Enums | ~1,052 |
| Impl blocks | ~1,204 |
| Legacy `(Parent)` syntax (compiler-internal only) | 7 classes, 26 structs |
| Mixin definitions | 13+ |
| `with` usage | 220+ |

### 9.2 Existing Traits

| Trait | Location | Required Methods |
|-------|----------|-----------------|
| `Error` | `src/std/error.spl` | `message() -> text`, `source() -> Error?`, `backtrace() -> Backtrace?` |
| `FutureCore<T>` | `src/std/async_core.spl` | `poll() -> Poll<T>`, `is_ready() -> bool` |
| `TaskHandleCore<T>` | `src/std/async_core.spl` | `id() -> usize`, `is_finished() -> bool`, `try_join() -> Option<T>`, `state() -> TaskState` |
| `JoinSetCore<T>` | `src/std/async_core.spl` | `len() -> usize`, `is_empty() -> bool`, `try_join_next()` |
| `SchedulerCore` | `src/std/async_core.spl` | `has_runnable() -> bool`, `run_one() -> bool`, `is_idle() -> bool` |
| `ToJson` | `src/std/json.spl` | `to_json() -> text` |
| `Displayable` | various | `to_string() -> text` |
| `Comparable` | various | `compare_to(other) -> i64` |
| `Serializable` | various | `serialize() -> text`, `deserialize(text)` |
| `HasId` | test/ | `id() -> i64` |
| `HasLabel` | test/ | `label() -> text` |
| `HasPriority` | test/ | `priority() -> i64` |

### 9.3 Legacy Inheritance Syntax (NOT supported, compiler-internal only)

> **Note:** The `(Parent)` syntax shown below is **not part of the Simple language specification**. These patterns exist only in the compiler's own source code as internal implementation details. User code should use **composition + forwarding** (via `alias Trait = field`) instead of inheritance. The `(Parent)` syntax may be removed in a future compiler refactor.

**Class inheritance (`class Child(Parent)`) -- compiler-internal only:**
- `LinkerCompilationContext(CompilationContext)` -- overrides `load_template()`, `type_registry()`, `contract_mode()`
- `CompilerCompilationContext(CompilationContext)`
- `CheckBackendImpl(Backend)`

**Struct inheritance (26 cases, all Block system) -- compiler-internal only:**
- `BuiltBlockDef(BlockDefinition)`
- `MathBlockDef(BlockDefinition)`
- `LossBlockDef(BlockDefinition)`
- `SqlBlockDef(BlockDefinition)`
- `RegexBlockDef(BlockDefinition)`
- `JsonBlockDef(BlockDefinition)` ... etc.

**Recommended alternative:** Use composition with `alias Trait = field` forwarding sugar instead.

### 9.4 Mixin Patterns

```simple
mixin Timestamp:
    created_at: i64
    updated_at: i64
    fn get_created() -> i64: self.created_at
    me touch(): self.updated_at = current_time()

class User:
    use Timestamp
    id: i64
    name: text
```

Mixins inject both fields and methods. Support generics and trait bounds.

### 9.5 Composition Patterns (Manual Delegation)

**ErrorChain delegates to Error trait:**
```simple
class ErrorChain:
    current: Error?
    fn next() -> Error?:
        val error = self.current.unwrap()
        self.current = error.source()
        Some(error)
```

**Context wraps inner error:**
```simple
class Context<E>:
    message: text
    error: E
    fn inner() -> E: self.error
```

**SmfWriter composes multiple collections:**
```simple
class SmfWriter:
    sections: [SmfSection]
    symbols: [SmfSymbol]
    relocations: [SmfRelocation]
```

### 9.6 What Interfaces Do Current Classes Implement?

| Class | Implements (via `impl` blocks) | Manual Delegation Fields |
|-------|-------------------------------|-------------------------|
| `SimpleError` | `Error` | `source_error: Error?` |
| `Context<E>` | `Error` | `error: E` |
| `LinkerCompilationContext` | legacy `(CompilationContext)` (compiler-internal) | `type_reg`, `project_di`, `project_aop` |
| `SmfWriter` | (builder pattern) | sections, symbols, relocations |
| `ErrorChain` | (iterator pattern) | `current: Error?` |
| `CancellationToken` | (state pattern) | `cancelled: bool` |

---

## 10. Alias-Based Forwarding Designs

The key insight: **Simple already has `alias` at three levels (type, class, function). Extend it to a fourth: trait forwarding.**

### 10.A Field Alias (D's `alias this` Style)

```simple
class Stack:
    inner: [i64]
    alias inner                       # all methods of inner forwarded
```

**Desugars to:**
```simple
class Stack:
    inner: [i64]
    fn push(item: i64): self.inner.push(item)
    fn pop() -> i64: self.inner.pop()
    fn len() -> i64: self.inner.len()
```

| Pros | Cons |
|------|------|
| 1 line, maximum conciseness | Implicit -- can't see which methods without knowing inner type |
| Natural extension of `alias` keyword | Name collisions are silent |
| Zero new keywords | If field type changes, all forwarded methods change invisibly |

### 10.B Trait Alias (Kotlin `by` Using `alias`)

```simple
class Logger:
    printer: Printer
    alias Printable = printer         # forward Printable trait to printer field
```

**Desugars to:**
```simple
class Logger:
    printer: Printer
    fn print_line(msg: text): self.printer.print_line(msg)
```

| Pros | Cons |
|------|------|
| Explicit about WHICH interface and WHICH field | Requires trait system maturity |
| Reuses `alias X = Y` syntax | Need to verify field implements trait |
| At a glance: what Logger satisfies and how | |

### 10.C Method Alias Batch (Explicit Per-Method)

```simple
class Wrapper:
    inner: Base
    alias fn push = inner.push
    alias fn pop = inner.pop
    alias fn len = inner.len
```

| Pros | Cons |
|------|------|
| Most explicit, no surprises | Verbose for large interfaces |
| Extends existing `fn x = y` parser structure | Must update when inner type changes |
| Lowest implementation risk | |

### 10.D Class Header Forwarding (`via`)

```simple
class Logger(Printable via printer, Clickable via handler):
    printer: Printer
    handler: Handler
```

| Pros | Cons |
|------|------|
| Header is "table of contents" | Header gets long for complex classes |
| At a glance: all capabilities | New keyword `via` (or contextual keyword) |
| | Forward reference: field declared after header |

**Alternative without `via`:**
```simple
class Logger(Printable = printer, Clickable = handler):
    printer: Printer
    handler: Handler
```

### 10.E Embed-Style (Go)

```simple
class Container:
    embed Base
    name: text
```

| Pros | Cons |
|------|------|
| Clear intent | New keyword `embed` |
| Familiar to Go developers | Not really an "alias" concept |
| | Name collision resolution implicit |

---

## 11. Class Header Line Design -- DECIDED: H5

### 11.1 What the Header Should Communicate

At a glance, a developer reading a class definition should see:
1. **What traits/interfaces** the class satisfies
2. **Which are forwarded** (and to which field)
3. **Which are implemented directly**
4. **Mixins** (if any)

### 11.2 Current Simple Header Syntax

```simple
class Logger:                                    # Basic
class Logger with Timestamp:                     # Mixin
class Logger with Timestamp, Serializable:       # Multiple mixins
```

### 11.3 Language Comparison

| Language | Header | Forwarding |
|----------|--------|------------|
| Kotlin | `class X(b: B) : I by b` | `by` in header |
| Go | `type X struct { B }` | Embedding in body |
| Rust | `impl Trait for Type` | Separate block |
| Swift | `class X: P1, P2` | In header |
| Java | `class X implements I1, I2` | In header |
| D | `alias theInt this;` | In body |
| Scala | `class X extends B with T1 with T2` | `with` keyword |

### 11.4 Proposed Header Options

#### H1: Extend `with` for forwarding

```simple
# Direct implementation (existing syntax)
class Logger with Printable:
    fn print_line(msg: text): ...

# Forwarding via field (new: with Trait = field)
class Logger with Printable = printer:
    printer: Printer
```

Minimal syntax change. `with Trait` = implement directly. `with Trait = field` = forward to field.

#### H2: Separate `implements` and `forwards`

```simple
class Logger implements Printable, Serializable forwards Clickable = handler:
    handler: Handler
    fn print_line(msg: text): ...
```

Verbose but unambiguous.

#### H3: `via` in header parentheses

```simple
class Logger(Printable, Clickable via handler):
    handler: Handler
    fn print_line(msg: text): ...     # Printable implemented directly
    # Clickable forwarded to handler
```

Bare trait name = implemented directly. `via field` = forwarded.

#### H4: Header minimal, body declares forwarding

```simple
class Logger:
    printer: Printer
    handler: Handler
    alias Printable = printer
    alias Clickable = handler
    fn extra_method(): ...
```

Header stays clean. Forwarding is body-level implementation detail.

#### H5: Hybrid -- header declares WHAT, body declares HOW (Recommended)

```simple
class Logger with Printable, Clickable:
    printer: Printer
    handler: Handler
    alias Printable = printer         # forwarded
    fn on_click(event: Event): ...    # implemented directly
```

- Header `with Printable, Clickable` declares what traits are satisfied (already parses)
- Body `alias Printable = printer` declares how (forwarding)
- Direct `fn` in body = implemented directly
- **If a `with` trait has no `alias`, compiler checks all methods are implemented directly**

### 11.5 Full Example with All Features

```simple
# Header tells you: Logger mixes in Timestamp,
# and satisfies Printable + Clickable + Serializable
class Logger with Timestamp, Printable, Clickable, Serializable:
    printer: Printer                  # field
    handler: Handler                  # field

    # HOW traits are satisfied:
    alias Printable = printer         # forwarded to printer
    alias Clickable = handler         # forwarded to handler
    fn serialize() -> text:           # implemented directly
        "Logger({self.printer})"

    # Own methods:
    fn log(msg: text):
        self.print_line("[LOG] " + msg)

    # Override a forwarded method:
    fn print_line(msg: text):         # overrides the alias
        self.printer.print_line("[LOGGER] " + msg)
```

**Reading order:**
1. Header: Logger HAS Timestamp fields, DOES Printable + Clickable + Serializable
2. Body aliases: Printable comes from printer, Clickable comes from handler
3. Direct methods: serialize() is custom, log() is own method
4. Override: print_line() overrides the forwarded version

---

## 12. Creative Approaches (Evaluated, Not Chosen)

### 12.1 Pipe `|>` for Forwarding -- NOT Recommended

```simple
alias Printable |> printer
```

`|>` means data flow in expressions. Using it for compile-time declarations is a category error.

### 12.2 Compose `>>` for Forwarding -- NOT Recommended

```simple
Printable >> printer
```

Cryptic. Composing a trait with a field does not make semantic sense.

### 12.3 Layer Connect `~>` -- Interesting but NOT Recommended

```simple
Printable ~> printer
```

The "connect with checking" metaphor fits (validate that field implements trait), but `~>` is designed for neural network layers. Same operator doing dimension checking in expressions and trait forwarding in class bodies would be confusing.

### 12.4 Annotation `@forward` -- Strong Alternative

```simple
class Logger:
    @forward(Printable)
    printer: Printer

    @forward(Clickable)
    handler: Handler
```

Clear, extensible, explicit. Annotation directly on the field. Can support options:

```simple
@forward(Printable, except: ["debug_print"])    # Forward all except some
@forward(Printable, only: ["print_line"])        # Forward only specific
@forward                                         # Forward ALL methods
```

| Pros | Cons |
|------|------|
| Very clear relationship (annotation on field) | Annotations currently informational, not code-generating |
| Extensible with options | Semantic shift for annotation system |
| No new keywords | |

### 12.5 `use` Keyword Reuse -- Possible but Risky

```simple
class Logger:
    printer: Printer
    use printer as Printable
```

"Use printer's methods as Printable implementation." But `use` already has two meanings (module import, mixin application). A third would overload it.

### 12.6 `export` Keyword Reuse -- NOT Recommended

```simple
export printer.Printable
```

The export metaphor doesn't fit delegation.

### 12.7 Walrus `:=` for Binding -- Too Cryptic

```simple
Printable := printer
```

Same as `alias Printable = printer` but without the keyword. Less readable.

### 12.8 `impl Trait via field` Block -- Rust-Inspired

```simple
class Logger:
    printer: Printer

    impl Printable via printer        # all Printable methods forwarded

    impl Serializable:                # implemented directly
        fn serialize() -> text:
            "Logger"
```

| Pros | Cons |
|------|------|
| Clear separation of forwarded vs direct | More verbose |
| Reuses existing `impl` keyword | `via` is new contextual keyword |
| Familiar to Rust developers | |

---

## 13. Implementation Plan

### Design Decision Summary

| Decision | Choice | Rationale |
|----------|--------|-----------|
| **Header design** | H5 Hybrid | Header = WHAT, body = HOW |
| **Forwarding keyword** | `alias` | Unifies type/class/fn/trait alias |
| **Self binding** | Forwarding (self = inner) | Simpler, no fragile base class |
| **Extension methods** | Not implementing | `impl` blocks + traits + mixins cover it |
| **Override rule** | Explicit `fn` wins over `alias` | No surprises |
| **Collision rule** | Compile error on ambiguity | Safe default |

### The H5 Design in Full

```simple
# HEADER: declares name, mixins, and trait contracts
class Logger with Timestamp, Printable, Clickable, Serializable:

    # FIELDS:
    printer: Printer
    handler: Handler

    # FORWARDING (alias = this trait is satisfied by this field):
    alias Printable = printer
    alias Clickable = handler

    # DIRECT IMPLEMENTATION (satisfies Serializable directly):
    fn serialize() -> text:
        "Logger({self.printer})"

    # OVERRIDE (explicit fn shadows forwarded method):
    fn print_line(msg: text):
        self.printer.print_line("[LOGGER] " + msg)

    # OWN METHODS:
    fn log(msg: text):
        self.print_line("[LOG] " + msg)
```

**Reading the header:** Logger HAS Timestamp fields, DOES Printable + Clickable + Serializable.
**Reading the body:** Printable comes from printer, Clickable comes from handler, Serializable is custom, print_line overrides the forwarded version.

### DEPRECATED: Function Alias (`fn x = y`) via Desugar Pipeline

**Status:** COMPLETE (deprecated - prefer explicit delegation)
**Goal:** Make `fn println = print` work at module level via text-level desugar.

**Implementation:** Handled in `src/app/desugar/forwarding.spl` (not core parser).
The desugar scans source for the target function's signature using `fn_scanner.spl`,
then generates: `fn name(params): target(params)`.

**Files:**
- `src/app/desugar/fn_scanner.spl` -- Scans module-level fn definitions for signatures
- `src/app/desugar/forwarding.spl` -- Generates delegation from `fn name = target`

**Syntax (deprecated):**
```simple
fn println = print              # DEPRECATED: generates fn println(msg): print(msg)
# Preferred: fn println(msg: text): print(msg)
```

**Tests:** `test/feature/function_alias_spec.spl` -- 10/10 passing
- Basic alias works, chain alias, void alias, original preserved

### Phase 2: Method Alias Batch (`alias fn/me x = field.method`) in Class Body

**Status:** COMPLETE
**Goal:** Allow explicit per-method forwarding inside class bodies.

**Implementation:** `src/app/desugar/forwarding.spl` -- text-level desugar pass.

**Syntax:**
```simple
class Stack:
    inner: [i64]
    alias fn len = inner.len          # -> fn len(): self.inner.len()
    alias fn push(item) = inner.push  # -> fn push(item): self.inner.push(item)
    alias me clear = inner.clear      # -> me clear(): self.inner.clear()
```

**Tests:** `test/feature/method_alias_spec.spl` -- 7/7 passing
**Unit tests:** `test/unit/app/desugar/forwarding_spec.spl` Phase 2 section -- 4/4 passing

### Phase 3: Trait Alias Forwarding (`alias Trait = field`) in Class Body

**Status:** COMPLETE
**Goal:** Forward an entire trait's methods to a field with one line.

**Implementation:**
- `src/app/desugar/trait_scanner.spl` -- Scans source for `trait Name:` blocks, extracts method signatures
- `src/app/desugar/forwarding.spl` -- When `alias TraitName = field` found, generates forwarding for each abstract method

**Syntax:**
```simple
trait Printable:
    fn print_line(msg: text)
    fn debug_print(msg: text)

class Logger:
    printer: Printer
    alias Printable = printer       # forwards all Printable methods to printer
```

**Key behavior:**
- Default methods (with body) are skipped -- only abstract methods get forwarding
- Multiple `alias Trait = field` lines supported on same class
- Unknown traits silently generate nothing

**Tests:**
- `test/feature/trait_forwarding_spec.spl` -- 8/8 passing (runtime delegation)
- `test/unit/app/desugar/trait_scanner_spec.spl` -- 9/9 passing (scanner)
- `test/unit/app/desugar/forwarding_spec.spl` Phase 3 section -- 5/5 passing (desugar)

### Phase 4: Blanket Field Alias (`alias field`)

**Status:** COMPLETE
**Goal:** Forward ALL public methods of a field's type.

**Implementation:**
- `src/app/desugar/type_scanner.spl` -- Scans source for class/struct definitions, extracts fields and methods
- `src/app/desugar/forwarding.spl` -- When `alias field_name` found, looks up field type, generates forwarding for all methods

**Syntax:**
```simple
class Storage:
    fn size() -> i64: ...
    me clear(): ...

class Wrapper:
    store: Storage
    alias store                     # forwards size() and clear() to self.store
```

**Key behavior:**
- Resolves field type from class field declarations in same source file
- Forwards ALL methods of the field's type (no filtering)
- Unknown types silently generate nothing

**Tests:** `test/unit/app/desugar/forwarding_spec.spl` Phase 4 section -- 3/3 passing

### Collision & Override Rules (All Phases)

```
Priority (highest to lowest):
1. Explicit `fn` / `me` defined in class body
2. `alias fn x = field.method`  (specific method alias)
3. `alias Trait = field`  (trait-scoped forwarding)
4. `alias field`  (blanket forwarding)
5. Mixin methods from `with Mixin`
```

If two items at the same priority level provide the same method name -> **compile error** requiring explicit resolution.

### What Simple Does NOT Need (and Why)

| Feature | Why Not |
|---------|---------|
| **Extension methods** | `impl` blocks already add methods to types. Traits provide shared behavior. No static/dynamic dispatch confusion. |
| **Implementation inheritance** (`(Parent)`) | Composition + forwarding is the design direction. Avoids fragile base class, diamond problem. Use `alias Trait = field` for code reuse. |
| **True delegation** (self = wrapper) | Forwarding is simpler. Avoids fragile base class. Use composition + `alias Trait = field` for code reuse. |
| **`embed` keyword** (Go-style) | `alias field` covers this with explicit opt-in. Avoids Go's backwards-compat trap. |
| **Operator-based forwarding** (`|>`, `>>`, `~>`) | Overloads runtime operators for compile-time semantics. Confusing. |

### File Change Summary (ACTUAL)

| Phase | Files | Change | Status |
|-------|-------|--------|--------|
| Dep. | `src/app/desugar/fn_scanner.spl` | Module-level fn signature scanner | COMPLETE |
| Dep. | `src/app/desugar/forwarding.spl` | `fn name = target` delegation gen | COMPLETE |
| 2 | `src/app/desugar/forwarding.spl` | `alias fn/me` delegation gen | COMPLETE |
| 3 | `src/app/desugar/trait_scanner.spl` | Trait definition scanner | COMPLETE |
| 3 | `src/app/desugar/forwarding.spl` | `alias Trait = field` generation | COMPLETE |
| 4 | `src/app/desugar/type_scanner.spl` | Class/struct definition scanner | COMPLETE |
| 4 | `src/app/desugar/forwarding.spl` | `alias field` blanket generation | COMPLETE |

### Test Results (ACTUAL)

| Phase | Test File | Tests | Status |
|-------|-----------|-------|--------|
| Dep. | `test/feature/function_alias_spec.spl` | 10 | 10/10 PASS |
| 2 | `test/feature/method_alias_spec.spl` | 7 | 7/7 PASS |
| 3 | `test/feature/trait_forwarding_spec.spl` | 8 | 8/8 PASS |
| 3 | `test/unit/app/desugar/trait_scanner_spec.spl` | 9 | 9/9 PASS |
| All | `test/unit/app/desugar/forwarding_spec.spl` | 15 | 15/15 PASS |
| **Total** | | **49** | **49/49 PASS** |

---

## 14. References

### Delegation / Forwarding
- [Kotlin Delegation Documentation](https://kotlinlang.org/docs/delegation.html)
- [Kotlin `by` Internals](https://medium.com/@AlexanderObregon/what-happens-when-you-use-kotlins-by-keyword-for-delegation-01e16335499a)
- [Effective Class Delegation (Kotlin)](https://zsmb.co/effective-class-delegation/)
- [Go Embedding Backwards Compatibility (2024)](https://nigeltao.github.io/blog/2024/go-embedding-back-compat.html)
- [Embedding in Go](https://eli.thegreenplace.net/2020/embedding-in-go-part-1-structs-in-structs/)
- [Rust RFC 3530 `fn_delegation`](https://github.com/rust-lang/rust/issues/118212)
- [Rust `delegate` Crate](https://docs.rs/delegate)
- [D `alias this`](https://tour.dlang.org/tour/en/gems/subtyping)
- [Forwarding vs Delegation](https://en.wikipedia.org/wiki/Delegation_(object-oriented_programming))

### Performance
- [GCC Function Alias Attribute](https://gcc.gnu.org/onlinedocs/gcc/Common-Function-Attributes.html)
- [HotSpot JVM Optimizations](https://jdriven.com/blog/2019/11/HotSpot-JVM-optimizations)
- [V8 Inline Caching](https://braineanear.medium.com/the-v8-engine-series-iii-inline-caching-unlocking-javascript-performance-51cf09a64cc3)
- [Virtual Function Cost in C++](https://johnnysswlab.com/the-true-price-of-virtual-functions-in-c/)
- [CRTP vs Dynamic Dispatch](https://eli.thegreenplace.net/2013/12/05/the-cost-of-dynamic-virtual-calls-vs-static-crtp-dispatch-in-c)

### Default Methods / Traits
- [Java Diamond Problem Resolution](https://javanexus.com/blog/solving-java-diamond-problem-delegation)
- [Rust Trait Default Methods](https://effective-rust.com/default-impl.html)
- [Swift Protocol Extensions](https://www.swiftanytime.com/blog/protocol-extensions-in-swift)
- [C++ CRTP + Concepts](https://joelfilho.com/blog/2021/emulating_crtp_with_cpp_concepts/)

### Extension Methods (researched, not implementing)
- [Kotlin Extensions](https://kotlinlang.org/docs/extensions.html)
- [Scala 3 Extensions](https://docs.scala-lang.org/scala3/reference/contextual/extension-methods.html)

### Simple Language (Implementation References)
- `doc/guide/syntax_quick_reference.md` -- Current alias/type syntax
- `doc/report/alias_feature_investigation_2026-02-16.md` -- Function alias investigation
- `src/app/desugar/static_methods.spl` -- Existing desugaring infrastructure (model for forwarding desugar)
- `src/app/parser/def/function.spl:310-328` -- Existing `FunctionAliasDef` parser structure
- `src/compiler_core/traits.spl` -- Trait definitions and solver
- `src/compiler_core/parser.spl` -- Core parser (Phase 1-4 changes)
- `src/compiler_core/ast_types.spl` -- AST node definitions (Phase 1 addition)
- `src/compiler_core/interpreter/eval.spl` -- Evaluator (Phase 1 alias resolution)

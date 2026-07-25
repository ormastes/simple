# Design – Explicit Allocation (`new` Keyword)

**Date:** 2026-02-28
**Status:** Draft
**Related:** [baremetal_robustness_rules.md](baremetal_robustness_rules.md), [resource_lifecycle_manager_design.md](resource_lifecycle_manager_design.md)
**Research:** Cross-language survey of Zig, Rust, Ada/SPARK, Odin, D, Swift, Nim allocation models

---

## 1. Motivation

In embedded and safety-critical systems, **every heap allocation must be visible and intentional**. Hidden allocations cause:

- Unpredictable latency (malloc may block, fragment, or fail)
- Unbounded memory growth (OOM kills in production)
- Unauditable resource usage (cannot prove memory bounds at review time)

Zig addresses this by requiring an `Allocator` parameter on every allocating function — but this is **convention only**, not compiler-enforced. A Zig library can still hide allocations via direct syscalls or stored allocators.

Simple can do better: **compiler-enforced allocation visibility** through the `new` keyword, treating allocation as a tracked **effect**.

### Design Goals

| Goal | Description |
|------|-------------|
| **G1** | Every allocation is visible at the call site |
| **G2** | The compiler enforces this — not convention, not lint |
| **G3** | Normal mode remains ergonomic (no `new` required) |
| **G4** | Robust mode is strict (missing `new` = compile error) |
| **G5** | Works for constructors AND regular function calls |
| **G6** | Integrates with existing `Allocator` trait, `GcMode`, `#[no_gc]` |

---

## 2. Core Concept: Allocation as an Effect

Allocation is an **effect** — like mutability or IO. Functions that allocate are marked (explicitly or by inference), and the `new` keyword at the call site **acknowledges** the effect.

```
┌─────────────────────────────────────────────────────────────────┐
│                    Allocation Effect System                      │
│                                                                 │
│  Function declaration        Call site (robust mode)            │
│  ─────────────────────       ──────────────────────────         │
│  #[alloc]                    new func(args)        ← required  │
│  fn parse(input: text):      new(arena) func(args) ← required  │
│      ...allocates...         func(args)            ← ERROR     │
│                                                                 │
│  fn len(s: text) -> i64:     len(s)                ← OK        │
│      ...no allocation...     new len(s)            ← WARNING   │
└─────────────────────────────────────────────────────────────────┘
```

This is **stronger than Zig** (compiler-enforced, not convention), **more ergonomic than Zig** (no allocator threading through every parameter list), and **opt-in** (normal mode works like today).

---

## 3. The `new` Keyword

### 3.1 Three Forms

| Form | Meaning | Allocator Used |
|------|---------|---------------|
| `new expr` | Allocate with default allocator | System allocator (or module-level default) |
| `new() expr` | Allocate from type's registered pool | Pre-registered pool for the type |
| `new(alloc) expr` | Allocate with explicit allocator | The provided allocator instance |

### 3.2 Applies to ALL Allocating Expressions

`new` is not limited to constructors. It marks **any expression that allocates**:

```simple
# --- Constructors ---
val p = new Point(x: 3, y: 4)
val list = new List<Int>()
val node = new(arena) Node(value: 42, next: nil)

# --- Function calls that allocate ---
val parsed = new parse(input)
val copy = new(arena) deep_clone(original)
val text = new format("hello {name}")

# --- Collection operations that allocate ---
val doubled = new items.map(\x: x * 2)
val merged = new(arena) concat(list_a, list_b)

# --- Non-allocating calls: no `new` ---
val length = items.len()
val sum = add(a, b)
val found = items.contains(42)
```

### 3.3 Behavior by Mode

| Mode | `new` on allocating call | `new` on non-allocating call | Allocating call without `new` |
|------|-------------------------|------------------------------|-------------------------------|
| **Normal** (default) | Optional, accepted | Ignored (no-op) | OK — uses GC or default allocator |
| **Robust** (`#[robust]`) | Required | Warning (unnecessary `new`) | **Compile error** |

---

## 4. The `#[alloc]` Effect

### 4.1 Marking Functions

Functions that allocate heap memory carry the `#[alloc]` effect. This can be:

**Explicit — declared by the author:**

```simple
#[alloc]
fn parse(input: text) -> Ast:
    val tokens = new tokenize(input)     # allocates internally
    val tree = new build_tree(tokens)
    tree
```

**Inferred — detected by the compiler:**

The compiler propagates the `#[alloc]` effect upward through the call graph:

```
tokenize()       — calls allocator.allocate() → #[alloc]
build_tree()     — calls new tokenize()       → #[alloc]
parse()          — calls new build_tree()     → #[alloc]
```

A function is `#[alloc]` if its body contains:
- Direct allocator calls (`allocator.allocate()`, `allocator.create()`)
- Constructor calls that produce heap-allocated objects
- Calls to other `#[alloc]` functions (transitively)

**Opt-out — for functions that manage allocation internally:**

```simple
#[no_alloc]
fn with_temp_buffer(size: i64, block: fn([u8])):
    # Uses stack-based FixedBufferAllocator internally
    # Caller does not need `new` — no heap escapes
    var buf: [u8; 4096] = zeroed()
    var fba = FixedBufferAllocator(buffer: buf)
    val temp = fba.allocate(size, align: 8) ?? panic("too large")
    block(temp)
    # fba goes out of scope, stack reclaimed automatically
```

`#[no_alloc]` asserts: "this function may use allocators internally, but no heap allocation escapes to the caller." The compiler verifies this by checking that no allocated memory is returned or stored in caller-visible state.

### 4.2 Effect Propagation Rules

```
┌──────────────────────────────────────────────────────────────────┐
│                   #[alloc] Propagation                           │
│                                                                  │
│  Rule 1: Direct allocation → function is #[alloc]               │
│    fn foo():                                                     │
│        allocator.allocate(...)   ← direct call → foo is #[alloc]│
│                                                                  │
│  Rule 2: Calling #[alloc] function → caller is #[alloc]         │
│    fn bar():                                                     │
│        new foo()                 ← calls #[alloc] → bar #[alloc]│
│                                                                  │
│  Rule 3: #[no_alloc] breaks the chain                           │
│    #[no_alloc]                                                   │
│    fn baz():                                                     │
│        new foo()                 ← internal only → baz NOT alloc │
│        # nothing escapes                                         │
│                                                                  │
│  Rule 4: Pure value-type constructors are NOT #[alloc]           │
│    val p = Point(x: 3, y: 4)    ← stack only → NOT #[alloc]    │
│                                                                  │
│  Rule 5: Constructors with heap fields ARE #[alloc]              │
│    val n = Node(value: 1, children: [])  ← [] allocs → #[alloc]│
└──────────────────────────────────────────────────────────────────┘
```

### 4.3 What Counts as Allocation

| Expression | Allocates? | Reason |
|------------|-----------|--------|
| `Point(x: 3, y: 4)` | No | Pure value type, stack-only |
| `Node(value: 1, children: [])` | Yes | `[]` is a heap-allocated dynamic array |
| `List<Int>()` | Yes | Collection with internal heap buffer |
| `[1, 2, 3]` | Yes | Array literal creates heap array |
| `"hello " + name` | Yes | String concatenation allocates |
| `items.map(\x: x * 2)` | Yes | Creates new collection |
| `items.len()` | No | Read-only accessor |
| `items.contains(x)` | No | Read-only scan |
| `items.push(x)` | Maybe | May reallocate if at capacity |

For "maybe" cases (like `push`), the function is marked `#[alloc]` conservatively. In robust mode, `new items.push(x)` is required.

---

## 5. Robust Mode

### 5.1 Activation

```simple
# Per-file attribute
#[robust]

# Per-module (__init__.spl)
#[robust]
module motor_controller

# Project-wide (simple.sdn)
robust: true

# Compiler flag
bin/simple build --robust
bin/simple build --robust src/embedded/
```

### 5.2 What Robust Mode Enforces

| Rule | Description | Error |
|------|-------------|-------|
| **A1** | `new` required on all `#[alloc]` calls | `error[A1]: allocating call without 'new'` |
| **A2** | `new` on non-allocating call warns | `warning[A2]: unnecessary 'new' on non-allocating call` |
| **A3** | Implicit GC disabled (acts like `#[no_gc]`) | `error[A3]: GC not available in robust mode` |
| **A4** | Unbounded collections forbidden | `error[A4]: use FixedArray<T, N> or provide allocator` |

### 5.3 Error Messages

```
error[A1]: allocating call requires 'new' in robust mode
  --> src/embedded/controller.spl:42
   | val tokens = tokenize(input)
   |              ^^^^^^^^^ this function allocates (#[alloc])
   = help: use 'new tokenize(input)' for default allocator
   = help: use 'new(arena) tokenize(input)' for explicit allocator

error[A1]: constructor allocates in robust mode
  --> src/embedded/controller.spl:45
   | val list = List<Int>()
   |            ^^^^^^^^^^^ List<Int> allocates heap memory
   = help: use 'new List<Int>()' or 'new(pool) List<Int>()'
   = help: use FixedArray<Int, 64> for stack-based fixed collection

warning[A2]: unnecessary 'new' on non-allocating expression
  --> src/embedded/controller.spl:48
   | val len = new items.len()
   |           ^^^ items.len() does not allocate
   = help: remove 'new'
```

---

## 6. Allocator Selection

### 6.1 `new expr` — Default Allocator

The default allocator is determined by the context:

| Context | Default Allocator |
|---------|------------------|
| Normal mode, GC | GC-managed (automatic) |
| Normal mode, `#[no_gc]` | System allocator (`malloc`/`free`) |
| Robust mode | Module's `#[allocator]` attribute, or system allocator |
| `with_allocator` block | Block's allocator |

```simple
#[robust]
#[allocator(system)]              # module default = system allocator
module my_module

val p = new Point(x: 3, y: 4)    # uses system allocator
```

### 6.2 `new() expr` — Type Pool

`new()` uses a pre-registered pool for the type. Pools are declared at the module level:

```simple
#[pool(capacity: 256)]
struct Particle:
    x: f64
    y: f64
    vx: f64
    vy: f64

# Usage
val p = new() Particle(x: 0.0, y: 0.0, vx: 1.0, vy: 0.0)

# Pool is auto-created at module init with capacity 256
# Allocation is O(1), no fragmentation, fixed memory footprint
```

For functions (not constructors), `new()` uses the return type's pool:

```simple
#[alloc]
fn create_particle(x: f64, y: f64) -> Particle:
    Particle(x: x, y: y, vx: 0.0, vy: 0.0)

val p = new() create_particle(1.0, 2.0)  # allocates from Particle pool
```

**Pool exhaustion** returns `nil` (wrapped in Option) or panics, depending on configuration:

```simple
#[pool(capacity: 256, on_full: nil)]       # returns nil when full
#[pool(capacity: 256, on_full: panic)]     # panics when full (default)
#[pool(capacity: 256, on_full: grow)]      # grows pool (not available in robust)
```

### 6.3 `new(alloc) expr` — Explicit Allocator

Pass any value that implements the `Allocator` trait:

```simple
val arena = ArenaAllocator.create(capacity: 64 * 1024)
defer arena.destroy()

val tokens = new(arena) tokenize(input)
val tree = new(arena) build_tree(tokens)
val result = new(arena) evaluate(tree)

# arena.destroy() frees everything at once
```

### 6.4 `with_allocator` Block — Scoped Default

Override the default allocator for a scope:

```simple
val arena = ArenaAllocator.create(capacity: 64 * 1024)
defer arena.destroy()

with_allocator(arena):
    val tokens = new tokenize(input)       # uses arena
    val tree = new build_tree(tokens)      # uses arena
    val result = new evaluate(tree)        # uses arena
```

In robust mode, `new` is still required inside `with_allocator` — the block only changes WHICH allocator `new` uses, not whether `new` is needed.

---

## 7. Value Types vs Reference Types

Not all construction allocates. Pure value types live on the stack:

```simple
# Value type — all fields are value types, no indirection
struct Point:
    x: i64
    y: i64

val p = Point(x: 3, y: 4)        # stack allocated, even in robust mode — no `new` needed

# Reference type — has heap-allocated fields
struct Node:
    value: i64
    children: List<Node>          # List is heap-allocated

val n = new Node(value: 1, children: new List<Node>())   # `new` required in robust mode
```

### Classification Rules

| Type | Stack (no `new`) | Heap (`new` required in robust) |
|------|-------------------|-------------------------------|
| Struct with only value-type fields | Yes | — |
| Struct with heap fields (List, Map, text, etc.) | — | Yes |
| Class (always reference) | — | Yes |
| Enum (no indirection) | Yes | — |
| Enum with heap payload | — | Yes |
| Fixed-size array `[T; N]` | Yes | — |
| Dynamic array `[T]` | — | Yes |
| Closure (captures heap state) | — | Yes |

The compiler determines this from the type definition. A struct is stack-only if all its fields are recursively stack-only.

---

## 8. Interaction with Existing Systems

### 8.1 GC Mode (`gc_config.spl`)

| GC Mode | Robust Mode | `new` behavior |
|---------|-------------|----------------|
| `Gc` (default) | Off | `new` optional, GC manages memory |
| `Gc` | On | **Error**: GC not available in robust mode |
| `NoGc` | Off | `new` optional, manual management |
| `NoGc` | On | `new` required on all allocating calls |

Robust mode implies `#[no_gc]`. The combination `Gc + robust` is a compile error.

### 8.2 Existing Allocator Trait (`src/lib/nogc_sync_mut/allocator.spl`)

The existing `Allocator` trait remains the backend. `new(alloc)` dispatches through the trait:

```simple
trait Allocator:
    fn allocate(size: usize, align: usize) -> [u8]?
    fn deallocate(ptr: [u8], size: usize, align: usize)
    fn reallocate(ptr: [u8], old_size: usize, new_size: usize, align: usize) -> [u8]?
```

`new(alloc) Point(x: 3, y: 4)` desugars to:

```simple
# Compiler-generated equivalent:
val __mem = alloc.allocate(size: size_of<Point>(), align: align_of<Point>()) ?? panic("OOM")
val __ptr = cast<Point>(__mem)
__ptr.x = 3
__ptr.y = 4
__ptr
```

### 8.3 Baremetal Allocators (`src/lib/nogc_async_mut_noalloc/baremetal/allocator.spl`)

All existing baremetal allocators (`BumpAllocator`, `FreeListAllocator`, `FixedBlockAllocator`, `MultiPoolAllocator`) implement `Allocator` and work with `new(alloc)`:

```simple
#[robust]
module motor_controller

val heap = BumpAllocator(base: 0x2000_0000, size: 128 * 1024)

val config = new(heap) MotorConfig(speed: 100, direction: Forward)
val buffer = new(heap) FixedArray<u8, 256>()
```

### 8.4 Baremetal Robustness Rules (`baremetal_robustness_rules.md`)

This design adds rule **R7** to the existing robustness rules:

| ID | Rule | Rationale |
|----|------|-----------|
| R7 | Explicit allocation (`new` required) | No hidden heap allocation |

R7 complements R4 (Init/Reset lifecycle): `@init` functions use `new` to set up pools and arenas; `@main` functions use `new()` or `new(alloc)` to allocate from pre-initialized pools.

### 8.5 `#[alloc]` and `@safe` Profile

```simple
#[robust]  # enables A1-A4 (allocation rules)
#[safe]    # enables R1-R6 (baremetal rules) + A1-A4

# @safe implies @robust — all allocation rules active
```

---

## 9. Deallocation

`new` controls allocation. Deallocation depends on the allocator:

| Allocator | Deallocation Method |
|-----------|-------------------|
| GC (normal mode) | Automatic |
| System (`new expr`) | `free(ptr)` or `defer free(ptr)` |
| Pool (`new() expr`) | `pool.release(ptr)` or automatic on pool reset |
| Arena (`new(arena) expr`) | `arena.destroy()` frees all at once |
| Explicit (`new(alloc) expr`) | `alloc.deallocate(ptr, ...)` |

In robust mode, the compiler warns on allocated values that have no corresponding deallocation path (leak detection, similar to Zig's `DebugAllocator`):

```
warning[A5]: allocated value 'tokens' may leak
  --> src/embedded/controller.spl:42
   | val tokens = new tokenize(input)
   |     ^^^^^^ allocated here, no deallocation found
   = help: use 'defer free(tokens)' or allocate from an arena
```

---

## 10. Cross-Language Comparison

| Property | Simple (this design) | Zig | Rust | Ada | Odin |
|----------|---------------------|-----|------|-----|------|
| **Allocation visible at call site** | Yes (`new` keyword) | Yes (allocator param) | No (implicit global) | Yes (`new` + pool) | No (implicit context) |
| **Compiler-enforced** | Yes (robust mode) | No (convention) | No | Yes (`Default_Storage_Pool(null)`) | Partial (`#+vet`) |
| **Transitive tracking** | Yes (`#[alloc]` propagation) | No (manual threading) | No | No | No |
| **Non-allocating guaranteed** | Yes (no `#[alloc]` = proof) | Yes (no allocator param) | No | No | No |
| **Custom allocator at call site** | Yes (`new(alloc)`) | Yes (param) | Nightly only | Yes (per-type pool) | Yes (context override) |
| **Ergonomic in normal mode** | Yes (no `new` needed) | No (always explicit) | Yes | No (always explicit) | Yes |
| **Pool shorthand** | Yes (`new()`) | No | No | No | No |
| **Stack vs heap distinction** | Yes (value types skip `new`) | Yes (stack is default) | Yes (default stack) | No | Yes |

Simple's design is **unique** in combining compiler enforcement with ergonomic opt-in. Zig requires allocator threading everywhere; Simple only requires `new` at the call site. Ada binds allocators to types; Simple binds them to call sites. Odin's context is implicit; Simple's `new` is explicit.

---

## 11. Syntax Grammar

```
# New expressions (additions to parser)
new_expr        = 'new' alloc_spec? call_expr
alloc_spec      = '(' ')'                    # type pool
                | '(' expression ')'          # explicit allocator

# Examples parsed:
# new Point(x: 3)           → NewExpr(alloc=Default, expr=Call(Point, {x:3}))
# new() Point(x: 3)         → NewExpr(alloc=Pool,    expr=Call(Point, {x:3}))
# new(arena) Point(x: 3)    → NewExpr(alloc=Expr(arena), expr=Call(Point, {x:3}))
# new parse(input)           → NewExpr(alloc=Default, expr=Call(parse, {input}))
# new(a) items.map(fn)       → NewExpr(alloc=Expr(a), expr=MethodCall(items,map,{fn}))
```

### AST Node

```simple
# New AST expression type
val EXPR_NEW = 47

fn expr_new(alloc_kind: i64, alloc_expr: i64, inner_expr: i64, span_id: i64) -> i64:
    # alloc_kind: 0 = default, 1 = pool, 2 = explicit
    # alloc_expr: expression id for explicit allocator (0 if default/pool)
    # inner_expr: the call expression being allocated
    ...
```

### Token

```simple
val TOK_KW_NEW = 209    # 'new' keyword
```

---

## 12. Implementation Plan

| Phase | Work | Effort | Depends On |
|-------|------|--------|------------|
| **1** | Add `new` keyword to lexer/parser, `EXPR_NEW` AST node | Medium | — |
| **2** | `#[alloc]` attribute: manual annotation + basic checking | Low | Phase 1 |
| **3** | `#[alloc]` inference: call graph analysis, transitive propagation | High | Phase 2 |
| **4** | Robust mode: `#[robust]` attribute + A1-A4 error checking | Medium | Phase 3 |
| **5** | `new()` pool support: `#[pool]` attribute, auto pool creation | Medium | Phase 1 |
| **6** | `new(alloc)` codegen: dispatch through `Allocator` trait | Medium | Phase 1 |
| **7** | `with_allocator` block: scoped allocator override | Low | Phase 6 |
| **8** | Leak detection warnings (A5) | High | Phase 3 |
| **9** | Integration with `@safe` profile | Low | Phase 4 |

### Phase 1 Implementation Sketch

```simple
# src/compiler/10.frontend/core/lexer.spl — add token
val TOK_KW_NEW = 209

# src/compiler/10.frontend/core/parser.spl — parse new expression
fn parse_new_expr() -> i64:
    expect(TOK_KW_NEW)

    var alloc_kind = 0    # default
    var alloc_expr = 0

    # Check for allocator spec: new() or new(expr)
    if peek() == TOK_LPAREN:
        consume()
        if peek() == TOK_RPAREN:
            consume()
            alloc_kind = 1    # pool
        else:
            alloc_expr = parse_expression()
            expect(TOK_RPAREN)
            alloc_kind = 2    # explicit

    val inner = parse_call_expr()
    expr_new(alloc_kind, alloc_expr, inner, current_span())
```

---

## 13. Examples

### 13.1 Normal Mode (Backward Compatible)

```simple
# No changes needed — existing code works as-is
val p = Point(x: 3, y: 4)
val list = List<Int>()
val parsed = parse(input)

# `new` is accepted but optional
val p2 = new Point(x: 5, y: 6)
val parsed2 = new(arena) parse(input)
```

### 13.2 Robust Mode — Embedded Controller

```simple
#[robust]
module motor_controller

use std.baremetal.{BumpAllocator, FixedBlockAllocator}

# Allocators set up at module init
val heap = BumpAllocator(base: 0x2000_0000, size: 64 * 1024)
val cmd_pool = FixedBlockAllocator(base: 0x2001_0000, block_size: 64, count: 128)

#[pool(capacity: 128)]
struct MotorCommand:
    motor_id: u8
    speed: i16
    direction: u8

@init
fn setup():
    new(heap) configure_pwm(frequency: 20000)
    new(heap) init_sensors()

@main
fn run():
    # Stack-allocated value type — no `new` needed
    val reading = SensorReading(temp: 0, pressure: 0)

    # Pool-allocated command — O(1), no fragmentation
    val cmd = new() MotorCommand(motor_id: 1, speed: 500, direction: 1)
    defer cmd_pool.release(cmd)

    # Explicit allocator
    val buffer = new(heap) read_sensor_data(sensor_id: 3)
    defer heap.deallocate(buffer)

    process(cmd, buffer)    # process() is NOT #[alloc] — no `new` needed
```

### 13.3 Robust Mode — Game Frame Allocator

```simple
#[robust]
module renderer

use std.allocator.{ArenaAllocator}

fn render_frame(scene: Scene):
    val frame_arena = ArenaAllocator.create(capacity: 1024 * 1024)
    defer frame_arena.destroy()    # free everything at frame end

    with_allocator(frame_arena):
        val meshes = new collect_visible(scene)
        val sorted = new depth_sort(meshes)
        val batches = new batch_draw_calls(sorted)
        draw(batches)              # draw() does not allocate

    # frame_arena.destroy() frees all meshes, sorted, batches at once
```

### 13.4 Mixed: Library Code (Normal) + Application (Robust)

```simple
# --- src/lib/parser.spl (normal mode, library) ---
#[alloc]                               # author marks as allocating
fn parse(input: text) -> Ast:
    val tokens = tokenize(input)       # no `new` needed in normal mode
    val tree = build_tree(tokens)
    tree

# --- src/embedded/app.spl (robust mode, application) ---
#[robust]
module embedded_app

use std.parser.{parse}

fn handle_command(input: text):
    val ast = new(cmd_arena) parse(input)    # `new` required — parse is #[alloc]
    execute(ast)                              # execute is NOT #[alloc]
```

---

## 14. Open Questions

| Question | Options | Leaning |
|----------|---------|---------|
| Should `#[alloc]` be inferred by default or require explicit annotation? | Inferred (like Zig's convention) vs explicit-only | Inferred with opt-out `#[no_alloc]` |
| Should `new` on method calls use `new obj.method()` or `obj.new method()`? | Prefix vs infix | Prefix: `new obj.method()` |
| Should `new()` pool be per-type or per-instance? | `#[pool]` on type vs `pool_for<T>(n)` | Per-type via `#[pool]` attribute |
| Should robust mode allow `new` with GC mode? | Allow (GC as explicit allocator) vs forbid | Forbid — robust implies `#[no_gc]` |
| Should `with_allocator` be a block or a `using` declaration? | `with_allocator(a): ...` vs `using a as allocator` | Block form |
| How to handle generic functions where allocating depends on type parameter? | Conditional `#[alloc]` vs always `#[alloc]` | Conservative: always `#[alloc]` if any instantiation allocates |

---

## 15. References

- **Zig allocator model**: No hidden allocations in stdlib. Convention-based, allocator passed as parameter. [zig.guide/allocators](https://zig.guide/standard-library/allocators/)
- **Ada `Default_Storage_Pool(null)`**: Compile-time enforcement — uncontrolled allocation is a compile error. [AdaCore guidelines](https://learn.adacore.com/courses/Guidelines_for_Safe_and_Secure_Ada_SPARK/)
- **Odin `#+vet explicit-allocators`**: Per-file compiler check for implicit allocator use. [Odin overview](https://odin-lang.org/docs/overview/)
- **D composable allocators**: Building-block allocator design (Segregator, FreeList, Region). [std.experimental.allocator](https://dlang.org/phobos/std_experimental_allocator.html)
- **Rust `heapless`**: Fixed-capacity no-alloc data structures. [docs.rs/heapless](https://docs.rs/heapless/)
- **Swift Embedded two-tier**: Allocating vs non-allocating compilation modes. [swift-evolution/embedded-swift.md](https://github.com/swiftlang/swift-evolution/blob/main/visions/embedded-swift.md)
- **C++ PMR**: Runtime-polymorphic allocators with `monotonic_buffer_resource`. [cppreference.com](https://en.cppreference.com/w/cpp/memory/monotonic_buffer_resource.html)
- **TigerBeetle (Zig CSDI pattern)**: Call-site dependency injection for allocators. [matklad.github.io](https://matklad.github.io/2023/03/26/zig-and-rust.html)
- **Simple baremetal rules**: [baremetal_robustness_rules.md](baremetal_robustness_rules.md)
- **Simple allocator trait**: `src/lib/nogc_sync_mut/allocator.spl`
- **Simple baremetal allocators**: `src/lib/nogc_async_mut_noalloc/baremetal/allocator.spl`
- **Simple GC config**: `src/compiler/00.common/gc_config.spl`

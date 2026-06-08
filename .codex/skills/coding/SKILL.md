---
name: coding
description: "Simple language coding rules for Codex. Key syntax, generics, pattern binding, constructors, runtime limitations, reserved keywords. Reference: doc/07_guide/quick_reference/syntax_quick_reference.md."
---

# Coding — Simple Language Rules for Codex

**Cooperative Phase:** All phases (always active when writing code)
**Self-sufficient.** Reference rules for any code-writing task.

## Reference

Full syntax: `doc/07_guide/quick_reference/syntax_quick_reference.md`

## Core Syntax

### Variables

```simple
val name = "Alice"             # Immutable (preferred)
# name := "Alice"              # Walrus shorthand is not currently proven; use val
var count = 0                  # Mutable
```

### Strings

```simple
print "Hello, {name}!"        # String interpolation (default)
print r"raw: \d+"              # Raw string (no interpolation)
```

### Logging and Print

- Use `print` only for scripts, examples, tests, and intentionally human-facing CLI output.
- In `src/app/`, `src/lib/`, and `src/compiler/`, prefer structured logging calls: `log`, `info`, `warn`, `error`, `debug`, or `trace`.
- `debug`/`trace` are for diagnostic detail and must be safe to compile out or suppress in production paths.
- Hardware access, external process/file/network access, and trace capture should log through the AOP/debug logging path when available so human and LLM log modes can fold/group it.
- `simple lint` emits `LOG001` when production source uses bare `print`; script-style `print` remains allowed outside production source roots.

### Functions

```simple
fn square(x):
    x * x                      # Implicit return

fn add(a: i64, b: i64) -> i64:
    a + b
```

### Generics

**Use `<>` not `[]`:**
```simple
Option<T>
List<Int>
Map<String, Int>
Result<T, E>
```

### Classes (NO INHERITANCE)

```simple
class Point:
    x: i64
    y: i64
    fn get_x() -> i64: self.x          # Immutable method
    me move(dx: i64):                   # Mutable method ('me' keyword)
        self.x = self.x + dx
    static fn origin() -> Point:        # Static method
        Point(x: 0, y: 0)
```

**`class Child(Parent)` is NOT supported.** Use:
- Composition
- Alias forwarding
- Traits
- Mixins

### Constructors

```simple
Point(x: 3, y: 4)             # Named fields — NOT .new()
```

### Pattern Binding

```simple
if val x = optional_value:     # NOT 'if let'
    process(x)
```

### Error Handling

```simple
# Use Result<T, E> + ? operator (no try/catch/throw)
fn read_file(path: text) -> Result<text, Error>:
    val content = fs.read(path)?
    Ok(content)
```

### Match

```simple
match value:
    Some(x): process(x)
    nil: ()                    # Unit value
```

### Lambdas

```simple
items.map(\x: x * 2)          # Lambda
items.map(_ * 2)               # Placeholder lambda
items.map(_1 * 10)             # Numbered placeholder
words.map(&:len)               # Method reference
```

### Short Grammar Use

Use compact grammar when it removes local boilerplate without hiding control flow:

```simple
fn double(x: i64) -> i64: x * 2              # Expression-bodied function
items.map(_ * 2)                              # Single-argument transform
items.zip(other).map(_1 + _2)                 # Short tuple/zip transform
words.map(&:len)                              # Method reference
[for x in items if x > 0: x * x]              # Comprehension
value ?? fallback                             # Nil coalescing
```

Prefer explicit forms when the expression has side effects, more than one decision point,
or needs clear runtime support in native mode:

```simple
items.map(\x:
    val scaled = x * factor
    scaled + offset
)
```

- Do not use `:=` in new code until parser/runtime tests prove the actual token works; use `val`.
- Treat `|>` pipe-forward dispatch as interpreter-supported unless native tests pass with `SIMPLE_NO_STUB_FALLBACK=1`.
- For native-targeted code, prefer expression-bodied functions, comprehensions, and direct calls over pipe chains.

### Comprehensions

```simple
[for x in 0..10 if x % 2 == 0: x]
```

### Optional Chaining

```simple
user?.name ?? "Anonymous"      # Optional chaining + nil coalescing
```

### Operators

```simple
x |> transform                 # Pipe
f >> g                         # Compose
layer1 ~> layer2               # Layer connect
2 ** 10                        # Power
m{ x^2 + y^2 }                # Math block
```

### Pass Variants

```simple
pass_todo("what remains", "hint or issue")
pass_do_nothing("why no-op is correct")
pass_dn("why no-op is correct")
todo("what remains", "hint or issue")
case _("why catch-all is correct"):
pass                           # Generic no-op
```

### Type Aliases

```simple
type Point2D = Point           # Type alias
alias Optional = Option        # Class alias
```

## Runtime Limitations (CRITICAL)

| Issue | Workaround |
|-------|-----------|
| Multi-line booleans | Wrap in parentheses: `if (a and\n   b):` |
| Nested closure capture | Can READ outer vars, CANNOT MODIFY (module closures work fine) |
| Chained methods broken | Use intermediate `var` |
| `?` in names | Not allowed — `?` is operator only; use `.?` over `is_*` predicates |
| `:=` walrus shorthand | Use `val name = expr` until real `:=` parser/runtime tests pass |
| Native pipe-forward dispatch | Use direct calls or run native tests with `SIMPLE_NO_STUB_FALLBACK=1` |

## Concurrency API Map

When investigating Simple concurrency, search the API names as well as runtime
terms like fiber or scheduler. The implemented stdlib surfaces are split by
execution model:

| API | Path | Model |
|-----|------|-------|
| `thread_spawn` / `ThreadHandle` | `src/lib/nogc_async_mut/concurrent/thread.spl` and `thread_sffi.spl` | OS thread (`pthread_create` / `CreateThread`) |
| `cooperative_green_spawn` / `cooperative_green_spawn_value` / `GreenThreadHandle` / `cooperative_green_run_one` / `cooperative_green_run_all` | `src/lib/nogc_async_mut/concurrent/cooperative_green.spl` over `green_thread.spl` | Cooperative green-thread queue on the current OS thread; no preemption or CPU parallelism |
| `green_channel_new` / `green_channel_recv` / `green_channel_send` | `src/lib/nogc_async_mut/concurrent/green_channel.spl` | Pure Simple nonblocking green-channel contract; recv parks a logical green task, send unparks a waiter or reports bounded backpressure |
| `multicore_green_spawn` / `multicore_green_set_parallelism` / `multicore_green_parallelism` / `MulticoreGreenHandle.used_runtime_pool()` / `MulticoreGreenHandle.ran_inline_fallback()` | `src/lib/nogc_async_mut/concurrent/multicore_green.spl` | Pure Simple bounded-worker facade over `rt_pool_*`; current M:N benchmark candidate with a hosted Go `GOMAXPROCS`-like pool limit, not final scheduler-aware green runtime |
| `task_spawn` / `TaskHandle` | `src/lib/nogc_async_mut/thread_pool.spl` | Lower-level pool-backed native task path when `rt_pool_*` is available; interpreter fallback otherwise; not the named cross-language M:N profile row |
| `channel_new` / `channel_from_id` | `src/lib/nogc_sync_mut/concurrent/channel.spl` re-exported through `std.concurrent.channel` | Runtime MPMC channel |

Use `cooperative_green_spawn` for lightweight cooperative scheduling tests, and
`cooperative_green_spawn_value` when a direct-run benchmark needs to exercise
the queue without function-value calls. Do not use either for Go-style M:N
CPU-parallel benchmarks. Use `multicore_green_spawn` for current cross-language
Go-like benchmark work, use `task_spawn` only for direct task API checks, or use
a future scheduler-aware green runtime when that lands. When a test or profile
claims M:N CPU parallelism, assert `used_runtime_pool()` so interpreter or
platform fallback does not masquerade as a parallel result.
Call `multicore_green_set_parallelism(workers)` before the first
`multicore_green_spawn` when a profile needs an explicit hosted pool limit, and
record `multicore_green_parallelism()` in evidence. Cross-language profile
evidence must also show Go `GOMAXPROCS` pinned to the same `CPU_WORKERS` value.
Live pools can grow but do not claim shrink/preemption behavior yet.

Do not use numeric-suffix concurrency aliases. They are rejected by
`simple check` with `E-PAR-002`; use `thread_spawn_with_args`,
`spawn_isolated_with_args`, or `spawn_limited_with_args` for
explicit-argument spawning.
Keep concurrency surfaces separate. Importing `thread_spawn` from
`std.concurrent.cooperative_green`, importing `cooperative_green_spawn` from
`std.concurrent.thread`, or similar wrong-surface imports is rejected with
`E-PAR-003`. Passing non-closures to `thread_spawn`, `green_spawn`,
`cooperative_green_spawn`, or `multicore_green_spawn`, or passing text to
`multicore_green_set_parallelism`, is rejected with `E-PAR-004`.

## Reserved Keywords

These CANNOT be used as identifiers:

`gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`

## File Organization

- All code in `.spl` files
- Shell scripts in `.shs` files (only for container entrypoints)
- Config/data in SDN format (not JSON/YAML)
- No Python, no Bash scripts (except 3 bootstrap scripts in `scripts/`)
- Files > 800 lines must be split

## Import Conventions

```simple
use std.io                     # Standard library (preferred)
use lib.common.text            # Also works (std -> lib internally)
```

`use std.X` and `use lib.X` both resolve from `src/lib/`. Prefer `use std.X` in new code.

## TODO Rules

- NEVER convert TODO/FIXME to NOTE — that hides work
- Either implement the TODO or delete the code entirely
- If a TODO cannot be implemented yet, leave it as TODO

## Code Quality

- NEVER over-engineer — only make requested changes
- NEVER add unused code — delete completely
- STUB001 = hard fail — no `pass_todo` in production code

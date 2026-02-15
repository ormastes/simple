# Baremetal Robustness Rules for Simple Language

**Date**: 2026-02-15
**Status**: Design
**Scope**: Compile-time enforced rules for safety-critical and resource-constrained targets
**Targets**: Baremetal, CUDA kernels, VHDL/HLS, MISRA-like safety profiles

---

## Motivation

Safety-critical and resource-constrained environments (embedded, GPU kernels, hardware description) require **statically provable** properties:

- Bounded stack usage (no unbounded recursion)
- Bounded execution time (no infinite loops)
- Predictable control flow (no hidden jumps)
- Deterministic initialization (resources ready before use)
- No invisible error paths (no exceptions)

These rules are enforced **at compile time** via the `@safe` module attribute or `--profile=safe` compiler flag.

---

## Rule Summary

| ID | Rule | Rationale |
|----|------|-----------|
| R1 | No recursion (direct or mutual) | Bounded stack |
| R2 | Circular call detection (compile-time) | Catch accidental mutual recursion |
| R3 | No try/catch/throw | Already language policy (see `no_exceptions_design_decision.md`) |
| R4 | Init/reset lifecycle enforcement | Resources initialized before main |
| R5 | All loops must be bounded | Provable termination |
| R6 | No goto-like control flow (no break, no continue) | Predictable single-exit loops |

---

## R1: No Recursion

### Rule

**No function may call itself, directly or indirectly.**

This includes:
- Direct recursion: `fn foo(): foo()`
- Tail recursion: `fn foo(n): if n == 0: return 0; foo(n - 1)` — also banned
- Mutual recursion: `fn a(): b()` + `fn b(): a()` — caught by R2

### Rationale

- Stack depth must be statically computable
- Tail call optimization is not guaranteed across all backends (C codegen, native x86, RISC-V, CUDA PTX)
- MISRA-C Rule 17.2, DO-178C, SPARK Ada — all ban recursion

### Enforcement

Compile-time call graph analysis. Every function call edge is recorded. If any cycle exists in the call graph, emit error:

```
error[R1]: recursion detected in function 'factorial'
  --> src/math.spl:12
   | fn factorial(n: i64) -> i64:
   |     if n <= 1: return 1
   |     n * factorial(n - 1)
   |         ^^^^^^^^^ recursive call
   = help: use iterative loop with bounded iteration count
```

### Alternatives

```simple
# BANNED: recursive factorial
fn factorial(n: i64) -> i64:
    if n <= 1: return 1
    n * factorial(n - 1)

# ALLOWED: iterative with bounded loop
fn factorial(n: i64) -> i64:
    var result = 1
    for i in 1..n+1:
        result = result * i
    result
```

---

## R2: Circular Function Call Detection

### Rule

**Compile-time detection of all call cycles in the module call graph.**

Build a directed graph where nodes are functions and edges are call-sites. Report all strongly connected components (SCCs) with size > 1 (mutual recursion) and self-loops (direct recursion).

### Enforcement

Uses Tarjan's SCC algorithm on the call graph.

```
error[R2]: circular call chain detected
  --> src/state.spl
   | fn parse_expr() calls parse_term()     at line 45
   | fn parse_term() calls parse_factor()   at line 78
   | fn parse_factor() calls parse_expr()   at line 102
   |
   = note: cycle: parse_expr -> parse_term -> parse_factor -> parse_expr
   = help: break cycle with iterative state machine or explicit stack
```

### Severity

| Profile | Behavior |
|---------|----------|
| `@safe` | **Error** — compilation fails |
| `@warn` | **Warning** — reports cycles but compiles |
| Default | **Off** — no analysis |

### Workaround Pattern: Explicit Stack

```simple
# BANNED: mutually recursive descent parser
fn parse_expr(): ... parse_term() ...
fn parse_term(): ... parse_factor() ...
fn parse_factor(): ... parse_expr() ...

# ALLOWED: iterative with explicit stack
enum ParseAction:
    ParseExpr
    ParseTerm
    ParseFactor

fn parse(tokens: [Token]) -> Ast:
    var stack = [ParseAction.ParseExpr]
    for step in 0..MAX_PARSE_DEPTH:
        if stack.len() == 0: return result
        val action = stack.pop()
        match action:
            ParseExpr: ...
            ParseTerm: ...
            ParseFactor: ...
    result
```

---

## R3: No try/catch/throw

### Rule

**Already a language-level decision.** Simple does not support exceptions.

See: `doc/design/no_exceptions_design_decision.md`

### Error Handling

```simple
# Use Result pattern
fn divide(a: i64, b: i64) -> (i64, text?):
    if b == 0: return (0, "division by zero")
    (a / b, nil)

# Use Option pattern
fn find(items: [Item], id: i64) -> Item?:
    for item in items:
        if item.id == id: return item
    nil
```

### Baremetal Note

In `@safe` modules, `Result`/`Option` must be checked — unchecked error values are compile errors (see existing ignored return value warnings in `src/core/interpreter/eval.spl`).

---

## R4: Init/Reset Lifecycle

### Rule

**Three execution phases with strict resource access rules:**

```
Phase 1: INIT    — runs before main, sets up resources
Phase 2: MAIN    — runs application logic, uses pre-initialized resources
Phase 3: RESET   — teardown/restart, may share code with INIT
```

### Constraints

| Phase | Can allocate | Can access pools | Can call init fns | Can call main fns |
|-------|-------------|-----------------|-------------------|-------------------|
| INIT  | Yes | No (not ready) | Yes | No |
| MAIN  | No (use pools) | Yes | No | Yes |
| RESET | Yes | Yes (for cleanup) | Yes | No |

### Declaration

```simple
@safe
module motor_controller

# Phase annotations
@init
fn setup_hardware():
    configure_gpio()
    init_pwm(frequency: 20000)
    init_pool(motor_commands, size: 32)

@init
fn init_pool(pool: Pool, size: i64):
    pool.allocate(size)

@reset
fn emergency_stop():
    disable_all_motors()
    setup_hardware()       # OK: reset can call init functions

@main
fn run():
    val cmd = motor_commands.acquire()  # OK: pool initialized in init
    cmd.speed = read_sensor()
    motor_commands.release(cmd)

# COMPILE ERROR examples:
@main
fn bad_main():
    init_pool(extra, size: 64)    # Error[R4]: main cannot call @init function
    val p = allocate(1024)        # Error[R4]: main cannot allocate directly

@init
fn bad_init():
    motor_commands.acquire()      # Error[R4]: init cannot access pool (not ready)
    run()                         # Error[R4]: init cannot call @main function
```

### Init/Reset Sharing

`@init` and `@reset` may call the same helper functions. The compiler verifies that shared helpers only use operations valid in both phases:

```simple
# Shared between init and reset
@init @reset
fn configure_gpio():
    gpio_set_mode(PIN_A, OUTPUT)
    gpio_set_mode(PIN_B, INPUT)

@init
fn setup_hardware():
    configure_gpio()        # OK

@reset
fn restart():
    configure_gpio()        # OK — same function, both phases allowed
```

### Execution Order

The compiler/linker guarantees:
1. All `@init` functions run before any `@main` function
2. `@init` functions run in declaration order within a module
3. Cross-module init order follows dependency order (imported modules init first)
4. `@reset` can be triggered by interrupt handlers or explicit call

---

## R5: All Loops Must Be Bounded

### Rule

**Every loop must have a statically determinable upper bound.**

| Loop Type | Requirement |
|-----------|-------------|
| `for i in 0..N` | N must be compile-time constant or annotated bound |
| `for item in collection` | Collection size must be bounded |
| `while condition` | Must have `@bound(N)` annotation |
| `loop` | Banned in `@safe` modules |

### Enforcement

```simple
@safe
module controller

val MAX_RETRIES = 10
val BUFFER_SIZE = 256

# OK: range with constant bound
for i in 0..BUFFER_SIZE:
    buffer[i] = 0

# OK: bounded collection
val sensors: [Sensor; 8] = get_sensors()
for sensor in sensors:
    sensor.read()

# OK: while with explicit bound annotation
@bound(MAX_RETRIES)
while not connected:
    attempt_connect()

# OK: for-range with variable, but annotated
fn process(data: [u8], len: i64):
    @bound(4096)
    for i in 0..len:
        handle(data[i])

# COMPILE ERRORS:
while true:              # Error[R5]: unbounded loop in @safe module
    do_work()

loop:                    # Error[R5]: 'loop' not allowed in @safe module
    process()

for i in 0..len:         # Error[R5]: 'len' has no proven bound
    handle(i)            #   help: add @bound(N) annotation
```

### CUDA/VHDL Compatibility

GPU kernels and hardware synthesis require bounded loops for:
- **CUDA**: Warp scheduling, register allocation, unrolling
- **VHDL/HLS**: Synthesis tool must know iteration count for pipeline scheduling

```simple
@safe @target(cuda)
fn vector_add(a: [f32; 1024], b: [f32; 1024], out: [f32; 1024]):
    for i in 0..1024:        # Synthesizable: constant bound
        out[i] = a[i] + b[i]

@safe @target(vhdl)
fn fir_filter(input: [f32; 16], coeffs: [f32; 16]) -> f32:
    var sum = 0.0
    for i in 0..16:          # Synthesizable: unrollable
        sum = sum + input[i] * coeffs[i]
    sum
```

### Bound Verification

The compiler checks `@bound(N)` annotations against actual loop behavior:
- If the loop can be proven to terminate within N iterations: OK
- If not provable: warning (may add runtime check in debug builds)
- Runtime check inserts: `if iterations > N: panic("bound exceeded")`

---

## R6: No goto-like Control Flow

### Rule

**No `break`, `continue`, or `goto` in `@safe` modules.**

Every loop has exactly one entry and one exit (the termination condition). This ensures:
- Single-entry, single-exit (SESE) control flow
- All loop iterations are predictable
- Control flow analysis is trivial

### Enforcement

```simple
@safe
module sensor_reader

# BANNED:
fn bad_search(items: [Item], target: i64) -> Item?:
    for item in items:
        if item.id == target:
            break              # Error[R6]: 'break' not allowed in @safe module
    item

fn bad_filter(items: [Item]) -> [Item]:
    var result: [Item] = []
    for item in items:
        if item.invalid:
            continue           # Error[R6]: 'continue' not allowed in @safe module
        result = result + [item]
    result

# ALLOWED: use conditional logic instead
fn search(items: [Item], target: i64) -> Item?:
    var found: Item? = nil
    for item in items:
        if item.id == target and found.? == false:
            found = item
    found

fn filter(items: [Item]) -> [Item]:
    var result: [Item] = []
    for item in items:
        if not item.invalid:
            result = result + [item]
    result
```

### Early Return

`return` is allowed — it exits the function, not a loop. Functions have clear single-exit semantics when `return` is used at the top level of a branch:

```simple
@safe
fn classify(value: i64) -> text:
    if value < 0: return "negative"
    if value == 0: return "zero"
    "positive"
```

---

## Activation

### Per-Module

```simple
@safe
module my_safe_module

# All R1-R6 rules enforced in this module
```

### Per-File (Compiler Flag)

```bash
# Check all files
bin/simple build --profile=safe

# Check specific directory
bin/simple build --profile=safe src/baremetal/
```

### Configuration (simple.build.sdn)

```sdn
profile safe:
    rules: [R1, R2, R3, R4, R5, R6]
    targets: [baremetal, cuda, vhdl]

profile warn:
    rules: [R1, R2, R5]
    severity: warning
```

### Selective Relaxation

For specific functions that need an exception (with justification):

```simple
@safe
module parser

# This function is proven safe by manual review
@allow(R1, reason: "bounded by token count, reviewed 2026-02-15")
fn parse_expr(tokens: [Token], depth: i64) -> Expr:
    if depth > MAX_DEPTH: return error_expr()
    # ... recursive descent with depth limit
```

---

## Relationship to Existing Systems

| Existing Feature | Relationship |
|-----------------|--------------|
| No exceptions (`no_exceptions_design_decision.md`) | R3 already enforced language-wide |
| Closure capture warnings (`closure_analysis.spl`) | Same pattern — static analysis at compile time |
| Ignored return warnings (`eval.spl`) | R3 strengthens this — unchecked Results are errors in `@safe` |
| Cycle detector (`cycle_detector.spl`) | R2 generalizes this from templates to all function calls |
| Assert system (`baremetal_features_examples.md`) | Complementary — asserts verify values, rules verify structure |
| Embedded immutable defaults (`embedded_immutable_defaults.md`) | Complementary — `@safe` modules default to immutable |

---

## Implementation Priority

| Phase | Rules | Effort | Value |
|-------|-------|--------|-------|
| 1 | R1, R2 (call graph analysis) | Medium | High — catches recursion bugs |
| 2 | R5, R6 (loop analysis) | Medium | High — provable termination |
| 3 | R4 (lifecycle phases) | High | High — init safety |
| 4 | Integration + `@allow` relaxation | Low | Polish |

### Phase 1 Implementation Sketch

```simple
# src/core/call_graph.spl

class CallGraph:
    nodes: [text]           # function names
    edges: [(i64, i64)]     # (caller_idx, callee_idx)

    fn add_function(name: text):
        self.nodes = self.nodes + [name]

    fn add_call(caller: text, callee: text):
        val from = self.index_of(caller)
        val to = self.index_of(callee)
        self.edges = self.edges + [(from, to)]

    fn find_cycles() -> [[text]]:
        # Tarjan's SCC algorithm
        # Returns list of cycles (each cycle = list of function names)
        ...

    fn has_self_recursion() -> [(text, i64)]:
        # Direct self-calls: (function_name, line_number)
        ...
```

---

## References

- MISRA-C:2012, Rule 17.2 (no recursion)
- DO-178C, Section 6.3.4 (bounded loops, no dynamic memory in flight)
- SPARK Ada, restriction `No_Recursion`
- CUDA Programming Guide, Section B.24 (loop bounds for unrolling)
- AUTOSAR C++14, Rule A7-5-2 (no recursion in safety-critical)

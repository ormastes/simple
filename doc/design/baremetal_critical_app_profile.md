# Baremetal & Critical Application Safety Profile

**Date**: 2026-02-15
**Status**: Design Proposal
**Extends**: `doc/design/baremetal_robustness_rules.md` (R1-R6)
**Scope**: Compile-time + runtime enforced rules for safety-critical applications
**Targets**: Baremetal, CUDA, VHDL/HLS, automotive (AUTOSAR), avionics (DO-178C), industrial control

---

## Overview

This document extends the existing R1-R6 robustness rules with **R7-R14** covering:

| ID | Rule | Origin |
|----|------|--------|
| R1-R6 | (See `baremetal_robustness_rules.md`) | Existing |
| **R7** | No memory allocation after init | NASA/JPL, MISRA, Ada/SPARK |
| **R8** | Application value limits (range types) | Ada, Pascal, Nim |
| **R9** | No ignored return values | Rust `#[must_use]`, C++ `[[nodiscard]]` |
| **R10** | Lifecycle phase functions (init/reset) | AUTOSAR, CMSIS, Zig |
| **R11** | Dynamic dispatch cycle warnings | MISRA, SPARK |
| **R12** | Stack usage analysis | DO-178C, MISRA, JPL |
| **R13** | Implicit allocation detection | Zig, Rust `#[no_std]`, SPARK |
| **R14** | Implicit numeric narrowing errors | MISRA, Ada, AUTOSAR |

### Profile Activation

```simple
# Module-level: full safety profile
@profile(critical)
module motor_controller

# Or individual rule groups
@profile(baremetal)     # R1-R6 + R7 + R12 (robustness + no-alloc + stack)
@profile(critical)      # All R1-R14 (full safety-critical)
@profile(industrial)    # R1-R6 + R7-R9 + R13-R14 (industrial control)
```

### Profile SDN Configuration

```sdn
# simple.build.sdn
profile critical:
    rules: [R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14]
    severity: error
    targets: [baremetal, cuda, vhdl]

profile baremetal:
    rules: [R1, R2, R3, R4, R5, R6, R7, R12]
    severity: error

profile industrial:
    rules: [R1, R2, R3, R4, R5, R6, R7, R8, R9, R13, R14]
    severity: error

profile warn_all:
    rules: [R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14]
    severity: warning
```

---

## Cross-Language Research Summary

### Init/Reset Naming Conventions

| System | Init | Reset/Deinit | Main/Run | Notes |
|--------|------|-------------|----------|-------|
| **AUTOSAR** | `Init()`, `*_Init()` | `DeInit()` | `MainFunction()` | Standardized per SWC |
| **CMSIS (ARM)** | `SystemInit()` | `SystemReset()` | `main()` | Called before main |
| **POSIX** | `_init` / `__attribute__((constructor))` | `_fini` / `__attribute__((destructor))` | `main()` | ELF lifecycle |
| **FreeRTOS** | `vApplicationInit()` | `vApplicationReset()` | `vTaskStartScheduler()` | RTOS startup |
| **Ada/SPARK** | `Initialize` / `Elaborate` | `Finalize` | `Main` procedure | Package elaboration |
| **Zig** | `init()` / `create()` | `deinit()` / `destroy()` | `main()` | Convention, not keyword |
| **Rust embedded** | `#[entry] fn main()` | N/A (RAII) | `fn main()` | `cortex-m-rt` crate |
| **NASA/JPL C** | `*_init()` | `*_shutdown()` / `*_reset()` | `main()` | Per-subsystem |
| **IEC 61131-3** (PLC) | `FB_init` | `FB_exit` | Cyclic `FB_body` | Function block lifecycle |

### Key Safety Standards Summary

| Standard | No Recursion | Bounded Loops | No Dynamic Alloc | No Ignored Return | Range Types |
|----------|-------------|---------------|------------------|-------------------|-------------|
| **MISRA C:2012** | Rule 17.2 | Rule 15.4 | Rule 21.3 | Rule 17.7 | Manual |
| **MISRA C++:2023** | Rule 8.2.4 | Rule 9.5.2 | Rule 21.6.1 | Rule 0.1.2 | Manual |
| **AUTOSAR C++14** | A7-5-2 | M6-5-6 | A18-5-1 | A0-1-2 | Manual |
| **Ada/SPARK** | `No_Recursion` | Provable | `No_Allocators` | Mode checking | **Native** |
| **DO-178C** | MC/DC required | Required | DAL A-C | Required | Required |
| **NASA/JPL** | Rule 1 | Rule 2 | Rule 3 | Rule 7 | Manual |

---

## R7: No Memory Allocation After Init

### Rule

**After the init phase completes, no heap or dynamic allocation is permitted. Only pre-sized pool operations are allowed.**

### Rationale

- **MISRA C Rule 21.3**: Bans `malloc`/`free` entirely
- **Ada/SPARK**: `pragma Restrictions(No_Allocators)` after elaboration
- **NASA/JPL Rule 3**: "No dynamic memory allocation after initialization"
- **DO-178C DAL A**: No dynamic allocation in flight-critical code

### Grammar: `@no_alloc` Annotation

```simple
# ---- Function-level: compiler verifies no allocation paths ----

@no_alloc
fn process_reading(raw: i64) -> i64:
    raw * 3300 / 4096           # OK: pure arithmetic

@no_alloc
fn bad_process(raw: i64) -> text:
    "value: {raw}"              # ERROR[R7]: string interpolation allocates
                                #   help: use pre-allocated BoundedString

# ---- Module-level: all functions in module are @no_alloc ----

@no_alloc
module sensor_driver

fn read_adc(channel: i64) -> i64:
    # compiler verifies no allocation in entire module
    extern fn rt_adc_read(ch: i64) -> i64
    rt_adc_read(channel)

# ---- Type-level: container tagged as allocation-free ----

@no_alloc
class SensorData:
    raw: i64
    timestamp: i64
    channel: i64
    # All fields are fixed-size primitives — no hidden allocation
```

### Grammar: Bounded Containers (Fixed-Capacity)

Inspired by Rust `heapless::Vec<T, N>`, C++ `etl::vector<T, N>`, Ada bounded containers.

```simple
# ---- Fixed-size array (stack-allocated, compile-time size) ----
val buffer: [u8; 256]              # 256-byte fixed array
val sensors: [SensorData; 8]       # 8 sensor structs, on stack

# ---- Bounded vector (fixed max capacity, variable length) ----
val readings: BoundedVec<i64, 64>  # max 64 elements, stack-allocated

@no_alloc
fn collect_samples() -> BoundedVec<i64, 64>:
    var samples: BoundedVec<i64, 64> = BoundedVec()
    for i in 0..8:
        val v = read_adc(i)
        samples.push(v)            # Returns Option — may be full
    samples

# ---- Bounded string (fixed max bytes) ----
val name: BoundedString<32>        # max 32 bytes, no heap
val msg: BoundedString<128> = BoundedString("OK")

# ---- Bounded map (fixed capacity) ----
val lookup: BoundedMap<i64, text, 16>  # max 16 entries
```

### Grammar: Pool-Based Allocation

```simple
# ---- Pool declaration (init phase only) ----
@init
fn setup():
    pool commands: Pool<MotorCommand, 32>  # 32-slot pool, pre-allocated
    pool buffers: Pool<[u8; 512], 4>       # 4 x 512-byte buffer pool

# ---- Pool usage (main phase) ----
@main
fn process():
    val cmd = commands.acquire()     # Returns Option<MotorCommand>
    if cmd.?:
        cmd.speed = read_sensor()
        execute(cmd)
        commands.release(cmd)

# ---- Pool as type parameter ----
fn process_with(pool: Pool<Command, 32>):
    val item = pool.acquire() ?? return    # Early return if pool empty
    # ... use item ...
    pool.release(item)
```

### Allocation Classification

The compiler classifies operations as allocating or non-allocating:

| Operation | Allocates? | `@no_alloc` Behavior |
|-----------|-----------|---------------------|
| `val x = 42` | No | OK |
| `val s = "literal"` | No (static) | OK |
| `"hello {name}"` | **Yes** (string concat) | **ERROR** |
| `a + b` (text) | **Yes** (string concat) | **ERROR** |
| `[1, 2, 3]` | **Yes** (dynamic array) | **ERROR** |
| `[u8; 256]` | No (fixed array) | OK |
| `BoundedVec<T, N>()` | No (stack) | OK |
| `pool.acquire()` | No (pre-allocated) | OK |
| `var x: [i64] = []` then `x.push(1)` | **Yes** (growth) | **ERROR** |
| `BoundedVec.push()` | No (bounded) | OK |

### Enforcement

```
error[R7]: allocation in @no_alloc context
  --> src/driver.spl:15
   | fn format_error(code: i64) -> text:
   |     "error: {code}"
   |     ^^^^^^^^^^^^^^^ string interpolation allocates
   = help: use BoundedString<64> or pre-allocated error table
   = note: @no_alloc forbids heap allocation (MISRA-C Rule 21.3)
```

---

## R8: Application Value Limits (Range Types)

### Rule

**All user-defined types based on primitive types should define application limits. Out-of-range values are compile-time errors (for literals) or runtime-checked (for dynamic values).**

### Rationale

- **Ada**: First-class `type Voltage is range 0..3300` — the gold standard
- **Pascal/Nim**: Subrange types with compile-time checking
- **MISRA**: Requires documented value ranges for all variables
- **DO-178C**: Range analysis required for DAL A certification
- **IEC 61508**: SIL 3-4 requires value range monitoring

### Grammar: Range Types

```simple
# ---- Basic range type (constrains a primitive) ----
type Voltage = i64 range 0..3300           # millivolts, 0-3.3V
type Temperature = i64 range -40..125      # Celsius, industrial range
type PWM_Duty = i64 range 0..100           # percentage
type SensorID = i64 range 1..16            # 16 sensors max
type Pressure = f64 range 0.0..1000.0      # kPa

# ---- Usage: compile-time checked for literals ----
val v: Voltage = 1500                      # OK
val v: Voltage = 5000                      # ERROR[R8]: 5000 not in 0..3300

# ---- Runtime checked for dynamic values ----
val raw = read_adc()
val v: Voltage = Voltage(raw)              # inserts runtime range check
                                           # panics/returns error if out of bounds

# ---- Safe conversion with Option ----
val maybe_v: Voltage? = Voltage.try_from(raw)   # nil if out of range
if maybe_v.?:
    process(maybe_v)
```

### Grammar: Range Type Operations

```simple
type Voltage = i64 range 0..3300

# ---- Range attributes ----
Voltage.min            # 0
Voltage.max            # 3300
Voltage.range          # 0..3300

# ---- Arithmetic produces widened ranges ----
val a: Voltage = 2000
val b: Voltage = 1500
val sum = a + b        # type inferred as i64 range 0..6600
val avg = (a + b) / 2  # type inferred as i64 range 0..3300

# ---- Subrange (narrowing) ----
type SafeVoltage = Voltage range 100..3300   # exclude "too low"
val sv: SafeVoltage = SafeVoltage(v)         # runtime check: v >= 100

# ---- Overflow behavior (explicit per type) ----
type Angle = i64 range 0..359 wrap          # wraps: 360 -> 0
type Counter = i64 range 0..65535 saturate  # saturates: 70000 -> 65535
type Critical = i64 range 0..100 trap       # traps: panic on overflow (default)
```

### Grammar: Domain Types (Structured Value Limits)

```simple
# ---- Complex domain constraints ----
type ConnectionCount = i64 range 1..1024
type BufferSize = i64 range 64..65536
type Timeout_ms = i64 range 0..30000        # max 30 seconds
type Retry = i64 range 0..10

# ---- Enum-like constrained ----
type Weekday = i64 range 1..7
type Month = i64 range 1..12

# ---- Hardware register fields ----
type RegAddr = u32 range 0x4000_0000..0x5FFF_FFFF  # peripheral region
type BitField = u8 range 0..7                       # 3-bit field
type Priority = u8 range 0..15                       # 4-bit NVIC priority
```

### Grammar: Struct Field Limits

```simple
# ---- Apply limits to struct fields ----
class MotorCommand:
    speed: i64 range -1000..1000     # RPM, bidirectional
    direction: i64 range 0..1        # 0=forward, 1=reverse
    duty: PWM_Duty                   # reuse named range type
    timeout: Timeout_ms

# ---- Construction checks ranges ----
val cmd = MotorCommand(
    speed: 500,        # OK
    direction: 0,      # OK
    duty: 75,          # OK: PWM_Duty range 0..100
    timeout: 5000      # OK: Timeout_ms range 0..30000
)

val bad = MotorCommand(
    speed: 2000,       # ERROR[R8]: 2000 not in -1000..1000
    direction: 2,      # ERROR[R8]: 2 not in 0..1
    duty: 150,         # ERROR[R8]: 150 not in 0..100 (PWM_Duty)
    timeout: 60000     # ERROR[R8]: 60000 not in 0..30000 (Timeout_ms)
)
```

### Enforcement

```
error[R8]: value 5000 out of range for type 'Voltage'
  --> src/sensor.spl:12
   | val reading: Voltage = 5000
   |                        ^^^^ value 5000 exceeds maximum 3300
   = note: Voltage = i64 range 0..3300
   = help: check sensor calibration or use Voltage.try_from(value)
```

```
warning[R8]: runtime range check inserted for dynamic value
  --> src/sensor.spl:18
   | val reading: Voltage = Voltage(raw_adc)
   |                        ^^^^^^^^^^^^^^^^ runtime check: 0 <= value <= 3300
   = note: will panic if value is out of range
   = help: use Voltage.try_from() for safe conversion
```

---

## R9: No Ignored Return Values

### Rule

**Functions annotated with `@must_use`, and all functions returning `Result` or `Option` in `@profile(critical)` modules, must have their return values handled.**

### Rationale

- **Rust**: `#[must_use]` on `Result` — compiler warns if discarded
- **C++17**: `[[nodiscard]]` attribute
- **MISRA C Rule 17.7**: "The value returned by a function having non-void return type shall be used"
- **Ada**: Mode checking ensures OUT parameters are consumed

### Grammar: `@must_use` Annotation

```simple
# ---- On individual functions ----
@must_use("push may fail if buffer is full")
fn push(item: T) -> Option<T>:
    pass_todo

# ---- On types (all functions returning this type require use) ----
@must_use("error must be handled")
union Result<T, E>:
    Ok(T)
    Err(E)

@must_use("option must be checked")
union Option<T>:
    Some(T)
    None
```

### Usage Patterns

```simple
# ---- COMPILE ERROR: ignored return value ----
buffer.push(42)           # ERROR[R9]: unused @must_use value
                          #   help: handle with 'val _ = ...' or '?? fallback'

# ---- ALLOWED: explicit handling ----
val result = buffer.push(42)        # OK: assigned
buffer.push(42) ?? handle_full()    # OK: coalesced
val _ = buffer.push(42)             # OK: explicit discard

# ---- ALLOWED: chained usage ----
if buffer.push(42).?:               # OK: used in condition
    print "pushed"

# ---- In @profile(critical): ALL non-void returns are @must_use ----
@profile(critical)
module controller

fn read_sensor() -> i64:
    42

fn bad_example():
    read_sensor()          # ERROR[R9]: return value of 'read_sensor' (i64) discarded
                           #   help: assign to variable or use result

fn good_example():
    val v = read_sensor()  # OK
    process(v)
```

### Enforcement

```
error[R9]: return value of function 'push' must be used
  --> src/buffer.spl:25
   | buffer.push(sensor_data)
   | ^^^^^^^^^^^^^^^^^^^^^^^^ unused return value
   = note: @must_use("push may fail if buffer is full")
   = help: use 'val _ = buffer.push(...)' to explicitly discard
   = help: or handle with '?? fallback_value'
```

---

## R10: Lifecycle Phase Functions (Init/Reset/Main)

### Rule

**Safety-critical modules must declare explicit lifecycle phases. The compiler enforces phase ordering and resource access rules.**

### Research: Naming Conventions Across Systems

After surveying AUTOSAR, CMSIS, Ada, Zig, NASA/JPL, FreeRTOS, and IEC 61131-3:

| Simple | Meaning | AUTOSAR Equivalent | Ada Equivalent | Zig Equivalent |
|--------|---------|-------------------|---------------|----------------|
| `@init` | Pre-main setup | `*_Init()` | `Initialize` | `init()` |
| `@deinit` | Teardown/cleanup | `*_DeInit()` | `Finalize` | `deinit()` |
| `@reset` | Restart/recover | `SystemReset()` | N/A | N/A |
| `@main` | Application logic | `*_MainFunction()` | `Main` | `main()` |

**Chosen convention**: `@init` / `@deinit` / `@reset` / `@main`

- `@init` + `@deinit` matches Zig/AUTOSAR (most modern embedded)
- `@reset` is unique to embedded (hardware reset vector)
- `@main` is universal

### Grammar: Phase Declarations

```simple
@profile(critical)
module motor_controller

# ---- Phase 1: INIT — runs before main, allocates resources ----
@init
fn system_init() -> i32:
    configure_gpio()
    init_pwm(frequency: 20000)
    pool_create(commands, capacity: 32)
    return 0                   # 0 = success, nonzero = error code

# ---- Phase 2: MAIN — application logic, no allocation ----
@main
fn run() -> i32:
    val cmd = commands.acquire() ?? return -1
    cmd.speed = read_sensor()
    execute(cmd)
    commands.release(cmd)
    return 0

# ---- Phase 3: RESET — triggered by watchdog/error/explicit call ----
@reset
fn emergency_reset() -> i32:
    disable_all_motors()
    system_init()              # OK: @reset can call @init
    return 0

# ---- Phase 4: DEINIT — teardown (optional, for graceful shutdown) ----
@deinit
fn shutdown() -> i32:
    disable_all_motors()
    pool_destroy(commands)
    return 0
```

### Phase Access Matrix

| Caller Phase | Can Call @init | Can Call @main | Can Call @reset | Can Call @deinit | Can Allocate |
|-------------|---------------|---------------|----------------|-----------------|-------------|
| `@init` | Yes | **No** | **No** | **No** | **Yes** |
| `@main` | **No** | Yes | **No** (trigger only) | **No** | **No** (pools only) |
| `@reset` | Yes | **No** | Yes | **No** | **Yes** |
| `@deinit` | **No** | **No** | **No** | Yes | **Yes** (freeing) |
| (unphased) | Yes | Yes | Yes | Yes | Yes |

### Return Type Convention

All phase functions return `i32` (or `i64`):
- `0` = success
- Nonzero = error code (application-defined)

This matches AUTOSAR `Std_ReturnType`, POSIX `main()` return, and CMSIS error codes.

```simple
# ---- Error code constants ----
val E_OK: i32 = 0
val E_INIT_FAILED: i32 = 1
val E_HW_ERROR: i32 = 2
val E_POOL_FULL: i32 = 3
val E_TIMEOUT: i32 = 4

@init
fn system_init() -> i32:
    val gpio_ok = configure_gpio()
    if not gpio_ok: return E_HW_ERROR
    val pool_ok = pool_create(commands, capacity: 32)
    if not pool_ok: return E_INIT_FAILED
    E_OK
```

### Enforcement

```
error[R10]: @main function cannot call @init function
  --> src/controller.spl:28
   | @main
   | fn run():
   |     init_pool(extra, 64)
   |     ^^^^^^^^^^^^^^^^^^^^ calls @init function 'init_pool'
   = note: allocation is only permitted during @init or @reset phase
   = help: pre-allocate in @init, use pool.acquire() in @main
```

```
error[R10]: @init function cannot call @main function
  --> src/controller.spl:12
   | @init
   | fn setup():
   |     run()
   |     ^^^^^ calls @main function 'run'
   = note: resources may not be ready during @init
```

---

## R11: Dynamic Dispatch Cycle Warnings

### Rule

**Warn when indirect calls (function pointers, trait dispatch, callbacks) create potential call cycles that cannot be statically resolved.**

### Rationale

- **MISRA C Rule 17.2**: "Functions shall not call themselves, either directly or indirectly"
- **SPARK**: Dispatching calls are restricted; must prove no cycles
- Extends R2 (circular call detection) to indirect calls

### Grammar: Dynamic Dispatch Annotations

```simple
# ---- Trait/interface dispatch creates potential cycle ----
trait Handler:
    fn handle(event: Event) -> Result<(), Error>

# The compiler cannot prove handle() implementations don't call back
fn dispatch_event(handler: Handler, event: Event):
    handler.handle(event)      # WARNING[R11]: potential cycle via dynamic dispatch
                               # note: Handler.handle() could call dispatch_event()

# ---- Resolution: annotate max call depth ----
@max_depth(4)
fn dispatch_event(handler: Handler, event: Event):
    handler.handle(event)      # OK: bounded at 4 levels

# ---- Resolution: annotate as acyclic ----
@acyclic
trait Handler:
    fn handle(event: Event) -> Result<(), Error>
    # Implementors promise not to call back into dispatch
```

### Function Pointer Analysis

```simple
# ---- Function pointer stored in struct ----
class Callback:
    handler: fn(i64) -> i64

fn invoke_callback(cb: Callback, value: i64) -> i64:
    cb.handler(value)          # WARNING[R11]: indirect call via function pointer
                               # note: target unknown, potential cycle

# ---- Resolution: register callbacks at init, freeze before main ----
@init
fn register_handlers():
    var table: [fn(Event); 16] = []
    table[0] = handle_sensor
    table[1] = handle_motor
    # Compiler can now analyze the concrete targets

@main
fn dispatch(event_type: i64, event: Event):
    table[event_type](event)   # OK: targets known from @init registration
```

### Severity

| Profile | Definite Cycle (static) | Potential Cycle (dynamic) |
|---------|------------------------|--------------------------|
| `@profile(critical)` | **Error** | **Warning** |
| `@profile(baremetal)` | **Error** | **Info** |
| `@profile(warn_all)` | **Warning** | **Warning** |
| Default | Off | Off |

### Enforcement

```
warning[R11]: potential call cycle via dynamic dispatch
  --> src/event.spl:32
   | fn dispatch(handler: Handler, event: Event):
   |     handler.handle(event)
   |     ^^^^^^^^^^^^^^^^^^^^^ indirect call — target unknown at compile time
   = note: Handler.handle() implementations may call dispatch()
   = help: add @acyclic to trait or @max_depth(N) to function
   = help: or register concrete handlers at @init for static analysis
```

---

## R12: Stack Usage Analysis

### Rule

**Every function must have statically bounded stack usage. The compiler reports worst-case stack frame + call-depth estimates.**

### Rationale

- **DO-178C**: Stack analysis required for DAL A-C certification
- **MISRA C Dir 4.1**: "Run-time failures shall be minimized" — includes stack overflow
- **NASA/JPL Rule 2**: All loops bounded → enables stack prediction
- **AUTOSAR**: Stack monitoring required per AUTOSAR OS specification

### Grammar: Stack Limits

```simple
# ---- Module-level stack budget ----
@profile(critical)
@stack_limit(4096)                # Max 4KB stack for this module
module controller

# ---- Function-level stack budget ----
@stack_limit(256)
fn process_packet(data: [u8; 128]) -> i64:
    var buffer: [u8; 64] = []     # 64 bytes local
    # Total: 128 (param) + 64 (local) + frame overhead = ~200 bytes
    pass_todo

# ---- ISR stack budget (typically much smaller) ----
@interrupt
@stack_limit(512)
fn timer_isr():
    val counter = read_timer()     # Must fit in ISR stack
    update_tick(counter)
```

### Compiler Stack Analysis

The compiler computes for each function:

```
STACK ANALYSIS REPORT — src/controller.spl
═══════════════════════════════════════════

Function                  Frame   Max Call Depth   Worst-Case Stack
─────────────────────────────────────────────────────────────────────
system_init()             128B    3                384B
run()                     256B    4                1024B
process_packet()          200B    2                400B
timer_isr()               64B     1                64B
─────────────────────────────────────────────────────────────────────
Module worst-case:                                 1024B (run)
Module stack limit:                                4096B
Status:                                            OK ✓
```

### Unknown Stack Usage Warning

```
warning[R12]: unknown stack usage in function 'process'
  --> src/handler.spl:15
   | fn process(data: [u8]):
   |                  ^^^^^ unsized parameter — stack usage unknown
   = note: [u8] is dynamically-sized; use [u8; N] for static analysis
   = help: use fixed-size array [u8; 256] or pass by reference
```

```
warning[R12]: call depth not statically bounded
  --> src/dispatch.spl:22
   | fn handle(event: Event):
   |     callback(event)
   |     ^^^^^^^^^^^^^^^ indirect call — call depth unknown
   = note: function pointer targets not resolved at compile time
   = help: register concrete handlers at @init or add @max_depth(N)
```

### Enforcement

```
error[R12]: stack usage exceeds limit
  --> src/isr.spl:8
   | @interrupt
   | @stack_limit(512)
   | fn sensor_isr():
   |     var big_buffer: [u8; 1024] = []
   |                     ^^^^^^^^^^^ 1024 bytes exceeds ISR stack limit (512)
   = help: reduce local variable sizes or move buffer to module-level pool
```

---

## R13: Implicit Allocation Detection

### Rule

**The compiler detects and reports all operations that implicitly allocate memory. In `@no_alloc` contexts these are errors; elsewhere they are warnings (configurable).**

### Rationale

- **Zig**: No hidden allocations — every allocating function takes an `Allocator` parameter
- **Rust `#[no_std]`**: `heapless` crate replaces `String`/`Vec` with fixed-capacity versions
- **Ada/SPARK**: `pragma Restrictions(No_Implicit_Heap_Allocations)`
- **MISRA**: Rule 21.3 (no `malloc`/`free`)

### Implicit Allocation Sources

| Operation | Allocates | Replacement |
|-----------|-----------|-------------|
| `"hello {x}"` (interpolation) | Yes — concat | `BoundedString<N>`, format to buffer |
| `a + b` (text concatenation) | Yes — new string | `BoundedString.append()` |
| `[1, 2, 3]` (array literal) | Yes — heap array | `[i64; 3]` fixed array |
| `arr.push(x)` (dynamic growth) | Yes — realloc | `BoundedVec<T, N>.push()` |
| `arr.map(\x: ...)` | Yes — new array | In-place loop |
| `arr.filter(\x: ...)` | Yes — new array | In-place with `BoundedVec` |
| `{"key": val}` (dict literal) | Yes — hash table | `BoundedMap<K, V, N>` |
| `text.split(",")` | Yes — array of strings | Iterator-based split |
| `text.replace(a, b)` | Yes — new string | In-place with `BoundedString` |
| Closure capture (heap) | Yes — closure env | Module-level fn or inline |

### Grammar: `@no_alloc` Tag on Types

```simple
# ---- Tag a container implementation as allocation-free ----
@no_alloc
class BoundedVec<T, const N: i64>:
    """Fixed-capacity vector. Stack-allocated. No heap."""
    data: [T; N]
    len: i64

    @must_use
    me push(item: T) -> Option<T>:
        if self.len >= N:
            return Some(item)      # Return item back — full
        self.data[self.len] = item
        self.len = self.len + 1
        nil                        # Success (Option = nil = no leftover)

    fn get(index: i64) -> T?:
        if index < 0 or index >= self.len: return nil
        Some(self.data[index])

# ---- Tag a string type as allocation-free ----
@no_alloc
class BoundedString<const N: i64>:
    """Fixed-capacity string. Stack-allocated. No heap."""
    bytes: [u8; N]
    len: i64

    @must_use
    me append(s: text) -> bool:
        # Returns false if would exceed capacity
        pass_todo

    fn as_text() -> text:
        # Returns view of internal buffer (no copy)
        pass_todo
```

### Grammar: Allocation-Free Trait

```simple
# ---- Marker trait for allocation-free types ----
trait NoAlloc:
    """Types implementing this trait guarantee no heap allocation."""
    pass_dn

# ---- Compiler auto-checks: a @no_alloc type must satisfy NoAlloc ----
# If any method allocates, compile error

# ---- Usage in function signatures ----
@no_alloc
fn safe_process(data: impl NoAlloc):
    # Compiler guarantees 'data' operations don't allocate
    pass_todo
```

### Grammar: Allocation-Free Suggestions

When the compiler detects an implicit allocation, it suggests the allocation-free alternative:

```
warning[R13]: implicit heap allocation detected
  --> src/logger.spl:18
   | val msg = "sensor {id}: value={reading}"
   |           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ string interpolation allocates
   = suggest: use BoundedString<64>:
   |     var msg: BoundedString<64> = BoundedString()
   |     msg.append("sensor ")
   |     msg.append_int(id)
   |     msg.append(": value=")
   |     msg.append_int(reading)
```

```
warning[R13]: implicit heap allocation — array growth
  --> src/collector.spl:25
   | var readings: [i64] = []
   | readings.push(value)
   |          ^^^^^^^^^^^ dynamic array may reallocate
   = suggest: use BoundedVec<i64, 64>:
   |     var readings: BoundedVec<i64, 64> = BoundedVec()
   |     readings.push(value)  # bounded, no realloc
```

### Severity

| Context | Behavior |
|---------|----------|
| Inside `@no_alloc` function | **Error** — hard fail |
| Inside `@profile(critical)` module | **Warning** — report all allocations |
| Inside `@profile(baremetal)` module | **Warning** — report all allocations |
| Default module | **Off** (or `--warn-alloc` flag) |

---

## R14: Implicit Numeric Narrowing Errors

### Rule

**No implicit narrowing conversions between numeric types. All narrowing must be explicit with defined overflow behavior.**

### Rationale

- **MISRA C Rule 10.3**: "The value of an expression shall not be assigned to an object with a narrower essential type"
- **MISRA C Rule 10.4**: "Both operands of an operator in which the usual arithmetic conversions are performed shall have the same essential type category"
- **Ada**: All type conversions explicit; mixing types is a compile error
- **AUTOSAR C++14 A5-0-2**: "The condition of an if-statement and loops shall have type bool"

### Grammar: Explicit Conversions

```simple
# ---- BANNED: implicit narrowing ----
val big: i64 = 100000
val small: i32 = big               # ERROR[R14]: implicit narrowing i64 -> i32
val byte_val: u8 = big             # ERROR[R14]: implicit narrowing i64 -> u8

# ---- ALLOWED: explicit conversion with defined behavior ----
val small: i32 = i32(big)          # Truncates (may lose data) — warning in critical
val small: i32 = i32.try_from(big) ?? 0  # Safe: returns default if out of range
val small: i32 = i32.saturate(big) # Clamps to i32.min..i32.max
val small: i32 = i32.wrap(big)     # Wraps (modular arithmetic)

# ---- BANNED: signed/unsigned mixing ----
val signed_val: i32 = -1
val unsigned_val: u32 = 42
val sum = signed_val + unsigned_val  # ERROR[R14]: mixed signed/unsigned arithmetic
                                     #   help: convert explicitly

# ---- ALLOWED: same-type arithmetic ----
val a: i32 = 10
val b: i32 = 20
val c: i32 = a + b                  # OK: same type

# ---- ALLOWED: explicit widening (always safe) ----
val small: i32 = 42
val big: i64 = i64(small)           # OK: widening is lossless
val big: i64 = small as i64         # Alternative syntax
```

### Conversion Functions

```simple
# ---- Conversion modes ----
val x: i64 = 100000

# Truncating (C-style, may lose data)
val a: i32 = i32(x)                # Truncates to lower 32 bits
                                   # WARNING in @profile(critical)

# Checked (returns Option)
val b: i32? = i32.try_from(x)     # nil if x not in i32 range
if b.?: process(b)

# Saturating (clamps to target range)
val c: i32 = i32.saturate(x)      # Clamps: max(i32.min, min(x, i32.max))

# Wrapping (modular arithmetic)
val d: i32 = i32.wrap(x)          # x mod 2^32, interpreted as signed

# Explicit widening (always safe, no annotation needed in non-strict)
val e: i64 = i64(small_val)       # Lossless
```

### Overflow Arithmetic

```simple
# ---- Default: trap on overflow in @profile(critical) ----
@profile(critical)
module controller

val a: i32 = 2_000_000_000
val b: i32 = 2_000_000_000
val c: i32 = a + b                 # RUNTIME ERROR: i32 overflow

# ---- Explicit overflow modes ----
val c: i32 = i32.wrapping_add(a, b)    # Wraps around
val c: i32 = i32.saturating_add(a, b)  # Clamps to i32.max
val c: i32 = i32.checked_add(a, b) ?? 0  # Returns Option

# ---- Or per-type overflow policy ----
type SafeCounter = i32 range 0..1000000 saturate   # Always saturates
type WrapCounter = u16 range 0..65535 wrap          # Hardware counter
```

### Enforcement

```
error[R14]: implicit narrowing conversion
  --> src/driver.spl:22
   | val raw: i64 = read_adc()
   | val byte: u8 = raw
   |                ^^^ implicit narrowing: i64 -> u8 may lose data
   = note: value range of i64 (-2^63..2^63-1) exceeds u8 (0..255)
   = help: use u8.try_from(raw) ?? 0
   = help: or u8.saturate(raw) for clamping
```

```
error[R14]: mixed signed/unsigned arithmetic
  --> src/calc.spl:15
   | val offset: i32 = -10
   | val addr: u32 = 0x1000
   | val result = offset + addr
   |              ^^^^^^^^^^^^^ i32 + u32: mixed sign arithmetic
   = help: convert to same type: i64(offset) + i64(addr)
```

---

## Complete Grammar Summary

### New Annotations

| Annotation | Target | Purpose |
|-----------|--------|---------|
| `@profile(name)` | module | Activate safety profile |
| `@no_alloc` | fn, module, class | Forbid heap allocation |
| `@must_use("reason")` | fn, union/type | Require return value handling |
| `@init` | fn | Init phase function |
| `@deinit` | fn | Teardown phase function |
| `@reset` | fn | Reset/recovery phase function |
| `@main` | fn | Application logic phase function |
| `@stack_limit(N)` | fn, module | Max stack usage in bytes |
| `@max_depth(N)` | fn | Max call depth for indirect calls |
| `@acyclic` | trait | Promise no callback cycles |
| `@bound(N)` | while/loop | Loop iteration bound (from R5) |
| `@allow(rule, reason: "...")` | fn | Relax a specific rule (from R1-R6) |

### New Type Syntax

| Syntax | Purpose | Example |
|--------|---------|---------|
| `type T = P range A..B` | Range type | `type Voltage = i64 range 0..3300` |
| `type T = P range A..B wrap` | Wrapping range | `type Angle = i64 range 0..359 wrap` |
| `type T = P range A..B saturate` | Saturating range | `type Counter = i64 range 0..65535 saturate` |
| `type T = P range A..B trap` | Trapping range (default) | `type Critical = i64 range 0..100 trap` |
| `[T; N]` | Fixed-size array | `val buf: [u8; 256]` |
| `BoundedVec<T, N>` | Fixed-capacity vector | `var v: BoundedVec<i64, 32>` |
| `BoundedString<N>` | Fixed-capacity string | `var s: BoundedString<64>` |
| `BoundedMap<K, V, N>` | Fixed-capacity map | `var m: BoundedMap<i64, text, 16>` |
| `Pool<T, N>` | Pre-allocated pool | `pool cmds: Pool<Command, 32>` |

### New Conversion Syntax

| Syntax | Purpose |
|--------|---------|
| `T(value)` | Explicit conversion (truncating) |
| `T.try_from(value)` | Safe conversion (returns `Option<T>`) |
| `T.saturate(value)` | Clamping conversion |
| `T.wrap(value)` | Wrapping/modular conversion |
| `T.checked_add(a, b)` | Checked arithmetic (returns `Option<T>`) |
| `T.saturating_add(a, b)` | Saturating arithmetic |
| `T.wrapping_add(a, b)` | Wrapping arithmetic |

---

## Implementation Priority

| Phase | Rules | Effort | Value | Dependencies |
|-------|-------|--------|-------|-------------|
| **1** | R9 (must_use) | Low | High | Extend existing ignored-return warnings |
| **2** | R14 (narrowing) | Medium | High | Type checker enhancement |
| **3** | R7 (no_alloc) | Medium | High | Allocation analysis pass |
| **4** | R13 (implicit alloc) | Medium | High | Builds on R7 analysis |
| **5** | R8 (range types) | High | Very High | New type system feature |
| **6** | R12 (stack analysis) | High | High | Frame analysis extension |
| **7** | R10 (lifecycle) | High | High | Phase checker, extends R4 |
| **8** | R11 (dispatch cycles) | Medium | Medium | Extends R2 call graph |

### Phase 1 is fastest ROI:
- R9 builds directly on existing `ignored_return_warning` in `src/core/interpreter/eval.spl`
- Add `@must_use` to attribute parser (already supports `@name("arg")`)
- Change warning to error in `@profile(critical)` context

### Phase 5 is highest value:
- Range types catch the most bugs in embedded code (off-by-one, overflow, invalid sensor readings)
- Ada's range types are cited by every safety-critical standard
- But requires type system changes — most implementation effort

---

## Complete Example: Safety-Critical Motor Controller

```simple
@profile(critical)
@no_alloc
@stack_limit(4096)
module motor_controller

# ===== Domain Types with Application Limits =====

type Voltage = i64 range 0..3300           # millivolts
type Speed = i64 range -10000..10000       # RPM
type Duty = i64 range 0..100              # PWM percentage
type Channel = i64 range 0..7             # ADC channels
type ErrorCode = i32 range 0..255

val E_OK: ErrorCode = 0
val E_HW: ErrorCode = 1
val E_RANGE: ErrorCode = 2
val E_POOL: ErrorCode = 3
val E_TIMEOUT: ErrorCode = 4

# ===== Data Types =====

class MotorCommand:
    target_speed: Speed
    duty: Duty
    channel: Channel

# ===== Resource Pools =====

var cmd_pool: Pool<MotorCommand, 16>

# ===== Lifecycle Functions =====

@init
fn system_init() -> i32:
    configure_gpio()
    init_pwm(frequency: 20000)
    cmd_pool = Pool(capacity: 16)
    i32(E_OK)

@reset
fn emergency_reset() -> i32:
    disable_all_motors()
    system_init()

@main
fn run() -> i32:
    val raw = read_adc(Channel(0))
    val voltage = Voltage.try_from(raw)
    if voltage == nil: return i32(E_RANGE)

    val speed = voltage_to_speed(voltage)
    val cmd = cmd_pool.acquire()
    if cmd == nil: return i32(E_POOL)

    cmd.target_speed = speed
    cmd.duty = speed_to_duty(speed)
    cmd.channel = Channel(0)
    execute_command(cmd)
    cmd_pool.release(cmd)
    i32(E_OK)

@deinit
fn shutdown() -> i32:
    disable_all_motors()
    i32(E_OK)

# ===== Helper Functions =====

@no_alloc
fn voltage_to_speed(v: Voltage) -> Speed:
    # Linear mapping: 0V -> 0 RPM, 3.3V -> 10000 RPM
    val raw = i64(v) * 10000 / 3300
    Speed.saturate(raw)

@no_alloc
fn speed_to_duty(s: Speed) -> Duty:
    val abs_speed = if i64(s) < 0: -i64(s) else: i64(s)
    val raw = abs_speed * 100 / 10000
    Duty.saturate(raw)

@no_alloc
fn execute_command(cmd: MotorCommand):
    set_pwm_duty(i64(cmd.channel), i64(cmd.duty))
    set_motor_direction(i64(cmd.channel), i64(cmd.target_speed) >= 0)
```

---

## References

| Standard | Rules Mapped |
|----------|-------------|
| MISRA C:2012 | R1(17.2), R5(15.4), R7(21.3), R9(17.7), R14(10.3, 10.4) |
| MISRA C++:2023 | R1(8.2.4), R5(9.5.2), R7(21.6.1), R9(0.1.2), R14(7.0.5) |
| AUTOSAR C++14 | R1(A7-5-2), R7(A18-5-1/2), R9(A0-1-2), R10(Init/DeInit), R14(A5-0-2) |
| Ada/SPARK | R1(No_Recursion), R7(No_Allocators), R8(range types), R12(stack analysis) |
| DO-178C | R1(MC/DC), R5(bounded), R7(no dynamic), R9(all outputs used), R12(stack) |
| NASA/JPL Power of Ten | R1(rule 1), R5(rule 2), R7(rule 3), R9(rule 7), R6(rule 5) |
| IEC 61508 (SIL 3-4) | R5(bounded exec), R8(range monitoring), R12(stack monitoring) |
| IEC 61131-3 (PLC) | R10(FB_init/FB_exit lifecycle) |

# Simple Numeric Robustness Specification

Robust numeric model for Simple that:

- Keeps user-facing types as `i64`, `f64` (with `int`/`float` aliases)
- Adds compile/runtime tracking of numeric hazards via generic `Checked<T>` enum
- Makes unhandled numeric hazards a compile-time error in embedded/critical builds
- Supports configurable "tiny floats behave like zero" mode (`small_like_zero`)

Grounded in IEEE-754's exception model (invalid, div-by-zero, overflow, underflow, inexact)
and common FTZ/DAZ practice.

---

## 1) Goals and Non-Goals

### Goals

1. **No silent NaN/Inf propagation** in critical code: the type system forces handling
2. **Ergonomic math**: `m{ }` blocks provide checked math without per-op checks
3. **Configurable float tiny behavior**: `small_like_zero` treats tiny nonzero as signed zero
4. **Type inference tracks hazards**: developers write `i64`, `f64`, compiler infers `Checked<T>`

### Non-Goals

- Tracking inexact rounding as a fault (too ubiquitous; optionally exposed as events)
- Replacing IEEE-754 semantics (we track and enforce, not override)

---

## 2) Numeric Exception Model

IEEE-754 defines five exception conditions: invalid, division by zero, overflow, underflow, inexact.

### 2.1 Float Fault Kinds

```simple
enum FloatFault:
    IsNaN           # invalid/indeterminate (0/0, Inf-Inf, 0*Inf)
    PosInf          # +infinity
    NegInf          # -infinity
    DivByZero       # x/0 where x != 0
    Overflow        # result exceeds representable range
    InvalidOp       # sqrt(-1), log(-1), asin(2), etc.
```

### 2.2 Integer Fault Kinds

```simple
enum IntFault:
    DivByZero       # a / 0, a % 0
    Overflow        # includes MIN_INT / -1
    ShiftOutOfRange # shift >= bitwidth or negative
    InvalidCast     # narrowing/out-of-range cast
```

### 2.3 Unified Fault Type

```simple
enum NumericFault:
    FloatErr(kind: FloatFault)
    IntErr(kind: IntFault)
```

### 2.4 Tiny Float Behavior (Policy-Level)

Two modes for underflow/subnormal handling:

- **`small_like_zero`** (default for embedded): tiny nonzero values canonicalize to signed zero.
  Mirrors FTZ/DAZ flags. If `0 < |x| < eps`, result is `+0.0` or `-0.0` preserving sign.
- **`strict_zero`** (optional): tiny nonzero becomes a fault (adds `TooSmall` variant)

---

## 3) App-Level Numeric Policy

Policy is configured via SDN (not a new syntax block). Place in project root or `__init__.sdn`:

```sdn
numeric_policy:
    default_int: i32
    default_float: f32
    float_tiny_mode: small_like_zero
    small_like_zero:
        pos_eps: 1e-20
    int_overflow_mode: checked
    severity:
        unhandled_numeric_fault: error
        lossy_cast: warn
        inexact_event: off
```

**Reading policy at runtime:**

```simple
use std.numeric_policy.{get_float_tiny_mode, get_overflow_mode, get_pos_eps}

val mode = get_float_tiny_mode()    # "small_like_zero" or "strict_zero"
val eps = get_pos_eps()             # 1e-20
```

**Notes:**
- `neg_eps` defaults to `-pos_eps` if omitted
- Signed zero matters: negative tiny becomes `-0.0`, so `1.0 / (-0.0) = -Inf`
- GPU/CPU may have their own FTZ rules; policy defines semantic intent

---

## 4) Types: Checked<T> and Refinements

### 4.1 Base User Types

```simple
# These are aliases resolved by the compiler per policy
# int  -> default_int (e.g., i32)
# float -> default_float (e.g., f32)

val x: i64 = 42
val y: f64 = 3.14
```

### 4.2 Checked<T> — The Hazard-Carrying Wrapper

`Checked<T>` is a generic enum representing either a valid value or a numeric fault:

```simple
enum Checked<T>:
    Value(v: T)
    Fault(f: NumericFault)
```

Key rule (critical profile):
> No implicit conversion from `Checked<T>` to `T`. Must handle with `??` or `?`.

**Why `Checked<T>` not `NaN<T>`:** The name `NaN` is misleading for integers (which have
no NaN). `Checked` accurately describes the semantics: "this computation was checked
and may have faulted."

### 4.3 Refinement Types (for Proofs + Optimization)

Refinements let the compiler eliminate runtime checks:

```simple
# Invariant: value != 0 (after tiny canonicalization for floats)
enum NonZero<T>:
    Valid(v: T)

# Invariant: not NaN, not +/-Inf
enum Finite<T>:
    Valid(v: T)
```

**Constructing refinements returns Checked:**

```simple
fn nonzero(x: f64) -> Checked<NonZero<f64>>:
    val canonicalized = canonicalize_tiny(x)
    if canonicalized == 0.0:
        Checked.Fault(NumericFault.FloatErr(FloatFault.DivByZero))
    else:
        Checked.Value(NonZero.Valid(canonicalized))

fn finite(x: f64) -> Checked<Finite<f64>>:
    if is_nan(x) or is_inf(x):
        Checked.Fault(NumericFault.FloatErr(FloatFault.IsNaN))
    else:
        Checked.Value(Finite.Valid(x))
```

---

## 5) Checked Math: `m{ }` Blocks with Policy

Math blocks (`m{ }`) already exist in Simple for math expressions. The numeric
robustness extension adds **policy awareness**:

### 5.1 Behavior by Policy

When `severity.unhandled_numeric_fault = error` (critical builds):
- `m{ }` produces `Checked<T>` and inserts checks/canonicalization as needed
- The compiler verifies all `Checked<T>` values are handled before use

When `severity.unhandled_numeric_fault = off` (default/non-critical builds):
- `m{ }` produces plain `T` with standard IEEE-754 behavior (NaN propagates silently)

### 5.2 Explicit Mode Selection

For per-expression control, use library functions instead of new syntax:

```simple
use std.numeric.{checked_div, checked_sqrt, checked_log}

# Checked versions return Checked<f64>
val result = checked_div(x, y)

# Fast versions (allow FTZ, approximate intrinsics)
val fast_result = fast_div(x, y)

# Raw versions (plain T, no fault tracking)
val raw_result = x / y
```

### 5.3 Tiny Canonicalization

When `float_tiny_mode = small_like_zero`, values are canonicalized:
- `0 < x < pos_eps` becomes `+0.0`
- `neg_eps < x < 0` becomes `-0.0`

```simple
fn canonicalize_tiny(x: f64) -> f64:
    val eps = get_pos_eps()
    if x > 0.0 and x < eps:
        return 0.0
    if x < 0.0 and x > -eps:
        return -0.0
    x
```

---

## 6) Handling Operators: `?` and `??`

### 6.1 Propagate with `?`

`x?` converts `Checked<T>` to `T` or returns early with the fault:

```simple
fn step(a: f64, b: f64, c: f64) -> Checked<f64>:
    val v = checked_div(a, b)
    val x = v?                  # if Fault -> return Fault early
    val w = checked_log(c)
    val y = w?
    Checked.Value(x + y)
```

### 6.2 Recover with `??`

`expr ?? default` provides a fallback for faults (existing Simple operator):

```simple
val x: f64 = checked_div(a, b) ?? 0.0
```

### 6.3 Recover with Match

For fine-grained fault handling, match on the `Checked<T>` enum:

```simple
val result = checked_div(x, y)
val x: f64 = match result:
    | Value(v) -> v
    | Fault(f) -> match f:
        | FloatErr(kind) -> match kind:
            | IsNaN -> 0.0
            | PosInf -> 9999999.0
            | NegInf -> -9999999.0
            | DivByZero -> 0.0
            | Overflow -> 9999999.0
            | InvalidOp -> 0.0
        | IntErr(_) -> 0
```

**Simpler common pattern — helper function:**

```simple
fn recover_float(result: Checked<f64>, fallback: f64) -> f64:
    match result:
        | Value(v) -> v
        | Fault(_) -> fallback

val x = recover_float(checked_div(a, b), 0.0)
```

---

## 7) Dangerous Operations (What Produces Checked<T>)

In critical builds, these operations produce `Checked<T>` instead of plain `T`.

### 7.1 Float Operations -> Checked<f64>

**A) Division and reciprocal:**

```simple
fn checked_div(x: f64, y: f64) -> Checked<f64>:
    val cy = canonicalize_tiny(y)
    if cy == 0.0:
        if canonicalize_tiny(x) == 0.0:
            Checked.Fault(NumericFault.FloatErr(FloatFault.IsNaN))   # 0/0
        else:
            if x > 0.0:
                Checked.Fault(NumericFault.FloatErr(FloatFault.PosInf))
            else:
                Checked.Fault(NumericFault.FloatErr(FloatFault.NegInf))
    else:
        Checked.Value(x / cy)
```

**B) Indeterminate forms (invalid operation):**
- `Inf - Inf`, `0 * Inf`, `Inf / Inf` produce `IsNaN`

**C) Domain-restricted functions (invalid operation):**

```simple
fn checked_sqrt(x: f64) -> Checked<f64>:
    if x < 0.0:
        Checked.Fault(NumericFault.FloatErr(FloatFault.InvalidOp))
    else:
        Checked.Value(sqrt(x))

fn checked_log(x: f64) -> Checked<f64>:
    if x < 0.0:
        Checked.Fault(NumericFault.FloatErr(FloatFault.InvalidOp))
    elif x == 0.0:
        Checked.Fault(NumericFault.FloatErr(FloatFault.NegInf))
    else:
        Checked.Value(log(x))
```

**D) Overflow-prone growth:**
- `exp`, `pow`, large mul/add chains produce `PosInf`/`NegInf` on overflow

**E) Conversions:**

```simple
fn checked_f64_to_i64(x: f64) -> Checked<i64>:
    if is_nan(x) or is_inf(x):
        Checked.Fault(NumericFault.IntErr(IntFault.InvalidCast))
    elif x > 9223372036854775807.0 or x < -9223372036854775808.0:
        Checked.Fault(NumericFault.IntErr(IntFault.InvalidCast))
    else:
        Checked.Value(int(x))
```

### 7.2 Integer Operations -> Checked<i64>

**A) Division / remainder:**

```simple
fn checked_div_i64(a: i64, b: i64) -> Checked<i64>:
    if b == 0:
        Checked.Fault(NumericFault.IntErr(IntFault.DivByZero))
    elif a == -9223372036854775808 and b == -1:
        Checked.Fault(NumericFault.IntErr(IntFault.Overflow))
    else:
        Checked.Value(a / b)
```

**B) Overflow detection (Zig-inspired tuple pattern):**

```simple
fn checked_add_i64(a: i64, b: i64) -> Checked<i64>:
    val max_i64 = 9223372036854775807
    val min_i64 = -9223372036854775808
    if a > 0 and b > max_i64 - a:
        Checked.Fault(NumericFault.IntErr(IntFault.Overflow))
    elif a < 0 and b < min_i64 - a:
        Checked.Fault(NumericFault.IntErr(IntFault.Overflow))
    else:
        Checked.Value(a + b)

fn checked_mul_i64(a: i64, b: i64) -> Checked<i64>:
    if a == 0 or b == 0:
        return Checked.Value(0)
    val max_i64 = 9223372036854775807
    val result = a * b
    # Check by division: if result / a != b, overflow occurred
    if result / a != b:
        Checked.Fault(NumericFault.IntErr(IntFault.Overflow))
    else:
        Checked.Value(result)
```

**C) Saturating arithmetic (Zig-inspired, no fault):**

```simple
fn saturate_add_i64(a: i64, b: i64) -> i64:
    val max_i64 = 9223372036854775807
    val min_i64 = -9223372036854775808
    if a > 0 and b > max_i64 - a:
        max_i64
    elif a < 0 and b < min_i64 - a:
        min_i64
    else:
        a + b
```

**D) Shifts:**

```simple
fn checked_shl_i64(x: i64, k: i64) -> Checked<i64>:
    if k < 0 or k >= 64:
        Checked.Fault(NumericFault.IntErr(IntFault.ShiftOutOfRange))
    else:
        Checked.Value(x << k)
```

---

## 8) Where Checked<T> Must Be Handled (Critical Profile)

When `severity.unhandled_numeric_fault = error`, any `Checked<T>` must be resolved
(`?` / `??` / `match`) before:

1. Assignment to a plain `T`
2. Branch conditions (`if`, `while`)
3. Indexing / slicing / address calculation
4. Hardware register access, MMIO, DMA descriptors
5. Leaving a module boundary (public API / FFI)
6. Use as a loop bound

This turns "unhandled numeric fault" into a **compile-time error** in critical apps.

---

## 9) Float Comparison: Robust Dual-Tolerance

The current `math_is_close()` uses only absolute tolerance, which fails for
large values and near-zero comparisons. Research shows combining relative
and absolute tolerance (numpy's `isclose` approach) is required:

```simple
fn float_eq_robust(a: f64, b: f64, rel_tol: f64, abs_tol: f64) -> bool:
    """Robust float comparison using combined relative + absolute tolerance.

    - Near zero: uses absolute tolerance (avoids division-by-near-zero)
    - Normal values: uses relative tolerance (scales with magnitude)
    - Exact equality: short-circuits for identical values (including +/-0)

    Based on numpy.isclose: abs(a-b) <= abs_tol + rel_tol * max(abs(a), abs(b))
    """
    if a == b:
        return true
    val diff = math_abs(a - b)
    val max_val = math_max(math_abs(a), math_abs(b))
    diff <= abs_tol + rel_tol * max_val

# Convenience with common defaults
fn float_eq(a: f64, b: f64) -> bool:
    float_eq_robust(a, b, 1e-9, 1e-12)
```

**Why dual tolerance:**
- Absolute-only fails: `1e15 + 0.001` vs `1e15` looks equal with `tol=0.01`
  but differs by 1e-18 relative
- Relative-only fails: `1e-20` vs `0.0` has infinite relative difference
- Combined formula: `abs(a-b) <= abs_tol + rel_tol * max(abs(a), abs(b))`

---

## 10) Numeric Events (Optional Flag-Based Tracking)

IEEE includes underflow and inexact as exceptions, but they produce finite results
plus flags. These don't need type-level tracking:

### 10.1 Faults vs Events

- **Faults** (type-level via `Checked<T>`): NaN, Inf, div0, overflow, shift, cast
- **Events** (flag-level): underflow occurred, inexact occurred, tiny-canonicalized

### 10.2 API

```simple
use std.numeric_events.{numeric_events_get, numeric_events_clear}

# Check what events occurred during a computation
val events = numeric_events_get()   # returns [text]
numeric_events_clear()

# Event names: "underflow", "inexact", "tiny_canonicalized"
```

Events use bit flags internally for zero overhead when not observed.

---

## 11) PyTorch Interop Mapping

### 11.1 nan_to_num

```simple
fn nan_to_num(x: f64, nan_val: f64, posinf_val: f64, neginf_val: f64) -> f64:
    """Replace NaN/Inf with specified values (mirrors torch.nan_to_num)."""
    if is_nan(x):
        nan_val
    elif is_posinf(x):
        posinf_val
    elif is_neginf(x):
        neginf_val
    else:
        x

# Default behavior: NaN->0, +Inf->max, -Inf->min
fn nan_to_num_default(x: f64) -> f64:
    nan_to_num(x, 0.0, 9999999.0, -9999999.0)
```

### 11.2 clip / clamp (Already Exists)

```simple
# Already in std/math.spl as math_clamp:
# fn math_clamp(x: f64, lo: f64, hi: f64) -> f64
```

### 11.3 Flush Denormals Mapping

PyTorch's `torch.set_flush_denormal(True)` maps to `small_like_zero` policy.
Simple provides deterministic behavior via explicit eps-band canonicalization
rather than relying on hardware FTZ flags.

---

## 12) Backend Notes: CPU, CUDA, and Fast Math

### 12.1 CPU FTZ/DAZ

CPU FTZ/DAZ flags are common performance optimizations. Simple's
`small_like_zero` policy provides the same semantics deterministically:
- Backend MAY set hardware FTZ/DAZ flags as an optimization
- But the language guarantees the eps-band canonicalization regardless

### 12.2 CUDA Notes

GPU behavior is instruction-dependent (some atomics operate in FTZ mode
regardless of global settings). Simple's contract:
- Critical policy: compiler inserts explicit finite checks
- Non-critical: backend may rely on hardware FTZ behavior

---

## 13) Compiler Diagnostics

### 13.1 Required Diagnostics (Critical Profile)

```
error: unhandled numeric fault: 'Checked<f64>' must be handled before use as 'f64'
error: unhandled numeric fault: 'Checked<i64>' must be handled before use as 'i64'
warning: lossy cast from 'f64' to 'i32' (configurable)
info: tiny value canonicalized to +/-0 under small_like_zero (optional)
```

### 13.2 Spec Test Examples

```simple
describe "Numeric Robustness":

    it "checked_div returns fault on divide by zero":
        val result = checked_div(1.0, 0.0)
        match result:
            | Fault(_) -> expect(true).to_equal(true)
            | Value(_) -> expect(false).to_equal(true)

    it "checked_div returns value on normal division":
        val result = checked_div(10.0, 2.0)
        match result:
            | Value(v) -> expect(v).to_equal(5.0)
            | Fault(_) -> expect(false).to_equal(true)

    it "checked_sqrt faults on negative input":
        val result = checked_sqrt(-1.0)
        match result:
            | Fault(_) -> expect(true).to_equal(true)
            | Value(_) -> expect(false).to_equal(true)

    it "canonicalize_tiny flushes small values to zero":
        # Assuming pos_eps = 1e-20
        val tiny = 1e-30
        val result = canonicalize_tiny(tiny)
        expect(result).to_equal(0.0)

    it "?? provides fallback for faulted computation":
        val x = checked_div(1.0, 0.0) ?? 0.0
        expect(x).to_equal(0.0)

    it "checked_add_i64 detects overflow":
        val max_i64 = 9223372036854775807
        val result = checked_add_i64(max_i64, 1)
        match result:
            | Fault(_) -> expect(true).to_equal(true)
            | Value(_) -> expect(false).to_equal(true)

    it "saturate_add_i64 clamps on overflow":
        val max_i64 = 9223372036854775807
        val result = saturate_add_i64(max_i64, 100)
        expect(result).to_equal(max_i64)

    it "float_eq_robust handles near-zero comparison":
        expect(float_eq_robust(0.0, 1e-15, 1e-9, 1e-12)).to_equal(true)
        expect(float_eq_robust(0.0, 1.0, 1e-9, 1e-12)).to_equal(false)

    it "float_eq_robust handles large value comparison":
        val a = 1000000000.0
        val b = 1000000000.000001
        expect(float_eq_robust(a, b, 1e-9, 1e-12)).to_equal(true)
```

---

## 14) Minimal Examples

### A) Safe expression with recovery

```simple
val x: f64 = checked_div(a, b) ?? 0.0
val y: f64 = checked_log(z) ?? 0.0
val result = x + y
```

### B) Safe expression with propagation

```simple
fn compute(x: f64, y: f64, z: f64) -> Checked<f64>:
    val safe_y = nonzero(y)?    # propagates fault if y is zero
    val div_result = checked_div(x, safe_y.v)?
    val log_result = checked_log(z)?
    Checked.Value(div_result + log_result)
```

### C) Full fault recovery

```simple
fn safe_compute(x: f64, y: f64) -> f64:
    val result = checked_div(x, y)
    match result:
        | Value(v) -> v
        | Fault(f) -> match f:
            | FloatErr(kind) -> match kind:
                | DivByZero -> 0.0
                | _ -> -1.0
            | IntErr(_) -> 0
```

### D) Integer checked arithmetic

```simple
fn safe_sum(items: [i64]) -> Checked<i64>:
    var total = Checked.Value(0)
    for item in items:
        val current = total?        # propagate if already faulted
        total = checked_add_i64(current, item)
    total
```

---

## 15) Summary: What's Handled?

| Hazard | Mechanism | Overhead |
|--------|-----------|----------|
| NaN, +/-Inf | `Checked<f64>` + mandatory handling | Zero when not in critical mode |
| Integer div0/overflow | `Checked<i64>` + mandatory handling | Pre-op bounds check |
| Shift out of range | `checked_shl_i64` / `checked_shr_i64` | Range check on shift amount |
| Narrowing cast | `checked_f64_to_i64` | Range + finiteness check |
| Tiny/subnormal | `small_like_zero` policy | Eps comparison at block boundary |
| Underflow/inexact | Optional events (flags) | Zero unless events enabled |
| Lossy cast | Compiler warning (configurable) | Compile-time only |

---

## 16) Efficiency Design Rationale

### Why Functions, Not Operators

The original proposal used `m[checked]{...}` / `m[fast]{...}` / `m[raw]{...}` syntax.
This was rejected because:

1. **Parser complexity**: `m[mode]{...}` requires new token types and grammar rules,
   slowing down parsing for ALL code even when numeric robustness isn't used
2. **Incremental adoption**: Functions let you check one operation at a time;
   block syntax forces all-or-nothing within a block
3. **Debuggability**: Each checked call is a clear function boundary for debugging
4. **Composability**: Functions compose naturally with `?`, `??`, `match`, pipes

### Why Checked<T>, Not NaN<T>

1. `NaN` is misleading for integers (integers have no NaN concept)
2. `Checked` accurately describes semantics for both int and float
3. Avoids confusion with IEEE-754's specific NaN encoding

### Zero-Cost When Not Used

In non-critical builds (`severity.unhandled_numeric_fault = off`):
- `Checked<T>` functions are not called
- `m{ }` blocks produce plain `T`
- No runtime overhead
- Compiler does not emit diagnostics

### Zig-Inspired Saturating Arithmetic

Saturating functions (`saturate_add_i64`, etc.) return plain `T`, not `Checked<T>`,
because saturation IS the handling strategy. This avoids unnecessary wrapping
when the developer explicitly chose clamping behavior.

### Combined Tolerance for Float Comparison

Research from Random ASCII, ACCU, and numpy shows:
- Absolute-only tolerance breaks at large magnitudes
- Relative-only tolerance breaks near zero
- Combined formula `abs(a-b) <= abs_tol + rel_tol * max(abs(a), abs(b))` handles all ranges
- Single comparison, no branching beyond the initial `a == b` short-circuit

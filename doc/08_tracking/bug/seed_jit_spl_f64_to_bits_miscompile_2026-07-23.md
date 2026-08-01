# Seed JIT miscompiles `spl_f64_to_bits` (float→bits) + interpreter traps on f64 div-by-zero

- **Date:** 2026-07-23
- **Component:** Rust bootstrap-seed `simple` binary (seed-only; not the self-hosted `bin/simple`)
- **Severity:** Seed codegen bug — interpreter-workaroundable. Forces float-bit-reinterpretation models to run interpreter-only.
- **Verified with seed:** `.../scratchpad/wjob` (ELF x86-64, BuildID `4b93906bb31ec7c91849ba14f6d66c069d7fa782`)

Two independent seed-runtime defects surfaced while bringing up the
`rv64gc_rtl` FPU model, which depends on IEEE float↔bits reinterpretation.

---

## Issue 1 — JIT miscompiles `spl_f64_to_bits`: wrong stored value + broken i64 equality

### Symptom
Under the seed's **default JIT** execution mode, the `i64` produced by
`extern fn spl_f64_to_bits(value: f64) -> i64` is not a plain integer. It prints
correctly when used directly, but:

- (a) after being stored into and read back from a `[i64]` element it comes back
  as a **different, wrong** bit pattern; and
- (b) two `i64` values that print identically compare `==` as **false**.

The value behaves like a boxed float masquerading as `i64`: the box tag survives
into array-store/readback and into the equality path, so both mangle it. Under
`SIMPLE_EXECUTION_MODE=interpreter` the exact same source is fully correct.

`f64_bits(3.0)` must be IEEE `0x4008000000000000` = `4613937818241073152`.

### Minimal repro
`repro_bits.spl`:
```
extern fn spl_f64_to_bits(value: f64) -> i64

fn f64_to_bits(v: f64) -> i64:
    return spl_f64_to_bits(v)

fn main() -> i64:
    val b = f64_to_bits(3.0)
    print("bits=")
    print(b)
    print("\n")
    var arr: [i64] = [0, 0, 0]
    arr[1] = b
    val readback = arr[1]
    print("readback=")
    print(readback)
    print("\n")
    print("eq=")
    if readback == b:
        print("true")
    else:
        print("false")
    print("\n")
    return 0
```

### Verbatim transcript
```
=== JIT (default) ===
bits=
4613937818241073152

readback=
2251799813685248

eq=
false

=== INTERP (SIMPLE_EXECUTION_MODE=interpreter) ===
bits=
4613937818241073152

readback=
4613937818241073152

eq=
true

=== expected 0x4008000000000000 = 4613937818241073152 ===
```

JIT: direct print is right, but readback is `2251799813685248` (`0x8000000000000`)
and `eq=false`. Interpreter: readback correct and `eq=true`.

### Root-cause hypothesis
JIT float-box tagging. `spl_f64_to_bits` returns an `i64` that the JIT still
carries with a float box/tag rather than a raw integer. The tag is transparent to
`print` (which unboxes) but corrupts:
- the `[i64]` store/readback lane (re-tag/shift mangles the bits →
  `0x8000000000000`), and
- the integer `==` comparator (compares boxed-float representation, so
  bit-identical values are unequal).
Same tag-box shift family as previously seen with `BoxInt <<3` mangling
enum heap-handles through `ANY` (SEED-specific). The interpreter keeps the
value as a plain `i64`, so it is correct.

### Impact + workaround
Any `.spl` model using float-bit reinterpretation (float↔bits) miscompiles under
the seed JIT. **Workaround: run such models interpreter-only**
(`SIMPLE_EXECUTION_MODE=interpreter`) until the self-hosted `bin/simple` is
deployed / the seed JIT box tagging is fixed.

---

## Issue 2 — Interpreter traps on host f64 divide-by-zero instead of IEEE ±inf

### Symptom
Under `SIMPLE_EXECUTION_MODE=interpreter`, a float divide by zero **traps** with
`error[E2001]: division by zero` instead of producing IEEE `+inf`/`-inf`. The JIT
correctly yields `inf`. So float models must guard `b == 0` before `a / b` to stay
interpreter-safe (and interpreter-only is exactly what Issue 1 forces).

### Minimal repro
`repro_div.spl`:
```
fn main() -> i64:
    val a: f64 = 1.0
    val b: f64 = 0.0
    val c = a / b
    print(c)
    print("\n")
    return 0
```

### Verbatim transcript
```
=== INTERP div-by-zero ===
error[E2001]: division by zero
  = help: check the divisor before dividing
=== JIT div-by-zero ===
inf
```

### Root-cause hypothesis
Non-IEEE division in the interpreter: the interpreter applies the integer
divide-by-zero guard (E2001) to `f64` division as well, instead of letting the
host FPU produce `±inf`/`NaN` per IEEE-754.

### Impact + workaround
Interpreter-run float models cannot rely on IEEE inf/NaN semantics for `/0`.
**Workaround: guard `b == 0` before every `a / b`** in float models.

---

## Applied in-tree
Both workarounds are already applied by `src/lib/hardware/rv64gc_rtl/fpu.spl`
and its probe `test/01_unit/lib/hardware/rv64gc_rtl/fpu_probe.spl`: the FPU model
runs interpreter-only (Issue 1) and guards divisors before dividing (Issue 2).

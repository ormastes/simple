# Stage-2 native codegen lowers f64 `+ - * /` as integer ops on the raw bit patterns (aarch64)

**Filed:** 2026-09-05
**Severity:** high — silent wrong values, no diagnostic, no crash
**Status:** open
**Area:** Stage-2 native codegen (aarch64-unknown-linux-gnu)

## Summary

Every f64 **binary arithmetic** operation compiled by the admitted Stage-2
compiler produces a wrong value. The results are not random: they are exactly
what you get by performing the corresponding **signed integer** operation on the
two operands' IEEE-754 bit patterns and reinterpreting the result as an f64.

f64 *literals*, f64 *storage/printing*, and integer arithmetic are all correct.
The damage is confined to the arithmetic (and comparison — see below) lowering.

This is a sixth defect of the same silent-wrong-value class as
`stage2_native_codegen_silent_wrong_values_aarch64_2026-09-05.md`, and is
**not** one of the five recorded there. That record's "What passes" section
verified *integer* arithmetic only; f64 was never exercised.

## How reproduced

Compiler: `build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple`
(152,326,376 bytes, 2026-09-05 08:06), default backend.
Reference: `bin/simple` -> `bin/release/aarch64-unknown-linux-gnu/simple`
(154,560,904 bytes, 2026-09-04 14:46), the Rust seed, interpreting the same file.

```
cd build/bootstrap/stage2/aarch64-unknown-linux-gnu
SIMPLE_BOOTSTRAP=1 \
SIMPLE_RUNTIME_PATH=<repo>/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-runtime-authority \
./simple native-build --source <repo>/src/app/cli --source <repo>/src/lib \
  --entry-closure --entry <ABS probe.spl> -o <ABS out>
```

## Evidence

Probe (`val f = 1.5`, `val g = 2.25`), interpreter vs native:

| expr | interpreter | stage2 native |
|---|---|---|
| `f` | `1.5` | `1.5` (ok) |
| `g` | `2.25` | `2.25` (ok) |
| `f + g` | `3.75` | `NaN` |
| `f - g` | `-0.75` | `-NaN` |
| `f * g` | `3.375` | `0.0` |
| `f / g` | `0.6666666666666666` | `0.0` |
| `1.5 + 2.25` (literals) | `3.75` | `NaN` |
| `addf(1.5, 2.25)` (f64 param + return) | `3.75` | `NaN` |

## Root cause is pinned by the bit patterns, not inferred

`1.5` = `0x3FF8000000000000`, `2.25` = `0x4002000000000000`.

- **add:** `0x3FF8… + 0x4002… = 0x7FFA000000000000` -> exponent all ones,
  mantissa nonzero = **NaN**. Matches.
- **sub:** `0x3FF8… - 0x4002… = 0xFFF6000000000000` -> sign set, exponent all
  ones, mantissa nonzero = **-NaN**. Matches.
- **mul:** both operands have >= 48 trailing zero bits, so the low 64 bits of
  the integer product are zero = **0.0**. Matches.
- **div:** integer division of the two patterns truncates to 0 = **0.0**. Matches.

Two further probes make this decisive, because they predict *specific finite
numbers* rather than just NaN:

| expr | interpreter | stage2 native | predicted by i64 lowering |
|---|---|---|---|
| `0.5 + 0.5` | `1.0` | `2.2471…e307` | `0x3FE0…+0x3FE0… = 0x7FC0…` = 2^1021 = **2.2471…e307** |
| `1.0 + 1.0` | `2.0` | `8.9884…e307` | `0x3FF0…+0x3FF0… = 0x7FE0…` = 2^1023 = **8.9884…e307** |
| `0.0 - 1.5` | `-1.5` | `-3.0` | `0 - 0x3FF8… = 0xC008…` = **-3.0** |
| `0.0 - 1.0` | `-1.0` | `-4.0` | `0 - 0x3FF0… = 0xC010…` = **-4.0** |

All four predicted values match the observed native output exactly. The
lowering is emitting integer `add`/`sub`/`mul`/`sdiv` where it must emit
`fadd`/`fsub`/`fmul`/`fdiv`.

## Comparison is affected too, and currently hides itself

`f < g` and `-1.5 < -1.0` both returned the *correct* answer natively, but that
is a coincidence, not evidence of correctness: for two floats of the same sign,
signed-integer ordering of the bit patterns agrees with float ordering. In the
`-1.5 < -1.0` probe the native operands were already the corrupted `-3.0` and
`-4.0`, and a signed i64 compare of *those* patterns still returned `true`. A
comparison probe therefore cannot be used to argue f64 compare is sound; the
discriminating case is a mixed-sign pair (e.g. `-0.0 < 0.0`, or any negative vs
positive where the negative's pattern has the high bit set and so sorts *below*
every positive as unsigned but *above* as float, depending on the compare kind
emitted).

## Suggested triage

Independent of defects 1-3 of the sibling record (indirect-call lowering) and of
defect 5 (unresolved-method dispatch). Look for the binop lowering site that
selects an integer opcode from operand *size* (8 bytes) rather than operand
*type*, so `f64` falls into the i64 path. The fact that literals and
storage/printing are correct means the type information survives to that point
and is being discarded at instruction selection.

## Probes

`.spl` probes used are throwaway scratchpad files; both are reproduced inline
above in full (the `f`/`g` table and the four bit-pattern predictions). Any
file containing `val a = 1.5` / `val b = 2.25` / `print "{a + b}"` reproduces it
in one line.

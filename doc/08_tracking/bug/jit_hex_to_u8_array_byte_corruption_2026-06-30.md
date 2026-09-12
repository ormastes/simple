# JIT/compiled mode corrupts `[u8]` built via `((hi<<4)|lo).to_u8()` loop

- **Filed:** 2026-06-30
- **Severity:** High (silently corrupts byte arrays under JIT/native; interpreter is correct)
- **Area:** compiler — JIT/native codegen for `i64 -> u8` (`to_u8()`) and/or u8 array push in a tight loop
- **Status:** CLOSED (2026-09-12) — not reproducible; see "Re-check 2026-09-12"

## Summary

A pure-Simple hex-string → `[u8]` decoder produces the **correct array length**
but **garbage byte values** when executed under JIT/compiled mode. The exact
same code returns correct bytes under the interpreter.

This is the standard hex-decode idiom used widely, including the X.509 unit
spec's own `_hex_to_u8_array` helper
(`test/01_unit/lib/common/cert/x509_spec.spl`).

## Reproduction

```simple
fn hexn(c: text) -> i64:
    if c >= "0" and c <= "9":
        c.char_code_at(0) - 48
    elif c >= "a" and c <= "f":
        c.char_code_at(0) - 87
    else:
        c.char_code_at(0) - 55

fn h2b(hex: text) -> [u8]:
    val bc = hex.length() / 2
    var r: [u8] = []
    var i: i64 = 0
    while i < bc:
        val hi = hexn(hex.char_at(i*2))
        val lo = hexn(hex.char_at(i*2+1))
        r.push(((hi<<4)|lo).to_u8())
        i = i + 1
    r

fn main() -> i64:
    val der = h2b("308201610a")   # expected bytes: 48 130 1 97 10
    print("len={der.len()}")
    print("b0={der[0u64].to_i64()} b1={der[1u64].to_i64()} b2={der[2u64].to_i64()}")
    0
```

Run with `bin/simple run` (JIT path):
- `len=5`  ✓ (correct)
- bytes observed: `b0=249 b1=251 b2=250 ...` — garbage, nearly constant ~249-251
  regardless of input nibbles. Expected `48 130 1 97 10`.

Under interpreter fallback the same code prints the correct bytes.

## Impact

- Any pure-Simple code that builds a `[u8]` from computed `to_u8()` values in a
  loop is unreliable under JIT/native.
- Concretely: `test/01_unit/lib/common/cert/x509_spec.spl` is designed to fire
  its field-value assertions under compiled/native mode (see spec header lines
  19-21 and `.claude/memory/feedback_compile_mode_false_greens.md`). Because the
  spec's own cert bytes are corrupted by this codegen bug **before** they reach
  the parser, compiled-mode verification of that spec is impossible until this
  is fixed. The spec currently passes under the interpreter runner, and the new
  `src/lib/common/cert/x509_typed.spl` parser was independently verified correct
  by executing it under the interpreter (all parsed fields match the expected
  ECDSA P-256 cert values).

## Suspected root cause

`i64 -> u8` conversion (`to_u8()`) and/or `[u8].push` of a converted value in a
JIT-compiled loop. The near-constant garbage (~249-251 ≈ small negative i8
wrap) suggests the converted value is being read from a wrong/uninitialized
slot or sign-extended incorrectly. Related documented class:
`feedback_native_build_codegen_i64_boxing_bugs`.

## Not yet done

Minimal isolation of whether the corruption is in `to_u8()`, the bitwise
`(hi<<4)|lo`, `char_at`/`char_code_at`, or `[u8].push` under JIT. Needs a
compiler-side investigation in the JIT/MIR lowering path.

## Re-check 2026-09-12

Binary: `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b…`, `Simple Language v1.0.0-rc.1` (aarch64 host).

The record's own reproducer, run unchanged on both lanes:

```
$ bin/simple run h2b.spl
len=5
b=48,130,1,97,10
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run h2b.spl
len=5
b=48,130,1,97,10
```

Expected `48 130 1 97 10`; the defect produced `249 251 250 …`. Both engines
are correct and agree. **Not reproducible** — status CLOSED.

Regression guard: `test/01_unit/bugs/jit_hex_to_u8_array_byte_corruption_spec.spl`
(6 examples). It asserts the byte **values**, not only `len()` — a length-only
assertion was green throughout the original defect, which is how it survived.
Coverage: the record's DER prefix, both nibble halves at `00/0f/f0/ff`, a
lowercase and an uppercase alphabetic run, and the empty input.

```
SPEC FILE VERDICT: test/01_unit/bugs/jit_hex_to_u8_array_byte_corruption_spec.spl outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0
```

Non-vacuity proof: substituting the documented garbage bytes (`249 251 250 …`)
into the two value assertions turns the file RED —
`outcome=ERROR declared>=6 executed=6 passed=4 failed=2 skipped=0 dropped=0`.

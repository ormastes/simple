# Bug: FixedVec.shr_logical produces arithmetic shift on signed i32 input

**Discovered:** 2026-05-02 (Wave F5 D5 spec retest)
**File:** `src/lib/nogc_sync_mut/simd/fixed.spl:262-269`
**Test that fails:** `test/unit/lib/simd/fixed_spec.spl` F-10

## Symptom

```
F-10: shr_logical and shr_arith differ on negative i32 values
expected -4 > 0 to hold
```

The test creates a `FixedVec<i32>` containing `-8` and expects:
- `shr_logical(1)` → `0x7FFFFFFC` (positive, top bit zero-filled)
- `shr_arith(1)` → `-4` (sign-extended)

Both currently return `-4` because the impl uses Simple's `>>` operator,
which is arithmetic shift on signed integers.

## Source

```
fn shr_logical(self, count: u32) -> Self:
    val n = self.lanes
    var out: [T] = []
    var i = 0
    while i < n:
        out.push(self.elements[i] >> count)   # ← always arithmetic on i32
        i = i + 1
    FixedVec(elements: out, lanes: n)

fn shr_arith(self, count: u32) -> Self:
    # same body — both impls are identical, only the name differs
```

## Root cause

Simple's `>>` on signed integer types performs sign-preserving arithmetic
shift. There is no language-level distinction between logical (unsigned)
and arithmetic (signed) shift on a single typed operand.

C2 §1.1 trait surface specifies `shr_logical` and `shr_arith` as distinct
operations per Vector op-coverage matrix. The interpreter implementation
ignores the distinction.

## Proposed fix

Two options, neither trivial in current interpreter:

1. **Cast through unsigned in the impl:**
   ```
   out.push(((self.elements[i] as u32) >> count) as T)
   ```
   Blocked by `feedback_simd_trait_alias_gap.md` reports — interpreter
   does not support `i32 as u32` round-trip cleanly. D4 hit this exact
   limitation.

2. **Mask the sign bit then shift:**
   ```
   val masked = self.elements[i] & 0xFFFFFFFF   # widen to i64 conceptually
   out.push((masked >> count) as i32)
   ```
   Requires i64 intermediate which the interpreter handles, but the
   final `as i32` cast may also fail.

3. **Add `rt_shr_logical_i32(x: i32, count: u32) -> i32` extern**
   that does the right thing in Rust seed runtime. Per memory
   `feedback_extern_bootstrap_rebuild.md`, requires
   `bootstrap-from-scratch.sh --deploy`.

Option 3 is cleanest but heavyweight. Option 2 is the smallest change
that should work without seed rebuild — try first.

## Workaround

None within F5 scope. Test stays failing. M1+ stdlib hardening should
take this on as the FixedVec impl gets retargeted onto MIR opcodes.

## Cross-references

- `feedback_simd_trait_alias_gap.md` — interpreter cast/method-resolution gaps
- C2 §1.1 — Vector trait `shr_logical`/`shr_arith` op spec
- C3a backend strict-emit table for x86 `psrld`/`psrad` and ARM `usra`/`ssra`

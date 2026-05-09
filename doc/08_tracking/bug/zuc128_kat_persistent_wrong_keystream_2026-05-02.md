# ZUC-128 KAT: Persistent Wrong Keystream (27bede74 expected, 6b8f9a89 got)

**Status:** FIXED 2026-05-02 — S-boxes corrected + u32 arithmetic-shift workarounds (21809848fd). All 8 KAT pass.
**Severity:** Blocking — ZUC-128 keystream KAT fails; EEA3/EIA3 also wrong.
**Affected file:** `src/os/crypto/zuc.spl`
**Spec file:** `test/unit/os/crypto/zuc_kat_spec.spl`
**Path:** `bug` track.

## Symptom

All-zero key/IV produces z[0] = `6b8f9a89` (expected `27bede74`).
Both z[0] and z[1] return the same value `6b8f9a89`.

**Confirmed (via sentinel test):** The file IS executing. Replacing `zuc_keystream`
body with `ks.push(0xDEADBEEFu32)` produced `deadbeef` in the test output.
So `6b8f9a89` is a genuine algorithmic wrong-value, not a caching artifact.

## Fixes Applied (Attempt 1 — F-function algorithm)

Fixed 4 bugs in `_f_out_w` / `_f_update`:

1. W formula: `(R1+X0)^R2` → `(X0^R1)+R2` (XOR first, then ADD)
2. W1: `r1 ^ x1` → `_add32(r1, x1)` (ADD not XOR)
3. u/v: `rotl-XOR` → `(w1<<16)|(w2>>16)` (shift-OR, not rotation-XOR)
4. L/S order: S-then-L → L-then-S (L applied first to bit-concat, then S)

Result: still `6b8f9a89`. Output unchanged.

## Fixes Applied (Attempt 2 — u64 arithmetic-shift workaround)

Applied `_logical_shr64` workaround per
`doc/08_tracking/bug/u64_right_shift_fn_param_arithmetic_2026-05-02.md`:

- Added `_logical_shr64(x: u64, n: u64) -> u64` helper using AND-mask
- Applied to `_rotl32` right-shift component (`xi >> (32u64 - ni)`)
- Applied to `_mod31` (`v >> 31`)
- Applied to `_f_update` (`w2u >> 16`, `w1u >> 16`)

Result: still `6b8f9a89`. Output unchanged.

Both `md5sum` and `grep` confirmed edits landed in the source file between runs.
No ZUC-specific `.smf` cache files exist. Single copy of `zuc.spl` in repo.

## Revised Hypothesis

**z[0] == z[1]** is confirmed as a real algorithmic output. This means either:

### H1: LFSR state not advancing between `_zuc_run_32` calls
`_zuc_run_32` calls `_lfsr_with_work_mode(state)` → `_lfsr_shift(s, new_s)`.
The 2-level indirection for in-place array mutation: if `_lfsr_shift` receives
`s` by value (copy), the shift never propagates back to `state` in the caller.
ChaCha20 passes arrays 1-level deep and works. This is the prime suspect.

**Test:** Inline `_lfsr_shift` body directly into `_lfsr_with_work_mode` —
if z[0] != z[1] after inlining, this is confirmed.

### H2: LFSR feedback polynomial has sign errors
The polynomial `_lfsr_feedback` uses `(s15 << 15) + (s13 << 17) + ...` on u32
values widened to u64. The `<<` shifts are fine. But `(s0 << 8) + s0` should
equal `(2^8 + 1) * s0`. Verify: `(0x000000FF << 8) + 0x000000FF = 0x0000FFFF`.
This is correct. However: if any cell `s[n]` read from `[u32]` fn-param array
via `s[n].to_u64()` produces wrong u64 widening, the feedback sum is wrong.

### H3: d_i constant indexing off-by-one
`_d_const(i)` for i=0..15. `_zuc_load_state` uses `while i < 16` with
`_d_const(i)`. If the interpreter evaluates `i == 0u64` comparisons differently
than expected (e.g., u64 literal comparison bug), wrong d constants could load.

### H4: LFSR cell bit layout wrong
`val si = (ki << 23) | (di << 8) | ivi` — `ki` is bits [30:23] (8 bits),
`di` is bits [22:8] (15 bits), `ivi` is bits [7:0] (8 bits).
Total: 8+15+8 = 31 bits. This matches TS 35.221 §3.3. However, `di & 0x7FFFu32`
should mask to 15 bits — verify `_d_const(0) = 0x44D7 = 17623` which needs 15
bits. `0x44D7 & 0x7FFF = 0x44D7` (fits). Likely correct.

## Next Diagnostic (for a future fix attempt)

Inline `_lfsr_shift` into `_lfsr_with_work_mode` and `_lfsr_with_init_mode` to
test H1. If z[0] != z[1] after inlining, the 2-level array mutation is the cause.

```simple
# Replace _lfsr_with_work_mode body with:
fn _lfsr_with_work_mode(s: [u32]):
    val fb = _lfsr_feedback(s)
    var new_s = _mod31(fb)
    if new_s == 0u32:
        new_s = 0x7FFFFFFFu32
    # Inline _lfsr_shift here instead of calling it:
    var i: u64 = 0
    while i < 15:
        s[i] = s[i + 1u64]
        i = i + 1
    s[15] = new_s
```

## Blocked On

- 2-attempt budget exhausted per task rules
- Root cause not yet isolated without native-mode testing or deeper interpreter
  instrumentation

## Files

- `src/os/crypto/zuc.spl` — implementation (algorithm correct per TS 35.221)
- `test/unit/os/crypto/zuc_kat_spec.spl` — KAT spec (5 failing, 3 passing)

## Cross-references

- `doc/08_tracking/bug/u64_right_shift_fn_param_arithmetic_2026-05-02.md`
- `.claude/memory/feedback_it_block_var_mutation.md`
- `src/os/crypto/sha384.spl:140` — `_logical_shr64` pattern reference

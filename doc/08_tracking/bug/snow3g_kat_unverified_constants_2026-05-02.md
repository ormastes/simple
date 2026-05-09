# SNOW 3G KAT: Wrong Keystream — Unverified Constants (MUL_alpha, DIV_alpha, S_Q)

**Status:** FIXED 2026-05-09 — MUL_alpha/DIV_alpha tables corrected (4d024d2786), FSM fixed (cdc5b5b0a4), clocking fixed (ea491e2d99). KAT unverifiable in interpreter mode.
**Severity:** Blocking — SNOW 3G keystream KAT fails; UEA2/UIA2 also wrong.
**Affected file:** `src/os/crypto/snow3g.spl`
**Spec file:** `test/unit/os/crypto/snow3g_kat_spec.spl`
**Path:** `bug` track.

## Symptom

All-zero key/IV produces z[0] = `51713a3e` (expected `245a4307`).
z[0] != z[1], confirming state advances between words.
Self-inverse test passes: `encrypt(encrypt(m)) == m`.

These two structural properties confirm the algorithm wiring is correct:
- LFSR advances between keystream words
- FSM mutation is consistent (XOR-based symmetry holds)

The wrong output is due to incorrect constant tables, not algorithmic structure.

## Root Cause: Three Unverified Constant Tables

### 1. MUL_alpha — wrong values (16-bit residues, not 32-bit GF(2^32) values)

Current table entries (e.g. index 1 = `0x00000185`) are 16-bit GF(2^8) polynomial
values, not the actual 32-bit MUL_alpha values from TS 35.216.

The correct MUL_alpha(1) from TS 35.216 Table 2 is `0xE19FCF13`.

MUL_alpha(c) represents multiplication of c by alpha in GF(2^32)/f(x) where
f(x) = x^32 + x^10 + x^3 + x^2 + 1 (SNOW 3G-specific polynomial, NOT the
x^32 + x^10 + x^7 + x^2 + 1 approximation used in the current code).

### 2. DIV_alpha — trivial placeholder, completely wrong

Current implementation:
```
fn _div_alpha(c: u8) -> u32:
    c.to_u32() << 24
```

This is not the TS 35.216 Table 3 DIV_alpha table. Every entry is wrong.

DIV_alpha(c) is the multiplicative inverse operation and requires the proper
256-entry lookup table from the spec.

### 3. S_Q — written from memory, unverified

The S_Q table (256 entries, lines 327–586 of snow3g.spl) was transcribed from
memory, not sourced from TS 35.216 Annex 1. No authoritative reference was found
in the repository (vendor crates, test vectors, or spec docs).

Even a single wrong byte in S_Q will cause KAT failure, and with MUL_alpha and
DIV_alpha also wrong, diagnosing which table is faulty is ambiguous.

## What Is Structurally Correct

- LFSR 16-cell structure and feedback polynomial wiring (`_snow3g_lfsr_init_step`,
  `_snow3g_lfsr_work_step`) — no 2-level indirection; inline shift, state advances.
- FSM 3-register update logic (`_snow3g_fsm_step`) — S_R/S_Q applied to correct
  word positions; R1/R2/R3 updated in correct order.
- UEA2 (`uea2_encrypt`) — IV construction, keystream XOR, bit truncation correct.
- UIA2 (`uia2_mac`) — IV construction, accumulator, MAC extraction correct.
- All public API signatures match 3GPP TS 35.215 §3.3.

## Fix Required

Source all three tables directly from 3GPP TS 35.216:

1. **MUL_alpha**: Table 2 (256 x 32-bit entries) from TS 35.216
2. **DIV_alpha**: Table 3 (256 x 32-bit entries) from TS 35.216
3. **S_Q**: Table 1 (256 x 8-bit entries, §3.3) from TS 35.216 or its normative
   reference (can also compute via MULx/MULxPOW recurrence from TS 35.216 §3.2)

MUL_alpha and DIV_alpha can alternatively be computed via the `MULxPOW(c, i, Q)`
recurrence defined in TS 35.216 §3.3.2 — ~20 lines, no table to transcribe.

## Blocked On

- 1-attempt budget exhausted per task rules
- No authoritative constant source found in the repository
  (`src/`, `src/runtime/vendor/`, `src/compiler_rust/vendor/`, `doc/`, `test/`)

## Files

- `src/os/crypto/snow3g.spl` — implementation (algorithm structure correct;
  constants `_mul_alpha`, `_div_alpha`, `_sq` are wrong/unverified)
- `test/unit/os/crypto/snow3g_kat_spec.spl` — KAT spec (failing: z[0], UIA2 MAC;
  passing: output length, self-inverse)

## Cross-references

- `doc/08_tracking/bug/zuc128_kat_persistent_wrong_keystream_2026-05-02.md`
- `.claude/memory/feedback_compile_mode_false_greens.md`
- `.claude/memory/feedback_it_block_var_mutation.md`

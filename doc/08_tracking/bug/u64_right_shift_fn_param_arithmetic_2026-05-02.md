# `u64 >>` on a fn parameter performs arithmetic (sign-extending) shift

**Status:** OPEN. Discovered 2026-05-02 while debugging `sha384_kat_failure_2026-05-02.md`.
**Severity:** silent miscompute; affects every pure-Simple module that takes
a `u64` value through a fn parameter and right-shifts it where the high bit
may be set. SHA-512 family / arbitrary-precision / fixed-point u64 arithmetic
are all candidate victims.
**Path:** `bug` track.

## Symptom — minimal repro

```simple
fn _shr_param(x: u64, n: u64) -> u64:
    x >> n

fn _shr_local() -> u64:
    val x: u64 = 0xCBBB9D5DC1059ED8
    x >> 28
```

In the interpreter:

- `_shr_local()` returns `0xCBBB9D5DC` (logical, correct).
- `_shr_param(0xCBBB9D5DC1059ED8, 28)` returns `0xFFFFFFFCBBB9D5DC`
  (arithmetic / sign-extending — wrong).

Same `>>` token, two different code paths. The standalone `val`-bound case
takes a logical-shift code path; the fn-parameter case takes an arithmetic
path that sign-extends from the high bit when bit 63 of `x` is set.

`<<` does NOT exhibit this bug. `_u64_mask(x << n)` produces correct
truncated-to-u64 results for both `val`-bound and fn-parameter operands.

## Localization

The bug is in interpreter dispatch for `>>` on u64 values that arrived via
fn parameter. `val x: u64 = ...` and `let _ = h[i]` paths preserve u64
semantics. Likely cause: fn-param u64 storage uses i64-backed cells and
`>>` dispatches arithmetic shift for i64. The result then propagates
unmasked into XOR / OR chains where `_u64_mask` at the outer level cannot
recover the lost high bits.

## Reproduction in production code

`src/os/crypto/sha384.spl` rotr/sigma helpers exhibit the bug. Before fix
(commit 2a09ef1164):

```simple
fn _rotr64_384(x: u64, n: u64) -> u64:
    _u64_mask((x >> n) | _u64_mask(x << (64 - n)))
```

For `x = 0xCBBB9D5DC1059ED8, n = 28`:

- canonical:        `0x1059ed8cbbb9d5dc`
- got from fn:      `0xFFFFFFFCBBB9D5DC`

`big_sigma0(SHA-384 h[0]) = 0xdb9a810738c045b1` canonical, but Simple
interpreter returned `0xfffffffcb6c045b1` because each ROTR^28/34/39 sign-
extended into the high bits, then XOR'd together still left the top
bits stuck at 1.

This caused `SHA-384("")` to silently miscompute, breaking FIPS 180-4 KAT.

## Workaround applied

Added `_logical_shr64(x: u64, n: u64) -> u64` to `src/os/crypto/sha384.spl`
which masks the sign-extended bits explicitly:

```simple
fn _logical_shr64(x: u64, n: u64) -> u64:
    val mask: u64 = _u64_mask((1 << (64 - n)) - 1)
    (x >> n) & mask
```

Replaced every `(x >> n)` in `_rotr64_384`, `_small_sigma0_384`, and
`_small_sigma1_384` with `_logical_shr64(x, n)`.

Verified post-fix:

- `_logical_shr64(0xCBBB9D5DC1059ED8, 28)` = `0xCBBB9D5DC` (correct)
- `big_sigma0(0xCBBB9D5DC1059ED8)` = `0xdb9a810738c045b1` (correct)
- `SHA-384("")` matches FIPS 180-4 §D.1 (KAT 6/6 pass)
- `SHA-512("")` and `SHA-512("abc")` match FIPS 180-4 §D.1/§D.2 via
  `_sha384_sha512_emulate` (KAT 3/3 pass — regression baseline)

## Audit candidates (not yet checked)

These modules use u64 arithmetic and may exhibit the same silent miscompute:

- `src/lib/common/crypto/sha512.spl` — uses `i64`/`list` throughout, so
  high-bit masking happens via existing AND-masks; likely benign but worth
  KAT verification.
- Any pure-Simple wide-integer / bignum module taking u64 fn args.
- `src/lib/common/crypto/sha3.spl` — Keccak rotations use 64-bit lanes;
  if any helper rotates via `>>` on a fn-param u64, audit needed.
- Any module that passes u64 `mask >> n` patterns through fn helpers.

## Out of scope for the spot fix

- A real interpreter fix (make `>>` on u64 fn params dispatch logical shift
  by checking the operand's declared type, not its storage cell).
- Auditing every pure-Simple consumer of u64 shifts. The fix above only
  covers `os.crypto.sha384`. Other modules may still be silently wrong.

## Cross-references

- `doc/08_tracking/bug/sha384_kat_failure_2026-05-02.md` — the failing
  KAT that exposed this bug.
- `test/unit/os/crypto/sha384_kat_spec.spl` — KAT spec, includes a
  `_sha384_diag_big_sigma0_h0` regression guard that fails if this bug
  comes back in `_logical_shr64`.
- `test/unit/os/crypto/sha512_kat_spec.spl` — added 2026-05-02; verifies
  the shared compression chain in `_sha384_process_block` against
  FIPS 180-4 §D.1/§D.2 SHA-512 vectors via `_sha384_sha512_emulate`.
- `src/os/crypto/sha384.spl:140` — the `_logical_shr64` helper.

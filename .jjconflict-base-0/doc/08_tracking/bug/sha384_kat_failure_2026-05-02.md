# SHA-384 produces wrong output — KAT 2/6 fail on FIPS 180-4 vectors

**Status:** FIXED 2026-05-02 (W16-B-FIX). Root cause was an interpreter bug
in u64 right-shift on fn parameters, NOT in the SHA-384 algorithm itself.
See `doc/08_tracking/bug/u64_right_shift_fn_param_arithmetic_2026-05-02.md`
for the underlying compiler bug. Spot fix landed in `src/os/crypto/sha384.spl`
via the `_logical_shr64` helper. Both `sha384_kat_spec.spl` and the new
`sha512_kat_spec.spl` (regression baseline for the shared compression chain)
PASS in interpreter mode.

**Root cause diagnosis:** `(x >> n)` where `x` is a `u64` fn parameter and
bit 63 of `x` is set sign-extends 1-bits into the high positions, producing
arithmetic shift behavior. `_rotr64_384(x, n)` uses `(x >> n) | (x << (64-n))`,
and the high bits of `(x >> n)` arrived corrupted — `_u64_mask` on the OR'd
result couldn't recover them because the sign-extended bits were already in
the kept-bits range. `big_sigma0(0xCBBB9D5DC1059ED8)` returned
`0xfffffffcb6c045b1` instead of canonical `0xdb9a810738c045b1`.

`val`-bound u64 shifts work correctly (logical). SHA-256 family (`u32`
parameters) and `src/lib/common/crypto/sha512.spl` (uses `i64` with explicit
masking) escape the bug.

**Status before fix:** OPEN. Discovered 2026-05-02 by W16-B follow-up audit.
**Severity:** silent miscompute; affects any caller that uses `os.crypto.sha384`.
Blocks W14-E `rsa_pss_rsae_sha384` sigalg variant.
**Path:** `bug` track.

## Symptom

`bin/simple test test/unit/os/crypto/sha384_kat_spec.spl` — 2 of 6 fail:

- `SHA-384("")` →
  got `da1bad3c8f339d423b962d8ab4df0415533e73820edce36e22ba624082d1b128f8035623d4e4e2950685e5eabce5a749`,
  expected `38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b` (FIPS 180-4 §D.1).
- `SHA-384("abc")` →
  got `60f693c033f8ce2f0581d465badf2b659e52924de5da18d1097d793cded8c3cefffbd9f15641c535849ffed538265574`,
  expected `cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7` (FIPS 180-4 §D.2).

Wrong outputs do NOT match SHA-512("")=`cf83e1357eefb8bd...` or SHA-512("abc")=`ddaf35a193617aba...`,
so this is not a "wrong IV" or "didn't truncate" symptom — the entire compression
chain produces different bytes from FIPS 180-4 reference.

Sibling `os.crypto.sha224` PASSES 3/3 KAT, so SHA-256 family is sound; the bug
is localized to the SHA-512 family code (which SHA-384 depends on).

## Localization

- `src/os/crypto/sha384.spl:117-127` IV constants — verified against FIPS 180-4 §5.3.4 Table; **correct**.
- `src/os/crypto/sha384.spl:140-159` sigma + rotation helpers — visually correct, all `_u64_mask`'d; needs runtime probe.
- `src/os/crypto/sha384.spl:31-...` K constants — first two verified visually correct; full 80-entry table not audited.
- `src/os/crypto/sha384.spl:215-...` `_sha384_process_block` — round structure looks correct.
- No `test/unit/os/crypto/sha512*spec*` exists — cannot baseline whether SHA-512 itself
  is broken or only SHA-384's call into it.

## Reproduction

```bash
bin/simple test test/unit/os/crypto/sha384_kat_spec.spl
```

Spec is at `test/unit/os/crypto/sha384_kat_spec.spl`. Already references FIPS 180-4
vectors correctly (verified against the standard).

## First steps for fix agent

1. **Add SHA-512 KAT spec** — `test/unit/os/crypto/sha512_kat_spec.spl` with FIPS 180-4
   §D.1/§D.2 vectors:
   - `SHA-512("")` = `cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e`
   - `SHA-512("abc")` = `ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f`
2. If SHA-512 also fails: bug is in shared compression chain (`_sha384_process_block`,
   sigma helpers, padding, big-endian unpack at end). Likely places:
   - K constants typo (rare but possible — full audit of all 80 entries)
   - sigma rotation count (e.g. should be 28/34/39 for big_sigma0; 14/18/41 for big_sigma1)
   - small_sigma rotation count (1/8 + shift 7; 19/61 + shift 6)
   - byte-unpack at finalization (8 bytes per u64, MSB first)
3. If SHA-512 PASSES: bug is in SHA-384's IV use or output truncation
   (`sha384` should output first 6 of 8 u64 words = first 48 bytes).

## Out of scope

- SHA-224 (passes 3/3 KAT, separate code path).
- SHA-512 interpreter dispatch FR (`sha512_interpreter_dispatch.md`,
  W14-D blocker) — that's about Rust runtime extern; this bug is in the
  pure-Simple `_sha384_process_block` chain.

## Cross-references

- `src/os/crypto/sha384.spl` — buggy module.
- `src/os/crypto/sha224.spl` — sibling, works correctly (regression baseline).
- `test/unit/os/crypto/sha384_kat_spec.spl` — failing spec (correct vectors).
- `doc/02_requirements/feature/sha512_interpreter_dispatch.md` — W14-D's blocker FR; orthogonal but related.
- W14-E `4a55937ef5` filed `rsa_pss_sha384_sign` deferred pending `os.crypto.sha384`;
  this bug blocks that variant.

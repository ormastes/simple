# Feature Request: Pure-Simple RSA modexp interpreter perf cliff

### FR-CRYPTO-0001 — RSA-2048 modexp completes within interpreter test budget

- **Filed-on:** 2026-05-02
- **Filed-by:** W14-E (RSA-PSS sign/verify wave)
- **Target:** crypto / interpreter perf
- **Priority:** P1
- **Update 2026-05-30:** evaluated and rejected the next small pure-Simple
  PSS bigint micro-optimization. Current `HEAD` already contains the prior
  safe hot-path speedups in `src/os/crypto/rsa_pss.spl` (`_pss_bi_normalize`
  avoids copying already-normalized limb lists, `_pss_bi_get_bit` uses the
  same direct limb-mask extraction shape as `rsa_fallback.spl`,
  `_pss_bi_shift_left_one` returns zero without allocation, and
  `_pss_bi_mod_exp` avoids an unused reduced base). An attempted additional
  `_pss_bi_mul` zero/one short-circuit was correct but regressed the focused
  KAT to 10390ms reported spec time, so it was reverted and no source diff was
  kept. Focused evidence:
  `SIMPLE_LIB=src bin/simple check src/os/crypto/rsa_pss.spl src/os/crypto/rsa_fallback.spl test/01_unit/lib/crypto/rsa_pss_sha256_kat_spec.spl test/01_unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl`
  passed; `SIMPLE_LIB=src bin/simple test test/01_unit/lib/crypto/rsa_pss_sha256_kat_spec.spl --mode=interpreter --clean --fail-fast`
  passed at 2302ms reported spec time after reverting the rejected slice;
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/crypto/rsa_pss_smoke_spec.spl --mode=interpreter --clean --fail-fast`
  passed; `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/rsa_contract_parity_spec.spl --mode=interpreter --clean --fail-fast`
  passed. This does not close FR-CRYPTO-0001: the explicit RSA-2048 command
  `timeout 60s env SIMPLE_LIB=src bin/simple test --only-slow test/01_unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl --mode=interpreter --clean --fail-fast`
  still timed out, and `test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl` still
  reports 9 passed / 1 failed under the focused interpreter command with no
  assertion detail in runner output. Remaining work is still a correct
  Montgomery/Barrett reducer or shared runtime-independent bigint modexp.
- **Status:** PARTIAL 2026-05-30 — safe pure-Simple speedups landed, but the
  RSA-2048 interpreter acceptance budget is still not met. `rsa_pss.spl` now
  parses CRT private-key fields and signs via two half-size CRT modexps when
  PKCS#8 includes `p`, `q`, `dP`, `dQ`, and `qInv`; both `rsa_pss.spl` and
  `rsa_fallback.spl` use a 4-bit MSB-first sliding-window exponent loop, and
  `rsa_fallback._bi_mod` uses the shifted-modulus reducer shape already used
  by PSS instead of rebuilding the remainder bit-by-bit. Verification:
  `SIMPLE_LIB=src bin/simple check src/os/crypto/rsa_pss.spl src/os/crypto/rsa_fallback.spl test/01_unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl`,
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/crypto/rsa_pss_sha256_kat_spec.spl --mode=interpreter --clean --fail-fast`,
  and
  `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/rsa_contract_parity_spec.spl --mode=interpreter --clean --fail-fast`
  passed. The explicit acceptance command
  `timeout 60s env SIMPLE_LIB=src bin/simple test --only-slow test/01_unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl --mode=interpreter --clean --fail-fast`
  still timed out, so the remaining work is a correct Montgomery/Barrett
  reducer or shared runtime-independent bigint modexp. A temporary Montgomery
  REDC experiment completed the PKCS#1 interpreter spec in ~37s but produced
  invalid signatures, so it was not kept.

  Prior partial status from 2026-05-10: `rt_bigint_mod_exp` extern declared in
  `src/lib/nogc_sync_mut/io/signature_sffi.spl` (runtime-accelerated path stub
  exists); however `src/lib/common/math/bignum/` does NOT exist and no
  sliding-window pure-Simple `mod_exp` was written. The status note in the
  original entry was inaccurate: `bignat.spl` was never created and the
  acceptance-criteria specs are unverified. Also note: the file referenced in
  the original status (`signature_ffi.spl`) does not contain the extern — it is
  in `signature_sffi.spl`.
  - **Remaining work:** implement a correct fast pure-Simple modular reducer
    (Montgomery or Barrett) for the existing 30-bit-limb representation, wire
    both RSA modules through it or extract shared bignum code, and verify both
    acceptance-criteria specs pass in interpreter mode within 60s.
- **Requested-semantics:**
  Pure-Simple `_pss_bi_mod_exp` against a 2048-bit modulus and 2048-bit
  exponent runs O(bits^3) with the current schoolbook `_pss_bi_mod` doing
  one shift+subtract per bit per modexp round. In the SPipe interpreter
  this exceeds the 60s watchdog for a single sign/verify call. The
  existing `rsa_fallback._bi_mod_exp` has the same shape and is the
  reason `rsa_pkcs1_v15_spec.spl` routes through the FFI hosted backend
  (`RsaSignBackend.HostedReference`) rather than the pure-Simple fallback.

  Need either:
  - A faster pure-Simple modexp (Montgomery / Barrett / sliding-window),
    or
  - A `rt_*` extern surface (e.g. `rt_bigint_mod_exp(base_bytes,
    exp_bytes, mod_bytes) -> [u8]`) that lets `os.crypto.rsa_pss` and
    `os.crypto.rsa_fallback` share a fast modexp without pulling in
    full-featured RSA FFI.

- **Acceptance-criteria:**
  - [ ] `test/01_unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl`
        round-trip cases run to completion under interpreter mode within
        the default 60s watchdog (RSA-2048).
  - [ ] `test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl` can route via the
        PureSimple backend in interpreter mode (today only HostedReference
        works fast enough).
  - [ ] No new dependency on the embedded-host shortcut (`rt_embedded_host_rsa_component`).

- **Related-upfront:**
  `.claude/memory/feedback_interpreter_test_limits.md`,
  `.claude/memory/feedback_compile_mode_false_greens.md`.

- **Related-design-doc:** tbd

- **Related-issue:** none

- **Notes:**
  Symptom captured: `rsa_pss_sha256_sign(pkcs8_2048, msg, salt)` times
  out at 60s in interpreter mode after the DER parsers and EMSA-PSS
  encoder return promptly. Square-and-multiply MSB-first inner loop
  fires `_pss_bi_mod` ~2*2048 times, each doing up to 2048 bit-shift +
  subtract operations on 30-bit-limb lists; that is the cliff.

  W14-E ships the RFC 8017 PSS primitives correctly (DER parsers + smoke
  spec pass; logic matches RFC 8017 §9.1 EMSA-PSS-ENCODE/VERIFY and
  §B.2.1 MGF1) but cannot ship a 2048-bit interpreter-mode KAT round-trip
  until this is fixed. Compiled-mode coverage requires R2-broader
  (`feedback_compile_mode_false_greens.md`).

  Once compile-mode test execution is reliable, this FR may be
  downgradable; for now it blocks pure-Simple TLS 1.3 sigalg coverage
  for `rsa_pss_rsae_*` in the SPipe interpreter lane.

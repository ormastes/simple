# Feature Request: Pure-Simple RSA modexp interpreter perf cliff

### FR-CRYPTO-0001 — RSA-2048 modexp completes within interpreter test budget

- **Filed-on:** 2026-05-02
- **Filed-by:** W14-E (RSA-PSS sign/verify wave)
- **Target:** crypto / interpreter perf
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Pure-Simple `_pss_bi_mod_exp` against a 2048-bit modulus and 2048-bit
  exponent runs O(bits^3) with the current schoolbook `_pss_bi_mod` doing
  one shift+subtract per bit per modexp round. In the SSpec interpreter
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
  - [ ] `test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl`
        round-trip cases run to completion under interpreter mode within
        the default 60s watchdog (RSA-2048).
  - [ ] `test/unit/lib/crypto/rsa_pkcs1_v15_spec.spl` can route via the
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
  for `rsa_pss_rsae_*` in the SSpec interpreter lane.

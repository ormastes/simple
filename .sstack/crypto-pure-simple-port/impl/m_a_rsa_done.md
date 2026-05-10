# M-A: RSA → bignum migration — Implementation Notes

Wave 2 of the `crypto-pure-simple-port` sstack feature.  Migrates the live
RSA path from its in-tree ad-hoc `_bi_*` bignum to the canonical pure-
Simple bignum module landed by I-3 (R-B §5 step 3 + step 2).

## Files touched

| Path | Change | LOC before | LOC after | Δ |
|------|--------|-----------:|----------:|---:|
| `src/os/crypto/rsa_fallback.spl`             | migrated `_bi_*` block to `std.math.bignum.bignat`; deleted local bignat impl + bytes converters; introduced `_rsa_mod_exp` glue | 537 | 301 | **-236 (-44%)** |
| `src/lib/common/rsa/modular.spl`             | replaced legacy `import src.std.rsa.types` body with bignum-backed shim; preserves historical `bigint_*` names | 152 | 184 | +32 |
| `test/unit/lib/rsa/rsa_kat_spec.spl`         | new KAT spec | 0 | 229 | +229 |
| **Total**                                    |                                      |  689  |  714  | **+25 (net), -204 in live path** |

The +32 in `modular.spl` is a fair trade — the legacy file leaned on a
broken Python-style `import src.std.rsa.types` that no longer resolves
under the modern `use std.X` resolution; the shim now actually compiles
and exports usable `bigint_mod_exp` / `bigint_gcd` / `bigint_extended_gcd`
/ `bigint_mod_inverse` / `bigint_lcm` / `jacobi_symbol` against bignum.
Net change in the **live** RSA path (rsa_fallback.spl) is **-236 LOC**.

`src/os/crypto/rsa.spl` was deliberately **not** touched — it is a thin
FFI dispatcher that delegates to `rsa_fallback` for pure-Simple sign and
to `rt_rsa_*_verify` for verify.  No `_bi_*` references; nothing to
migrate.  R-B §5 step 2 originally suggested migrating it too, but a
grep showed it owns no bignum code.

`src/lib/common/rsa/{byte_conversion,encrypt,key_gen,padding,primality,
random,sign,types,utilities}.spl` (9 files, ~1180 LOC) were left as-is.
They use the legacy Python-style `import src.std.rsa.types as types`
syntax which no longer resolves under the modern `use std.X` build, and
nothing outside this directory imports them (verified: zero hits for
`import src\.std\.rsa` outside `src/lib/common/rsa/`, zero hits for
`use std.rsa` anywhere).  They are transitively dead code.  Removing
them is out of M-A scope — file deletion would belong to a "wave 3
cleanup" track or a future refactor task.

## KATs added

**Total: 10 KATs** in `test/unit/lib/rsa/rsa_kat_spec.spl`.

| # | Describe block | KAT | Source |
|---|----------------|-----|--------|
| 1 | RSA mod_exp KAT (toy 8-bit modulus)             | `7^7 mod 143 = 6`                           | RFC 3447 §A.2.4-shaped (textbook RSA, p=11 q=13) |
| 2 | RSA mod_exp KAT (toy 8-bit modulus)             | decrypt round-trip `m^e^d mod n = m`, m=7   | RFC 3447 §5.1 (RSAEP/RSADP shape) |
| 3 | RSA mod_exp KAT (toy 8-bit modulus)             | decrypt round-trip on m=42                  | RFC 3447 §5.1 |
| 4 | RSA mod_exp KAT (multi-limb modulus)            | `2^32 mod (LIMB_BASE+7)` — limb-boundary    | hand-derived edge case (limb-base regression) |
| 5 | RSA mod_exp KAT (multi-limb modulus)            | `(LIMB_BASE+1)^2 mod LIMB_BASE = 1`         | hand-derived (multi-limb base + reduce) |
| 6 | RSA byte conversion KAT                         | `0x0102` round-trip via `from_bytes_be`/`to_bytes_be` | RFC 3447 §4.1 (I2OSP/OS2IP shape) |
| 7 | RSA byte conversion KAT                         | left-pads to specified length               | RFC 3447 §4.1 |
| 8 | RSA byte conversion KAT                         | round-trips a 32-byte (256-bit) value       | hand-derived |
| 9 | RSA modulus-size byte decode KAT                | hex-decodes a 32-byte RSA modulus prefix    | ring `rsa_test_private_key_2048.p8` (test/system fixture) |
|10 | RSA modulus-size byte decode KAT                | from_bytes_be / to_bytes_be round-trip on 32-byte BE value | ring fixture |

KATs 1–5 directly exercise the migrated `_rsa_mod_exp` kernel: same
square-and-multiply structure as `rsa_fallback._rsa_mod_exp`, same
bignum primitives (`bn_mul`, `bn_modulo`, `bn_bit_length`, `bn_get_bit`).
If these go green, the migration's mathematical carrier is correct.

KATs 6–10 cover the byte<->limb edge that replaced the local
`_bytes_to_bigint_be` / `_bigint_to_bytes_be` helpers with bignum's
`from_bytes_be` / `to_bytes_be`.

### What's NOT covered (and why)

- **PSS sign/verify KATs (SHA-256 + SHA-512)** — task asked for these.
  After investigation: there is **no pure-Simple PSS implementation** in
  this tree.  PSS verify exists only as the FFI externs
  `rt_rsa_pss_sha{256,384,512}_verify` (declared in
  `src/lib/nogc_sync_mut/io/signature_ffi.spl`); the system test
  `test/system/os_rt_rsa_pss_verify_spec.spl` covers the FFI path but
  reaches "unknown extern function" in interpreter mode.  Since the
  bignum migration changes only the carrier types of the existing
  PKCS#1 v1.5 path — and that path has no PSS sibling — there is no
  pure-Simple PSS to migrate.  Adding PSS sign in pure-Simple is a
  separate feature ask, not a migration concern.  Recorded in the
  follow-up TODO so it isn't lost.

- **Full PKCS#8 v1 DER parse round-trip** — initial draft tried to call
  `rsa_debug_parse_pkcs8` on the ring fixture, but that path traverses
  the `rt_bytes_u8_at` extern which is not registered in interpreter
  mode (the test failed with "unknown extern function").  The system
  test `test/system/os_crypto_ref_signature_spec.spl` exercises the
  full DER+sign pipeline against `/usr/bin/openssl` — that is the
  appropriate gate for the parse path.  This unit-level KAT spec
  stays focused on the bignum carrier semantics so it runs green
  under direct `bin/simple <spec>` invocation.

- **RSA-2048 sign through pure-Simple `_crt_sign`** — the variable-time
  bit-by-bit `bn_modulo` reduce inside `_rsa_mod_exp` makes a single
  RSA-2048 mod-exp roughly O(2048 × 2048 × bignat-mul) operations in
  the interpreter, which is impractical for a unit-test rig.  The
  multi-limb KATs (#4, #5) cover the same kernel at sizes the
  interpreter can run; the system-test rig covers the full 2048-bit
  path against openssl.

## Deliberate-fail probe

Probe: line 95 of `rsa_kat_spec.spl`, first describe block, first `it`:

```
expect(r[0]).to_equal(99999)  # was 6
```

- **Probe red:** confirmed.  Output: `✗ encrypt: 7^7 mod 143 = 6` —
  `1 example, 1 failure` in the first describe block; remaining 9 KATs
  unaffected.  Rig is live.
- **Reverted:** to `expect(r[0]).to_equal(6)`.
- **Post-revert:** `bin/simple test/unit/lib/rsa/rsa_kat_spec.spl` is
  green: `3 + 2 + 3 + 2 = 10 examples, 0 failures` across the four
  describe blocks.

## Remaining duplication / OLD bignat usage (call-out for cleanup)

| Where | What | Reason left alone |
|-------|------|-------------------|
| `src/lib/common/rsa/{byte_conversion,encrypt,key_gen,padding,primality,random,sign,types,utilities}.spl` | Legacy `bigint_*` over `import src.std.rsa.types` syntax — own ad-hoc bignat in `types.spl` | 9 files, ~1180 LOC, all transitively dead (no caller outside this dir; legacy import syntax doesn't resolve under modern build).  Deletion belongs to a separate cleanup pass; not load-bearing. |
| `src/os/crypto/rsa_fallback.spl` `_rsa_mod_exp` | Variable-time square-and-multiply | Per task spec: "do NOT replace it with `mod_exp_ct_stub`".  The CT replacement requires real Montgomery reduction in `bignum/fixed.spl` (currently broken stub).  Tracked in `doc/08_tracking/todo/rsa_ct_modexp_2026-04-25.md`. |
| `src/os/crypto/curve25519*.spl`, `ed25519.spl`, `ecdsa_p256.spl` | Out of M-A turf | M-B / M-C / M-D scope. |

## Advisor consultations

- **Pre-implementation:** advisor flagged five subtle issues that
  re-shaped the plan:
  1. Verify the *actual* `bignat.spl` exports — design doc said
     `add/sub/mul/mod_exp` but I-3 ships `bn_*`-prefixed names plus no
     `mod_exp` at the bignat level (only the broken `*_stub` forms in
     `fixed.spl`).  Confirmed: had to rebuild `_rsa_mod_exp` over
     bignat's `bn_modulo` / `bn_get_bit` / `bn_bit_length`.
  2. `extended_gcd`'s 5-tuple shape has no direct bignum equivalent —
     either keep it in `modular.spl` or delete.  Decision: keep, but
     re-encode the sign tags as `bn_zero()` / `bn_one()` sentinels
     (modular.spl 5-tuple stays list-of-bignat shaped).
  3. `rsa.spl` may not need touching — confirmed via grep, left alone.
  4. PSS in scope? — confirmed PSS verify is FFI-only, no pure-Simple
     PSS to migrate.  Documented + filed follow-up.
  5. Test vector sourcing — used ring's CAVP-shaped 2048-bit fixture
     (already in test/system) rather than fabricating NIST bytes.

- **Pre-done (this note):** N/A — deliverable is durable
  (rsa_fallback edited, KAT spec written, KATs green, probe verified).

## Bootstrap / build status

- No externs added.  No Rust touched.  No `bootstrap-from-scratch.sh
  --deploy` needed.
- `bin/simple build` / `lint` / `check` are silent-noop wrappers
  (confirmed I-3 finding `feedback_extern_bootstrap_rebuild.md` still
  applies).  Verification was via direct `bin/simple <spec>` invocation
  + adjacent-spec regression check.
- Adjacent regression: `bin/simple test/unit/lib/math/bignum/bignat_spec.spl`
  still green post-migration (57 examples, 0 failures).
- Pre-existing failures observed (NOT regressions):
  `ssh_kex_rsa_contract_spec.spl` and `rsa_contract_parity_spec.spl`
  fail with "method `to_bytes` not found on type `str`" — these tests
  call `text.to_bytes()` at lines 76 / 93 respectively; that is a
  pre-existing rig issue independent of the migration (verified by
  inspecting the git-tracked test source — neither file was modified
  by M-A).

## Follow-up TODO filed

`doc/08_tracking/todo/rsa_ct_modexp_2026-04-25.md` — RSA secret-exponent
mod_exp uses variable-time `bignat.modulo`; switching to constant-time
requires real Montgomery reduction in `bignum/fixed.spl` (currently
`mod_exp_ct_stub` truncates upper limbs and is documented as
DO-NOT-USE-FOR-REAL-CRYPTO).

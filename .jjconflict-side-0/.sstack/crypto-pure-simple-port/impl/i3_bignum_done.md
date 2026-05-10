# I-3: Bignum Scaffold — Implementation Notes

**Track:** `crypto-pure-simple-port` / I-3 (bignum scaffold)
**Author:** I-3 (parallel SStack implementation fan-out)
**Date:** 2026-04-25
**Status:** Landed locally; tests green.
**Spec source:** `.sstack/crypto-pure-simple-port/research/bignum_design.md` (R-B)

## Files written

| Path | Lines | Purpose |
|------|-------|---------|
| `src/lib/common/math/bignum/limb.spl`           | 101 | Limb constants, single-limb helpers, `add_limbs` / `sub_limbs` / `mul_limbs` (60-bit i64 product, no `mul_hi` libcall). 6 fns. |
| `src/lib/common/math/bignum/bignat.spl`         | 397 | Variable-length BigNat: constructors, predicates, `cmp`, `normalize`, `bit_length`, `get_bit`, `shift_left_one`, `add`, `sub`, `mul`, `mul_i64`, `div_mod`, `modulo`, `from_bytes_be/le`, `to_bytes_be/le`. 20 fns. |
| `src/lib/common/math/bignum/fixed.spl`          | 407 | `Fixed` struct + CT helpers: `add_fixed`, `sub_fixed`, `mul_fixed` (full-width 2N), `cond_swap`, `cond_select`, `is_zero_ct`, `cmp_fixed`, `mod_reduce_ct`. STUBS (documented, name-suffixed): `mod_exp_ct_stub`, `mod_inv_ct_stub`. 18 fns + 1 struct. |
| `src/lib/common/math/bignum/mod.spl`            |  19 | Public re-export hub. |
| `test/unit/lib/math/bignum/limb_spike_spec.spl` |  29 | Spike: 3 KAT tests on limb primitives. |
| `test/unit/lib/math/bignum/bignat_spec.spl`     | 260 | 33 KAT tests covering constants, predicates, normalize, add/sub carry chains, mul, shift, bit access, div_mod, byte encoding round-trips. |
| `test/unit/lib/math/bignum/fixed_spec.spl`      | 202 | 21 CT tests: constructors, add/sub carry, cond_swap (incl. double-swap round-trip), cond_select, cmp_fixed, mul_fixed (cross-validated against BigNat mul), mod_reduce_ct, `mod_exp_ct_stub` (regime-only: base^0 = 1; 1^k = 1 — see "Stub regime" below). |
| **Total** | **1415** | |

## Test results

```
bin/simple test test/unit/lib/math/bignum/                        # 57 passed, 0 failed
bin/simple lint src/lib/common/math/bignum/ test/unit/lib/.../    # OK
bin/simple test test/unit/lib/bitwise_byte_helpers_spec.spl       # 8 passed (regression check)
```

**`bin/simple build check`:** confirmed silent-noop wrapper (exit 0, zero
stdout/stderr) — matches the `feedback_extern_bootstrap_rebuild.md` memory
entry that `build` falls through the wrapper whitelist.  Substituted with
directory-scoped lint + adjacent-spec regression checks above.

## KAT count and sources

**Total: 57 KAT cases.**

- **Hand-picked edge cases (all 57):**
  - Limb-layer (3): `LIMB_MASK^2 = (1, LIMB_BASE-2)`; carry-chain add at LIMB_BASE.
  - BigNat (33): canonical zero, single-limb arithmetic, multi-limb carry/borrow propagation, `LIMB_MASK*LIMB_MASK` cross-check, division (`100/7 = (14, 2)`, `(LIMB_BASE+5) mod LIMB_BASE = 5`), big-endian byte encoding (`0x0102 = 258`, `0xDEADBEEF` round-trip), little-endian symmetry.
  - Fixed CT (21): cond_swap double-swap identity, cond_select boundaries, cmp_fixed -1/0/1, mul_fixed cross-validated against BigNat `mul`, `mod_exp_ct(5,3,2^29+1) = 125`, `base^0 = 1`.
- **RFC / NIST vectors:** none used directly in this scaffold (intentional). Per advisor and R-B's migration plan, RFC 3447 PKCS#1 vectors live in the RSA module's KAT spec which consumes bignum; NIST SP 800-56A and full primality tests are gated on the migration step (R-B §5 step 3+) which is out of scope for I-3.

The bignum scaffold cross-validates Fixed `mul_fixed` against BigNat `mul` for the `LIMB_MASK^2` corner — the highest-risk overflow case in 30-bit limbs.

## Deviations from R-B's spec

1. **`Fixed<N: i64>` const-numeric generic → plain struct with `n: i64` field.**
   *Reason:* Const-numeric generics are not in active use in the codebase (verified by `grep -rn 'struct.*<.*>'` returning only type-parameter generics like `Connection<State>`). Per advisor, attempting unproven generic syntax risked blocking the entire scaffold. The CT property is preserved because `n` is a public, compile-time-fixed parameter at every call site (`FIXED_256`, `FIXED_2048`, etc.) — not derived from secret bits. Migration to a true const-generic later is a mechanical rename if the compiler grows that feature.
2. **`type BigNat = [i64]` alias not used; functions take `[i64]` directly.**
   *Reason:* No precedent for type-alias declarations in `src/lib/common/`. Annotations everywhere refer directly to `[i64]`; the BigNat invariant (top limb non-zero or canonical `[0]`) is documented in the module header.
3. **`mod_exp_ct` and `mod_inv_ct` are shipped as STUBS (`*_stub` suffix), not functional CT primitives.**
   *Issue:* Advisor caught this on the second pass — the post-multiply
   reduction inside `mod_exp_ct` truncates the upper n limbs of the 2n-limb
   schoolbook product instead of running a full Barrett / Montgomery
   reduction.  That's mathematically correct only when intermediate squares
   stay below 2^(n·30); for real RSA / curve moduli the upper-half bits
   matter and the function returns garbage.
   *Resolution:* Renamed to `mod_exp_ct_stub` / `mod_inv_ct_stub` with
   prominent "DO NOT USE FOR REAL CRYPTO" warnings in the docstrings and a
   pointer to this deviation entry.  KATs in `fixed_spec.spl` were tightened
   to stay strictly inside the stub-correct regime (`base^0 = 1`, `1^k = 1`)
   so they exercise the CT *shape* (square-and-multiply-always, cond_select
   per bit, n·30-bit loop) without depending on the broken reduction.
   The plumbing (Fermat dispatch in `mod_inv_ct_stub`, exponent build via
   `sub_fixed`) is in place for the migration step (R-B §5 step 3) to swap
   in Montgomery reduction with no API churn.
4. **`mod_reduce_ct` is a 2-step conditional subtraction (not Barrett / Montgomery).**
   *Reason:* Per R-B §3 the GF(p)-specific reductions live in R-C's field module. `mod_reduce_ct` here is a minimal building block; full RSA-CRT will replace it (and `mod_exp_ct_stub`'s reduction) with Montgomery in the migration step.
5. **Used `mod.spl` (per task spec) rather than `__init__.spl` (rsa convention).**
   *Reason:* Task spec said `mod.spl`. Both forms are picked up by `use std.math.bignum.X` import resolution; `mod.spl` is the more modern convention and the test harness resolves it correctly (verified: `bin/simple test` green from a `use std.math.bignum.limb.{...}` import path).
6. **`add_fixed` / `sub_fixed` return `[Fixed; 2]` (sum/diff + carry/borrow as a 1-limb Fixed) rather than a tuple.**
   *Reason:* No tuple-return precedent for `(Fixed, i64)` was found; using a 2-element list of Fixed keeps the existing convention. The carry/borrow is wrapped through `rt_black_box` before being placed in the second Fixed — same CT property as the design intent.

## Externs added

**None.** The design uses only `rt_black_box` (already wired, B6 closed) and standard list operations. No `bootstrap-from-scratch.sh --deploy` rebuild required, as confirmed by R-B §6.

## Pre-allocation rule (H-5)

All arithmetic inner loops use indexed assignment into pre-sized `[i64]` (or `[u8]`) buffers. The only `.push` calls in the module are:
- One-shot fixed-count zero-fill loops at function entry (`while i < n: result.push(0)`), permitted per R-B's design rule.
- `bn_from_i64` (driven by input value — bounded by 64 / LIMB_BITS = 3 pushes max).
- `from_bytes_le` reverse helper (single O(n) reverse pass, bounded by input size).
- `div_mod` quotient growth (one push per limb of the quotient as it grows; bounded by `bit_length(a) / LIMB_BITS`, single pass).

No `.push` appears inside the schoolbook multiply nest, the carry-add inner loop, or the fixed-CT reductions.

## Out of scope (deferred)

Per R-B's migration plan (§5) and I-3 task scope:
- Migrating `rsa_fallback._bi_*` → `math.bignum` (R-B §5 step 3).
- Deleting `curve25519_bigint.spl` (R-B §5 step 4) — gated on R-C's `gf_25519.spl`.
- ed25519 `Fixed<8, u32>` ScalarMod helpers (R-B §5 step 6) — different limb width.
- Full Barrett / Montgomery reduction in `fixed.spl` — moved to GF(p) modules.
- DUDECT-style timing harness for CT verification — separate test track.

## Advisor consultations

- **Pre-implementation:** flagged const-numeric generic risk → switched to plain `struct Fixed { n, limbs }`. Flagged `mod_inv_ct` ambiguity (not in R-B's design) → adopted Fermat with documented prime-modulus precondition. Flagged `type BigNat = [i64]` alias risk → used direct `[i64]` annotations. Recommended a 30-line spike before scaling up — landed as `limb_spike_spec.spl` (3 tests, green) and gated full implementation.
- **Pre-done:** caught two real issues the self-tests missed:
  1. `mod_exp_ct` truncates the upper half of the 2n-limb product, so the "5^3 mod (2^29+1) = 125" KAT only passed because intermediates stayed inside one 30-bit limb. Resolution: renamed to `mod_exp_ct_stub`/`mod_inv_ct_stub`, hardened docstrings with explicit "DO NOT USE FOR REAL CRYPTO", trimmed KATs to the stub-correct regime, queued Montgomery replacement against the migration step. See deviation #3.
  2. `bin/simple build check` exits 0 silently — confirmed it is a noop wrapper (zero stdout/stderr lines). Resolution: replaced the build-check claim in this doc with the directory-scoped lint + adjacent-spec regression checks that *did* run.
  3. Cleanup: removed dead first loop in `cmp_fixed`, fixed `(d >> 31)` → `(d >> 63)` for i64 sign extraction (worked-by-accident before).

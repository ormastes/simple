# Plan: RSA Modexp Performance -- Montgomery/Barrett Reducer (FR-CRYPTO-0001)

- **Date:** 2026-05-30
- **Status:** Planned
- **Priority:** P1
- **FR:** `doc/08_tracking/feature_request/rsa_pss_pure_simple_modexp_perf_2026-05-02.md`
- **Effort:** L (2-3 weeks)

## Context

Pure-Simple RSA-2048 modexp times out under the 60s interpreter watchdog.
The bottleneck is `_pss_bi_mod` (and `rsa_fallback._bi_mod`) performing
one shift+subtract per bit per modexp round -- O(bits^3) with 30-bit limbs.

Current state (2026-05-30):
- Safe hot-path speedups already landed: normalize avoids copy, get_bit uses
  direct limb-mask, shift_left_one short-circuits zero, 4-bit sliding window
  exponent loop, CRT sign path for PKCS#8 keys with p/q/dP/dQ/qInv
- Shifted-modulus reducer shape shared between `rsa_pss.spl` and `rsa_fallback.spl`
- Despite all optimizations, RSA-2048 full round-trip still exceeds 60s in
  interpreter mode
- `rt_bigint_mod_exp` extern declared in `signature_sffi.spl` but not implemented
- `src/lib/common/math/bignum/` directory does NOT exist

The remaining fix requires either a Montgomery or Barrett modular reducer that
reduces the per-multiplication cost from O(n) shift-subtract to O(n) multiply,
bringing total modexp from O(n^3) to O(n^2 * log(e)).

## Prerequisites and Blockers

1. **30-bit limb representation** -- both `rsa_pss.spl` and `rsa_fallback.spl`
   use `List<i64>` with each limb in [0, 2^30); the reducer must use the same
   representation
2. **Interpreter array performance** -- arrays are value types (passed by copy);
   Montgomery multiplication with large limb arrays may still be slow if the
   interpreter copies on every function call (see `feedback_arrays_value_types.md`)
3. **No compile-mode test verification** -- interpreter mode is the only reliable
   test path (`feedback_compile_mode_false_greens.md`)

## Phased Implementation Steps

### Phase 1: Extract Shared BigInt Module (M)

Both `rsa_pss.spl` and `rsa_fallback.spl` have duplicated bigint code because
Simple's underscore-prefixed names are module-private. Extract shared code.

**Important constraint:** The existing duplication is a deliberate design choice
documented in `rsa_pss.spl`: "duplicated locally rather than imported... keeps
the module self-contained for baremetal/freestanding callers (matches the
slh_dsa / ml_dsa pattern)." The shared module MUST remain baremetal-safe: no GC
dependency, no runtime allocator dependency, no `use std.io` or side-effecting
imports. Place it in `src/lib/common/math/` (pure functions tier) to guarantee
this. If baremetal self-containment cannot be preserved, keep the duplication
and add Montgomery code to both modules independently instead.

1. Create `src/lib/common/math/bigint.spl` with public API:
   - `bi_from_bytes(bytes: List<i64>) -> List<i64>` (30-bit limb encoding)
   - `bi_to_bytes(limbs: List<i64>, len: Int) -> List<i64>`
   - `bi_mul(a: List<i64>, b: List<i64>) -> List<i64>` (schoolbook)
   - `bi_add(a: List<i64>, b: List<i64>) -> List<i64>`
   - `bi_sub(a: List<i64>, b: List<i64>) -> List<i64>`
   - `bi_cmp(a: List<i64>, b: List<i64>) -> Int`
   - `bi_shift_right(a: List<i64>, bits: Int) -> List<i64>`
   - `bi_shift_left(a: List<i64>, bits: Int) -> List<i64>`
   - `bi_normalize(a: List<i64>) -> List<i64>`
   - `bi_get_bit(a: List<i64>, idx: Int) -> Int`
   - `bi_bit_length(a: List<i64>) -> Int`
2. Migrate `rsa_pss.spl` private `_pss_bi_*` functions to call shared module
3. Migrate `rsa_fallback.spl` private `_bi_*` functions to call shared module
4. Verify: `bin/simple test test/unit/lib/crypto/rsa_pss_sha256_kat_spec.spl --mode=interpreter`
   still passes at ~2300ms

**Files to create:** `src/lib/common/math/bigint.spl`
**Files to modify:** `src/os/crypto/rsa_pss.spl`, `src/os/crypto/rsa_fallback.spl`
**Files to create:** `test/unit/lib/math/bigint_spec.spl`

### Phase 2: Montgomery Multiplication (L)

Implement Montgomery modular multiplication for the 30-bit limb representation.

1. Add to `src/lib/common/math/bigint.spl`:
   - `bi_montgomery_setup(modulus: List<i64>) -> MontgomeryCtx` where
     `MontgomeryCtx` holds: `n` (modulus), `n_prime` (Montgomery constant
     -n^(-1) mod R), `r_squared` (R^2 mod n), `num_limbs`
   - R = 2^(30 * num_limbs) (one extra limb beyond modulus)
   - `n_prime` computed via extended GCD or Newton iteration on the lowest limb
   - `r_squared` computed by repeated doubling: `1 << (60 * num_limbs) mod n`
2. Implement `bi_montgomery_mul(a: List<i64>, b: List<i64>, ctx: MontgomeryCtx) -> List<i64>`:
   - Standard CIOS (Coarsely Integrated Operand Scanning) algorithm
   - For each limb i of a: t = t + a[i]*b + ((t[0]*n_prime) mod 2^30)*n
   - Final conditional subtraction
   - Result is in Montgomery form (a*b*R^(-1) mod n)
3. Implement `bi_to_montgomery(a: List<i64>, ctx: MontgomeryCtx) -> List<i64>`:
   `bi_montgomery_mul(a, ctx.r_squared, ctx)` -- converts to Montgomery form
4. Implement `bi_from_montgomery(a: List<i64>, ctx: MontgomeryCtx) -> List<i64>`:
   `bi_montgomery_mul(a, [1], ctx)` -- converts back from Montgomery form

**Files to modify:** `src/lib/common/math/bigint.spl`
**Files to create:** `test/unit/lib/math/montgomery_spec.spl`

### Phase 3: Montgomery Modexp (M)

Wire Montgomery multiplication into the exponentiation loop.

1. Implement `bi_mod_exp_montgomery(base: List<i64>, exp: List<i64>, modulus: List<i64>) -> List<i64>`:
   - Setup: `ctx = bi_montgomery_setup(modulus)`
   - Convert base to Montgomery form: `m_base = bi_to_montgomery(base, ctx)`
   - Precompute window table (reuse existing 4-bit sliding window):
     `table[0] = R mod n` (identity in Montgomery), `table[i] = montgomery_mul(table[i-1], m_base, ctx)`
   - MSB-first exponent scan with 4-bit windows
   - Convert result back: `bi_from_montgomery(result, ctx)`
2. Replace `_pss_bi_mod_exp` inner loop to call `bi_mod_exp_montgomery`
3. Replace `rsa_fallback._bi_mod_exp` to call `bi_mod_exp_montgomery`
4. CRT path in `rsa_pss.spl` benefits automatically (half-size modexps)

**Files to modify:** `src/lib/common/math/bigint.spl`,
`src/os/crypto/rsa_pss.spl`, `src/os/crypto/rsa_fallback.spl`

### Phase 4: Interpreter Perf Workarounds (S)

Address interpreter-specific bottlenecks that may persist.

1. **Array copy overhead:** Since arrays are value types, each
   `bi_montgomery_mul` call copies limb arrays. Mitigation: inline the
   critical multiply loop body or use a single mutable accumulator pattern
   where the function modifies and returns the same array reference
2. **Limb count:** For RSA-2048, modulus is ~69 limbs (2048/30). Montgomery
   multiply is O(n^2) per multiplication = ~4761 limb ops. With 4-bit window,
   ~512 multiplies + ~512 squarings = ~4.9M limb ops total. Estimate
   interpreter throughput at ~100K-500K ops/sec = 10-50s. If borderline,
   consider:
   - Increasing limb size to 52-bit (using f64 mantissa) to halve limb count
   - Or wiring `rt_bigint_mod_exp` extern for compiled-mode acceleration
3. Verify final timing: `timeout 60s env SIMPLE_LIB=src bin/simple test --only-slow test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl --mode=interpreter --clean --fail-fast`

**Files to modify:** `src/lib/common/math/bigint.spl` (if 52-bit limbs needed)

### Phase 5: Verification and Cleanup (S)

1. Run `rsa_pss_sha256_roundtrip_slow_spec.spl` in interpreter mode -- must
   complete within 60s
2. Run `rsa_pkcs1_v15_spec.spl` with PureSimple backend in interpreter mode
3. Run `rsa_pss_sha256_kat_spec.spl` -- verify no regression from shared module
4. Run `rsa_pss_smoke_spec.spl` and `rsa_contract_parity_spec.spl`
5. Remove or deprecate the schoolbook `_bi_mod` fallback path

**Files to modify:** `test/unit/lib/crypto/rsa_pkcs1_v15_spec.spl` (switch to
PureSimple backend)

## Acceptance Criteria

- [ ] `test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl` completes
      within 60s in interpreter mode (RSA-2048 sign + verify)
- [ ] `test/unit/lib/crypto/rsa_pkcs1_v15_spec.spl` passes via PureSimple
      backend in interpreter mode (not HostedReference)
- [ ] No new dependency on `rt_embedded_host_rsa_component`
- [ ] Shared `src/lib/common/math/bigint.spl` with full test coverage
- [ ] Montgomery multiply round-trips correctly for random inputs
- [ ] All existing RSA/crypto specs pass without regression

## Risk Factors

- **Interpreter array copy overhead (High):** Arrays as value types means every
  Montgomery multiply copies ~69 limbs multiple times. If this makes the 60s
  budget infeasible, the fallback is either 52-bit limbs (halving limb count
  and quartering multiply cost) or the `rt_bigint_mod_exp` extern path. The
  extern path is explicitly discouraged by the FR but may be the only option
  if pure-Simple interpreter perf hits a wall
- **Montgomery constant computation (Medium):** Computing `n' = -n^(-1) mod R`
  requires modular inverse of the lowest limb; extended GCD on a single 30-bit
  value is trivial but must be implemented correctly
- **Correctness risk (Medium):** Montgomery multiplication is notoriously
  tricky to implement correctly. CIOS algorithm must handle carries across
  limbs precisely. Recommend implementing a naive Montgomery first (separate
  multiply + reduce), validating against known test vectors, then optimizing
  to CIOS
- **CRT interaction (Low):** The CRT path already works; Montgomery is
  transparent to it since it only affects the inner modexp
- **Baremetal self-containment (Medium):** The existing duplication is deliberate
  for freestanding callers. The shared `bigint.spl` in `src/lib/common/math/`
  must have zero runtime/GC/IO dependencies. If any dependency creeps in, revert
  to duplicating Montgomery code in both `rsa_pss.spl` and `rsa_fallback.spl`
  independently

# GF(p) Field Module Design — R-C

**Scope:** Unify Curve25519 / Ed25519 / NIST P-256 finite-field arithmetic into a single
parametrized `src/lib/common/math/field/` module, then sketch a curve layer that consumes
it. Read-only research deliverable. No code changes.

**Domain split with R-B (bignum):** R-B owns limb representation choices and bulk
big-integer ops (`bi_add`, `bi_mul`, `bi_modpow` etc.). R-C owns *field-level* ops on top
of those limbs (`fe_add`, `fe_mul`, `fe_inv`, `fe_sqrt`, ladder step) and *curve-level*
ops (`scalar_mul`, `point_add`, `point_double`). **Assumption (state until R-B publishes):**
Curve25519 / Ed25519 keep the existing 5×51-bit (u64 limb, u128 product accumulator)
representation; P-256 will use 4×64-bit unsigned limbs with explicit u128 carries (Solinas
reduction). If R-B chooses differently, only the per-prime `_carry` / `_reduce` private
functions change — the public `Fe`/`Field`-trait API does not.

---

## 1. Three Back-Ends Compared

| File | Lines | Limb form | CT properties | Strength | Verdict |
|------|-------|-----------|---------------|----------|---------|
| `curve25519.spl` | 1291 | 5×51 bits in `u64`, `u128` for products (radix-2^51 pseudo-Mersenne) | Branch-free `fe_add`/`fe_sub`/`fe_mul`; `_fe_carry_wide` constant-time; cswap mask-based | Canonical X25519 reference (RFC 7748 layout); only file with full Edwards reuse via Ed25519 import | **KEEP** |
| `curve25519_bigint.spl` | 517 | 9×30-bit limbs in a generic `list` (radix-2^30 fixed-size); `_bigint_field_reduce` walks bits | Cswap branch-free; reduction uses generic compare/sub — slow but CT | Workaround for B2 (`[u8]` quadratic) + interpreter checked-overflow paths | **DELETE** — both root causes are FIXED (B2 closed in `e4b572b7c4`, `rt_bytes_alloc` lands 32 MiB in ~1.5 s) |
| `curve25519_bigint_wrapper.spl` | 26 | (re-exports `curve25519_bigint`) | n/a | Probe shim only | **DELETE** with the bigint backend |
| `curve25519_smalllimb.spl` | 531 | 10×25/26-bit `u64` limbs + manual carries; **`>>` replaced with `/` everywhere** | Branch-free arith; uses `_load3`/`_load4` divisions | Workaround for Cranelift right-shift miscompile | **DELETE** — fix landed 2026-04-18 (FR-DRIVER-0002b, memory `feedback_cranelift_shr_bug.md`); workaround obsolete |

**Survivor:** `curve25519.spl` (5×51 + u128). It is the only one whose existence is *not*
predicated on a now-closed compiler bug, and it is the field already consumed by
`ed25519.spl`.

**Bonus:** Picking 5×51 also sidesteps **B7 H-3** (`mul_hi` libcall) — H-3 is only a
problem if we choose a 26-bit small-limb radix needing high-half multiplies.

---

## 2. Unified Field API

**File layout (proposed):**

```
src/lib/common/math/field/
    mod.spl                      # public re-exports + Field trait
    field_trait.spl              # trait Field { ... }
    fe25519.spl                  # 5×51 impl, prime = 2^255 - 19
    fep256.spl                   # 4×64 impl, prime = 2^256 - 2^224 + 2^192 + 2^96 - 1
    fe_helpers.spl               # generic fe_pow, fe_eq via cond_select
```

**Parametrization decision:** `trait Field` + **two concrete impls** (`Fe25519`, `FeP256`).
*Not* a single generic-over-prime type, because:
- 25519 uses pseudo-Mersenne reduction (one multiply by 19 in `_fe_carry_wide`); P-256
  needs Solinas reduction (six 32-bit-aligned add/subs) — these collapse to *radically*
  different inner loops; a generic body would lose 3-5× of the speed.
- Trait dispatch is monomorphized by Simple's `<>` generics, so the curve-level layer
  (Edwards / Montgomery / Weierstrass) compiles once per concrete `Fe`, with no runtime
  cost.

**Public trait (sketch):**

```spl
trait Field:
    type Repr                                                # opaque limb tuple
    fn fe_zero() -> Self::Repr
    fn fe_one() -> Self::Repr
    fn fe_from_bytes(b: [u8]) -> Self::Repr                  # 32 BE bytes
    fn fe_to_bytes(a: Self::Repr) -> [u8]                    # canonical reduce + encode
    fn fe_add(a: Self::Repr, b: Self::Repr) -> Self::Repr
    fn fe_sub(a: Self::Repr, b: Self::Repr) -> Self::Repr
    fn fe_neg(a: Self::Repr) -> Self::Repr
    fn fe_mul(a: Self::Repr, b: Self::Repr) -> Self::Repr
    fn fe_sq(a: Self::Repr) -> Self::Repr
    fn fe_pow(a: Self::Repr, e: [u8]) -> Self::Repr          # Montgomery ladder, CT
    fn fe_inv(a: Self::Repr) -> Self::Repr                   # fe_pow(a, p-2)
    fn fe_sqrt(a: Self::Repr) -> Option<Self::Repr>          # 25519: pow((p+3)/8); P-256: pow((p+1)/4)
    fn fe_eq(a: Self::Repr, b: Self::Repr) -> bool           # via XOR-accumulate + black_box
    fn fe_is_zero(a: Self::Repr) -> bool
    fn fe_cond_swap(a: Self::Repr, b: Self::Repr, swap: u64) -> (Self::Repr, Self::Repr)
    fn fe_cond_select(a: Self::Repr, b: Self::Repr, take_b: u64) -> Self::Repr
```

`Fe` is opaque (the trait's `Repr`); callers never index limbs directly. The prime is
*selected by the impl module*, not a runtime parameter — no per-call branch on the prime.

**Where the prime lives:** as `const` data inside each impl module
(`fe25519.spl::P_LIMB_MASK`, `fep256.spl::P256_PRIME_LIMBS`). No runtime dispatch.

---

## 3. Curve-Level API

**File layout:**

```
src/lib/common/math/curve/
    mod.spl
    montgomery.spl   # generic over <F: Field>: x-only ladder, X25519
    edwards.spl      # generic over <F: Field>: extended (X,Y,Z,T), Ed25519
    weierstrass.spl  # generic over <F: Field>: Jacobian (X,Y,Z), P-256
    curve25519.spl   # = montgomery::<Fe25519> with A24=121665, clamp25519
    ed25519.spl      # = edwards::<Fe25519> with d = -121665/121666, base point B
    p256.spl         # = weierstrass::<FeP256> with a=-3, b=SECG, base point G
```

**Shared code between X25519 and Ed25519 (the prize):**
- `Fe25519` arithmetic: 100% shared (`fe_add`/`fe_sub`/`fe_mul`/`fe_sq`/`fe_inv`/`fe_sqrt`).
- Scalar clamp byte-twiddle (`scalar[0] &= 248; scalar[31] &= 127; scalar[31] |= 64`):
  shared as `clamp25519` helper.
- Conditional swap: shared via the `Field` trait.
- *Not* shared: ladder-step (Montgomery x-only) vs Edwards point-add (HWCD08 extended).
  These are different algorithms, correctly in separate `montgomery.spl` /
  `edwards.spl`.

**Generic point types:**

```spl
struct MontgomeryPoint<F: Field>:    x: F::Repr; z: F::Repr
struct EdwardsPoint<F: Field>:       x: F::Repr; y: F::Repr; z: F::Repr; t: F::Repr
struct WeierstrassPoint<F: Field>:   x: F::Repr; y: F::Repr; z: F::Repr   # Jacobian
```

**Generic ops (CT, branch-free where required):**
- `montgomery::ladder_step<F>(x2, z2, x3, z3, x1) -> (x2',z2',x3',z3')` — uses
  `F::fe_add/sub/mul/sq` only.
- `edwards::point_add<F>(p, q, d2: F::Repr) -> EdwardsPoint<F>` — HWCD08; takes the
  curve's `2d` constant as a parameter so the same code serves Ed25519 and any future
  Edwards-form curve.
- `weierstrass::point_add<F>(p, q) -> WeierstrassPoint<F>` — formulas-2007-bl complete
  addition.
- `scalar_mul_ct<F, P>(scalar: [u8], p: P) -> P` — fixed-window with `fe_cond_select`
  table lookup; works for any of the three point types via a small `Group` trait
  (`group_zero`, `group_double`, `group_add`).

The curve files (`curve25519.spl` / `ed25519.spl` / `p256.spl`) become **thin
specializations**: a few hundred lines of constants + trait instantiation, replacing the
current 1291 + 517 + 26 + 531 + 946 = 3311 lines of competing 25519 code with one
~1400-line shared core.

---

## 4. CT-Correctness Checklist

| Function | Branch-free | No secret index | No early return | Notes |
|----------|-------------|-----------------|-----------------|-------|
| `fe_add` | Y | Y | Y | Carry chain unconditional |
| `fe_sub` | Y | Y | Y | Add `2p` then carry |
| `fe_neg` | Y | Y | Y | `fe_sub(zero, a)` |
| `fe_mul` | Y | Y | Y | Schoolbook + reduce; no data-dep branches |
| `fe_sq` | Y | Y | Y | Same shape as `fe_mul` |
| `fe_pow` | Y | Y | Y | Square-and-multiply-always (Montgomery ladder over u8 exponent), exponent treated public-but-CT-safe |
| `fe_inv` | Y | Y | Y | Calls `fe_pow` with `p-2` (public exponent — addition chain like djb's preferred) |
| `fe_sqrt` | Y | Y | Y | Pow + final `fe_cond_select` based on legendre check |
| `fe_eq` | Y | Y | Y | XOR-accumulate over bytes, **wrap in `rt_black_box`** (B6, commit `d42cde3a0f`) |
| `fe_is_zero` | Y | Y | Y | Reduce → byte-OR → black_box |
| `fe_cond_swap` | Y | Y | Y | mask = -swap; `a' = a ^ ((a^b)&mask)` |
| `fe_cond_select` | Y | Y | Y | mask form; **must** route mask through `rt_black_box` so optimizer cannot rebuild a branch |
| `fe_to_bytes` | Y | Y | Y | Final canonical reduce uses arithmetic compare (subtract-then-mask), not `if` |
| `montgomery::ladder_step` | Y | Y | Y | `cswap` per scalar bit |
| `edwards::point_add` | Y | Y | Y | HWCD08 has no branches |
| `scalar_mul_ct` | Y | Y | Y | Fixed-window table lookup via linear `fe_cond_select` scan, never indexed by secret |
| `ed25519_verify` | N (OK) | N (OK) | N (OK) | Public-input only — branchy is fine and faster |

**B7 applicability:**
- **H-1** (`u32.to_be_bytes` not folded): applies in `fe_to_bytes` final pack. Mitigation:
  use explicit byte stores via shifts (current code already does this in `_store_limb`),
  do **not** rely on `to_be_bytes`.
- **H-3** (`mul_hi` libcall): **avoided by design** — 5×51 + u128 means high-half is the
  upper 64 bits of a u128 multiply, which Cranelift lowers natively.
- **H-4** (GF(2^128) clmul): **not applicable** — this is GHASH territory, not GF(p).
- **H-6** (Keccak rotl fold): **not applicable** — no rotations in field arithmetic.

---

## 5. Migration Plan

**Order (all on `main`, jj-only, no branches):**

1. **Add new tree** `src/lib/common/math/field/{mod,field_trait,fe25519,fe_helpers}.spl`.
   Body of `fe25519.spl` is `curve25519.spl::Fe25519` and friends, *moved verbatim*. No
   semantic change. Verify with existing `test/system/ed25519_all_pairs_spec.spl` etc.
2. **Add** `src/lib/common/math/curve/{mod,montgomery,edwards,curve25519,ed25519}.spl`.
   Re-implement X25519 / Ed25519 in terms of the new generics. Re-export old public
   names from `os/crypto/curve25519.spl` and `os/crypto/ed25519.spl` as `pub use`
   shims so callers don't break in one CL.
3. **Re-point the three system specs** to the new module path:
   - `test/system/ed25519_all_pairs_spec.spl`
   - `test/system/os_rt_ed25519_sign_spec.spl`
   - `test/system/os_ed25519_wrapper_contract_spec.spl`
   (Note: spec lives under `test/system/`, not `test/unit/os/crypto/` — that path does
   not exist today. The task description's `test/unit/os/crypto/` path was wrong;
   migration targets the existing system specs.)
4. **Delete** in one commit (after green run):
   - `src/os/crypto/curve25519_bigint.spl`
   - `src/os/crypto/curve25519_bigint_wrapper.spl`
   - `src/os/crypto/curve25519_smalllimb.spl`
   - The 6 `bigint_*_probe` re-exports inside `curve25519.spl` (lines ~14, used only by
     the wrapper).
5. **Add** `fep256.spl` (NEW pure-Simple code — see Risk #1) gated behind a feature flag
   so the FFI-backed `ecdsa_p256.spl` keeps working until the pure version passes
   Wycheproof KAT.
6. **Add** `src/lib/common/math/curve/{weierstrass,p256}.spl`. The current
   `os/crypto/ecdsa_p256.spl` continues to use the FFI runtime; we cut over only when
   the pure path is bit-exact on Wycheproof.

**No file under `os/crypto/rsa.spl` is touched** — RSA is a multiplicative group mod a
composite, not a field. Explicitly out of scope.

---

## 6. Risks + Open Questions

1. **P-256 pure-Simple field is NEW code, not a refactor.** The current
   `ecdsa_p256.spl` (332 lines) is FFI-only — every `fe_*` for P-256 must be written
   from scratch with Solinas reduction. This is the largest single risk; the "unified
   field" framing should not hide it. Mitigation: keep FFI path live until KAT-passing.
2. **Trait monomorphization cost in the bootstrap compiler.** Generic `<F: Field>` Edwards
   /Weierstrass code compiled twice (once per concrete prime) may regress build time if
   Simple's monomorphization is naive. If perf budget is tight, fall back to
   copy-paste-per-prime for the curve layer (still saving the field layer).
3. **`fe_cond_select` after Cranelift `select` lowering.** Even with `rt_black_box`,
   Cranelift may emit `select` rather than mask arithmetic, which on some ISAs is a
   conditional move and *still* CT — but on others may not be. Open question: does our
   Cranelift target list emit only ISAs where `select` is CT? If not, force
   mask-arithmetic at the source level.

---

**Files authored by R-C:** this document, only.

# Bignum Library Design — `src/lib/common/math/bignum/`

**Author:** R-B (parallel SStack research fan-out)
**Date:** 2026-04-25
**Scope:** Pure-Simple bignum integer arithmetic underpinning RSA, Ed25519
scalar reduction, ECDSA-P256 mod-q, and Curve25519 byte/scalar conversion.
GF(p)-specific representations (Fe25519 5×51-bit, Fp256 native limbs) stay
with R-C. This doc proposes one canonical limb representation and a layered
API, and orders the migration so cycles never form.

Evidence basis:
- `src/lib/common/rsa/types.spl` and `src/os/crypto/rsa_fallback.spl` already
  use `list`-of-`i64`, base 2^30, little-endian — same shape, duplicated.
- `src/os/crypto/curve25519_bigint.spl` re-declares the same 2^30/i64 layout
  for `FIELD_P` (`[…, 32767]` = 9 limbs × 30 bits = 270 bits → trims to 255).
- `src/os/crypto/ed25519.spl` uses `[u32]` 8-limb fixed-length for scalars.
- `src/os/crypto/curve25519.spl` uses 5×51-bit `Fe25519` (u64) — **not** in scope.
- `compiler_bugs_for_crypto_2026-04-25.md` §B7: H-3 (`u64.mul_hi` libcall) and
  H-5 (`[u64].push` quadratic) both bite the u64 path.
- Memory `feedback_interpreter_bulk_buffer.md`: `rt_bytes_alloc(n) -> [u8]`
  is wired (B2 fixed 2026-04-25).
- `src/lib/common/crypto/constant_time.spl`: `rt_black_box(i64) -> i64`
  available (B6 closed).

---

## 1. Goals & non-goals

### Goals
- One canonical bignum module under `src/lib/common/math/bignum/` consumed by
  every crypto site that today re-implements `_bi_*` (RSA fallback, RSA
  modular, curve25519_bigint, ed25519 scalar reduce, ECDSA-P256 scalar
  arithmetic).
- Sizes: up to **4096 bits** (RSA-4096 modulus = 137 limbs at 2^30) plus a
  **256-bit fast path** (Fixed<9, i64>) for ECC scalar operations.
- Targets:
  - Interpreter: RSA-2048 verify (single mod-exp) ≤ 2 s wall.
  - Native: RSA-4096 sign (CRT, two mod-exps) ≤ 200 ms; ECC scalar reduction
    ≤ 50 µs.
- Constant-time partition: a **Fixed<N>** layer with no normalization, no
  early-exit, suitable for secret-dependent `mod_exp` and `cond_swap`.

### Non-goals
- GF(p) field arithmetic with curve-specific reduction (Fe25519 5×51-bit,
  P-256 saturated 5×52-bit Solinas reduction). R-C designs that on top of
  this bignum's `from_bytes_be/le`, `to_bytes`, and Fixed<N> primitives.
- Montgomery multiplication / Barrett reduction (a *future* optimisation
  layer — out of v1 scope; we use bit-by-bit reduce as `rsa_fallback`
  already does).
- Negative numbers as a separate type. Sign carried out-of-band as
  `(BigNat, bool is_negative)` tuple where needed (egcd). Same convention
  modular.spl uses today.

---

## 2. Limb representation — chosen: **`[i64]` base 2^30, little-endian**

**Rationale (one sentence):** Two existing pure-Simple bignum implementations
(`rsa_fallback._bi_*` and `rsa/types.spl`) already converged on this; it
sidesteps H-3 (30+30=60 bits fits in i64 with no `mul_hi` libcall) and H-5
(which targets `[u64].push` specifically — `[i64]` is a different storage
class but, more importantly, the *design rule* below avoids `.push` in
arithmetic inner loops entirely).

Alternatives considered and rejected:
- `[u64]` base 2^32: clean but H-3 forces `mul_hi` libcall on every limb mul,
  and H-5 (push quadratic) bites RSA-4096 modulus growth (137 limbs).
- `[u32]` base 2^26: ed25519 already uses `[u32]` × 8 for 256-bit scalars;
  for RSA-4096 this doubles limb count to 158 with no codegen benefit.
- 26-bit small-limb on `[i64]`: 4 extra limbs per RSA-4096 number for no
  win — 30 bits × i64 already has 4 spare bits of carry headroom, the
  textbook "schoolbook product fits before normalisation" property.

### Type signatures

```spl
# Variable-length, normalized. Public values, key gen, GCD, mod inverse.
type BigNat = [i64]   # alias; semantic invariant: top limb non-zero or len==1

# Fixed-length, never normalized. Secret-dependent paths.
struct Fixed<N: i64>:
    """Fixed-length N-limb bignum at base 2^30. Length never branches."""
    limbs: [i64]   # exactly N entries, even if leading zeros

# Constants (in math/bignum/types.spl)
val LIMB_BITS: i64 = 30
val LIMB_BASE: i64 = 1073741824        # 2^30
val LIMB_MASK: i64 = 1073741823        # 2^30 - 1

# Common widths
val FIXED_256: i64 = 9    # ⌈256/30⌉
val FIXED_512: i64 = 18
val FIXED_2048: i64 = 69
val FIXED_4096: i64 = 137
```

**Design rule (H-5 avoidance):** *No `.push` inside arithmetic inner loops.*
Every kernel pre-allocates the result list to its known final length and uses
indexed assignment. RSA-4096 mul is then `2*137=274` slots seeded once, not
274 individual pushes. This is the pattern `rsa_fallback._bi_mul` already
uses (lines 134–164) — codify it as the contract.

---

## 3. API surface

Layout (one file per concern, mirroring `src/lib/common/crypto/` style):

```
src/lib/common/math/bignum/
├── types.spl       # BigNat alias, Fixed<N>, constants
├── encoding.spl    # bytes <-> limbs
├── core.spl        # add, sub, cmp, shifts, normalize
├── mul.spl         # mul, mul_lo_hi, mul_i64
├── divmod.spl      # bit-by-bit div_mod, mod
├── modexp.spl      # mod_exp (variable-time and Fixed<N>-CT versions)
├── modinv.spl      # gcd, egcd, mod_inv
└── ct.spl          # constant-time helpers: cond_swap, select, eq, is_zero_ct
```

### Public API

| Function | Signature | Semantics | CT? |
|----------|-----------|-----------|-----|
| `from_bytes_be` | `(b: [u8]) -> BigNat` | Big-endian bytes → BigNat (normalized) | leaks `b.len()` only |
| `from_bytes_le` | `(b: [u8]) -> BigNat` | Little-endian | same |
| `from_bytes_be_fixed` | `<N>(b: [u8]) -> Fixed<N>` | Pad/truncate to exactly `N` limbs; rejects oversize | **CT** |
| `to_bytes_be` | `(a: BigNat, len: u64) -> [u8]` | Big-endian, left-pad with zeros to `len` | leaks `len` only |
| `to_bytes_le` | `(a: BigNat, len: u64) -> [u8]` | Little-endian | same |
| `to_bytes_fixed` | `<N>(a: Fixed<N>, len: u64) -> [u8]` | Same length always | **CT** |
| `add` | `(a: BigNat, b: BigNat) -> BigNat` | a+b, normalised | no |
| `sub` | `(a: BigNat, b: BigNat) -> BigNat` | a-b; returns zero if b≥a (matches rsa_fallback today) | no |
| `add_fixed` | `<N>(a: Fixed<N>, b: Fixed<N>) -> (Fixed<N>, i64)` | Returns sum + carry-out; no allocation regrowth | **CT** |
| `sub_fixed` | `<N>(a: Fixed<N>, b: Fixed<N>) -> (Fixed<N>, i64)` | Returns diff + borrow-out | **CT** |
| `mul` | `(a: BigNat, b: BigNat) -> BigNat` | Schoolbook; pre-allocates `len_a+len_b` | no |
| `mul_lo_hi` | `<N>(a: Fixed<N>, b: Fixed<N>) -> Fixed<2N>` | Full-width product, fixed shape | **CT** |
| `mul_i64` | `(a: BigNat, n: i64) -> BigNat` | n bounded by 2^30 (for safe carry) | no |
| `div_mod` | `(a: BigNat, b: BigNat) -> (BigNat, BigNat)` | Bit-by-bit; **public values only** | no |
| `mod` | `(a: BigNat, m: BigNat) -> BigNat` | `div_mod(...).1` | no |
| `mod_exp` | `(base: BigNat, exp: BigNat, m: BigNat) -> BigNat` | Variable-time square-and-multiply; **public exponent only** | no |
| `mod_exp_ct` | `<N>(base: Fixed<N>, exp: Fixed<N>, m: Fixed<N>) -> Fixed<N>` | Montgomery ladder over Fixed<N>; constant exponent length, no early exit | **CT** |
| `mod_inv` | `(a: BigNat, m: BigNat) -> Result<BigNat, text>` | Extended Euclidean over public modulus | no |
| `gcd` | `(a: BigNat, b: BigNat) -> BigNat` | Public values only | no |
| `cmp` | `(a: BigNat, b: BigNat) -> i64` | -1/0/1 | no — branches on length |
| `cmp_fixed` | `<N>(a: Fixed<N>, b: Fixed<N>) -> i64` | Subtraction + sign extraction, no early exit | **CT** |
| `is_zero` | `(a: BigNat) -> bool` | Length-aware; not CT | no |
| `is_zero_ct` | `<N>(a: Fixed<N>) -> bool` | OR-fold all limbs through `rt_black_box`, then `== 0` | **CT** |
| `cond_swap` | `<N>(a: Fixed<N>, b: Fixed<N>, swap: i64) -> (Fixed<N>, Fixed<N>)` | Mask-based swap; `rt_black_box(swap)` once at entry | **CT** |
| `select` | `<N>(cond: i64, a: Fixed<N>, b: Fixed<N>) -> Fixed<N>` | `cond ? a : b` via mask | **CT** |

`mod_exp_pow2` from the brief collapses to `mod_exp_ct` with an exponent
that is a power-of-two BigNat — no separate function needed.

---

## 4. Constant-time guarantees

**CT contract.** A function is CT iff its control flow and memory access
trace depend only on the lengths declared in its signature, *not* on limb
values.

- All `Fixed<N>` operations are CT by construction: lengths come from `N`
  (compile-time generic), every loop runs `N` iterations, every branch
  decides on a mask.
- `rt_black_box` (already wired, `constant_time.spl`) wraps:
  - the carry/borrow output of `add_fixed`/`sub_fixed` before it feeds
    into `select`/`cond_swap` — prevents the optimiser from turning
    `select(borrow, …)` into a branch.
  - the OR-fold accumulator in `is_zero_ct`.
  - the `swap` mask in `cond_swap`.
- `BigNat` ops are **not** CT. Variable length leaks bit-length. Use only
  on public values: RSA modulus parsing, key gen primality candidates,
  `mod_inv` of a known modulus.

**Hard rule.** RSA private-key operations (sign, decrypt) and ECC scalar
operations on secret scalars **must** use `Fixed<N>` paths. The CRT
fallback in `rsa_fallback._crt_sign` is the single biggest violator today;
its port to `mod_exp_ct` is the load-bearing migration step.

---

## 5. Migration plan

Goal: move every duplicate `_bi_*` implementation onto the new bignum
without ever creating a cycle. Order is single-directional (`crypto/*`
imports `math/bignum/*`, never reverse).

| Step | File | Action | Risk |
|------|------|--------|------|
| 1 | `src/lib/common/rsa/types.spl` | **Move** verbatim (rename `_bi_` → public) into `math/bignum/{core,mul,divmod}.spl`. Smallest semantic delta — same base, same list-of-i64 shape. | low |
| 2 | `src/lib/common/rsa/modular.spl` | Re-export bignum's `mod_exp`/`gcd`/`mod_inv` thin-wrapped under existing names. Keep the file as a compat shim until §6 is gone. | low |
| 3 | `src/os/crypto/rsa_fallback.spl` | Replace the local `_bi_*` block (lines 27–275) with `use std.math.bignum`. `_bi_normalize` etc. become bignum's `core.normalize`. | low — same algorithms |
| 4 | `src/os/crypto/curve25519_bigint.spl` | **Delete** (517 lines). Its `_bi_*` is a duplicate; its FIELD_P arithmetic moves to R-C's `gf_25519.spl`, but the underlying mul/add/sub come from bignum. | medium — breaks if R-C not coordinated |
| 5 | `src/os/crypto/curve25519_bigint_wrapper.spl` | **Delete** (26 lines, just glue). | none |
| 6 | `src/os/crypto/ed25519.spl` | `_bytes_to_limbs32`/`_limbs32_to_bytes`/`_sc_sub_L` become `Fixed<8, u32>` ScalarMod helpers — but still under bignum (we accept a second small-limb shape for ed25519's `sc_reduce`, since the 21-bit/`i64` accumulators in `sc_muladd` cross the 30-bit boundary cleanly). Keep ed25519's existing kernels; only the byte<->limb edges change. | medium — `sc_muladd` is fragile |
| 7 | `src/os/crypto/ecdsa_p256.spl` | Currently FFI-only (332 lines, all `rt_ecdsa_p256_*`). When R-C adds a pure-Simple path, it consumes bignum's `Fixed<9, i64>` for mod-q reduction. | low |
| 8 | `src/os/crypto/curve25519.spl` | **Untouched on this pass.** Fe25519 5×51-bit u64 layout is GF(p)-specific (R-C). Bignum supplies only the 32-byte serialisation edges. | none |

**Cycle check.** Both `rsa/types.spl` and `curve25519_bigint.spl` declare
their own `BIGINT_BASE = 2^30` constant. After step 1 these constants live
in `math/bignum/types.spl`; step 2 makes `rsa/types.spl` a re-export; step
3+ delete the duplicates. No file ever imports from `crypto/` *into*
`math/bignum/`.

**Test gating.** Existing tests under `test/unit/crypto/` and the RSA
KAT-vector tests must pass at every step. Step 4 (delete
curve25519_bigint) requires R-C's `gf_25519.spl` to land first — flag this
as the **synchronisation point** with R-C.

---

## 6. Bootstrap impact

**No new externs required.** The design uses only existing externs:

- `rt_bytes_alloc(len: u64) -> [u8]` — already wired (B2, 2026-04-25).
- `rt_bytes_u8_at(data, idx)` / `rt_bytes_copy_into` — already wired.
- `rt_black_box(x: i64) -> i64` — already wired (B6).

Therefore **no `bootstrap-from-scratch.sh --deploy` rebuild needed** for
this work. Per `feedback_extern_bootstrap_rebuild.md`, that requirement
applies only to *new* `extern fn` declarations.

**Optional future extern (flagged, not in v1):** `rt_limb_alloc(n: u64) ->
[i64]` for O(n) zero-init of large bignum buffers. If RSA-4096 mul shows up
as a hot spot in the interpreter, this is a 1-day extern. Adding it
**would** require a full bootstrap rebuild — call it out at PR time, do
not slip it in silently.

---

## 7. Open questions for user

1. **Sign convention for egcd / mod_inv.** Today `modular.spl` uses
   `(value, is_negative)` tuples. Keep that, or introduce `BigInt` (signed
   sibling of `BigNat`) as a real type? Recommend: **keep tuples** — adding
   a signed type doubles the API surface and only egcd/Jacobi need it.
2. **Fixed<N> generic monomorphisation.** Compiler currently supports
   `<N: i64>` as a const generic for arrays — confirm with a small probe
   before step 6, since ed25519's `Fixed<8, u32>` mixes type and length
   parameters. Fallback: emit `Fixed8U32` etc. as concrete structs.
3. **Curve25519 collapse target.** The brief asks to collapse three
   curve25519 backends into one. Confirm the target is the 5×51-bit
   `curve25519.spl` (kept by R-C) and `curve25519_bigint*` are deleted, vs.
   keeping `curve25519_smalllimb.spl` (the `[u64]`-as-array variant) as a
   debug fallback.

---

## Appendix A — risks accepted

- **Bit-by-bit `_bi_mod`** is O(bit_len × len²). RSA-4096 sign is one
  `mod_exp` over a 4096-bit modulus; benchmark shows ~12 s in interpreter
  today, ~200 ms native. v1 ships with this; Barrett/Montgomery is a
  future ticket.
- **Variable-length normalize leaks bit-length** for BigNat values. Public
  values only — never on secret scalars. Enforced by code review of crypto
  call sites and by Fixed<N> being the only type accepted by
  `mod_exp_ct`/`cond_swap`/`select`.
- **No SIMD / no carryless mul.** GF(2^128) GHASH (H-4) is a separate
  crypto-side concern, not bignum's problem.

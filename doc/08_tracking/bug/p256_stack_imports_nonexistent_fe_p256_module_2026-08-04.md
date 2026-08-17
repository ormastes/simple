# The whole P-256 stack imports `std.common.math.field.fe_p256`, which was never written

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

**Status:** OPEN
**Found:** 2026-08-04

## Symptom

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache test/01_unit/os/crypto
#   FAIL test/01_unit/os/crypto/p256_spec.spl (0 passed, 6 failed, 1213ms)
#   Error: semantic: function `fe_from_bytes` not found; (x3)
```

Every example in `p256_spec.spl` fails; none of the P-256 code is reachable.

## Root cause (proven)

`src/os/crypto/p256.spl:21-28` and `src/os/crypto/ecdh_p256.spl:46-…` both open
with

```simple
use std.common.math.field.fe_p256.{
    FeP256,
    fe_zero, fe_one,
    fe_add, fe_sub,
    fe_mul, fe_sq, fe_inv,
    fe_from_bytes, fe_to_bytes,
    fe_eq
}
```

That module does not exist anywhere in the tree:

```
$ ls src/lib/common/math/field/
ls: cannot access 'src/lib/common/math/field/': No such file or directory
$ find src -name 'fe_p256*'
(no output)
$ ls src/lib/common/math/
bignum  distributions.spl  financial.spl  __init__.spl  math.spl  noise.spl
special.spl  statistics.spl
```

`src/os/crypto/` has a `p384_field.spl` (571 lines, `Fe384` over six limbs,
`fe_from_bytes` at `:181`) and a `curve25519.spl` (`fe_from_bytes` at `:289`),
but nothing for P-256. So both the ECDSA module (`p256.spl`) and the ECDH
module (`ecdh_p256.spl`) are dead: every `FeP256` type reference, every
`fe_mul`/`fe_inv`/`fe_from_bytes` call site (about 20 in `p256.spl` alone,
`:660-784`) resolves to nothing. An unresolved `use` is only a WARNING, so the
modules "load" and the failure only surfaces at the first call.

This is one instance of the known "std.* module declared but never written"
class, but it is worth its own entry because it silently disables an entire
NIST curve — P-256 ECDH and ECDSA both — that the rest of the tree imports as
if it worked.

## Why not fixed now

The missing piece is a complete constant-time field implementation modulo the
NIST P-256 prime `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`: four-limb schoolbook
multiply with the special-form reduction, modular squaring, and inversion via
the addition chain (or Fermat exponentiation). `p384_field.spl` is a workable
structural template but the reduction is prime-specific and cannot be ported
mechanically.

Writing that here would mean shipping unreviewed, unverified crypto — and this
tree already carries at least two recorded instances of a *fabricated* KAT
(ed25519, bip39) that passed review because the numbers looked plausible. A
P-256 field implementation must land with real FIPS 186-4 / RFC 5903 test
vectors transcribed from the standard and a constant-time review, which is its
own lane.

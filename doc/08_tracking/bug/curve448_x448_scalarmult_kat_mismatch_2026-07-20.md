# Curve448 (X448) scalar-mult and ECDH KAT mismatches across all RFC 7748 vectors

- **Date:** 2026-07-20
- **Area:** Curve448/X448 implementation exercised via
  `test/unit/lib/crypto/curve448_rfc7748_kat_spec.spl`
- **Severity:** high (every KAT vector in the file mismatches — near-total
  break, not an edge case).
- **Status:** FIXED 2026-11-03. Root cause: `_f448_sub` added an all-0x1FFFFFFE bias (= 2*(2^448-1), not a multiple of p); 2p needs limb 8 = 0x1FFFFFFC. Fixed in `src/os/crypto/curve448.spl`; `curve448_rfc7748_kat_spec.spl` 7/7 pass, new `curve448_field_sub_spec.spl` fails before/passes after. (was OPEN.) **Do not touch the expected vectors** — RFC 7748 §5.2/§6.2
  values are canonical.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/curve448_rfc7748_kat_spec.spl --no-session-daemon
```

```
✗ TV1: scalar 3d262fdd... × u 06fce640... → ce3e4ff9...
✗ TV2: scalar 203d4944... × u 0fbcc2f9... → 884a0257...
✗ after 1 iteration from BASE_POINT: 3f482c8a...
✗ Alice public key: x448_keygen(alice_priv)[1] == alice_pub
✗ Bob public key: x448_keygen(bob_priv)[1] == bob_pub
✗ Alice computes shared secret: x448_dh(alice_priv, bob_pub) == shared
✗ Bob computes shared secret: x448_dh(bob_priv, alice_pub) == shared
```

Every scalar-mult and ECDH example in the file fails (single-scalar-mult TV1
and TV2, the 1-iteration BASE_POINT test, and all 4 §6.2 ECDH round-trip
checks) — the failing byte arrays bear no partial resemblance to the
expected ones (unlike, e.g., the AES-256-CTR bug where a prefix matched).

## Root-cause hypothesis

Total, not partial, mismatch across every vector (single scalar-mult,
iterated scalar-mult, and full ECDH key exchange) strongly suggests a
fundamental defect in the Curve448 field arithmetic or the core X448 ladder
(e.g. `x448_keygen`/`x448_dh`'s underlying scalar-mult routine) rather than
an edge case in one code path — since ECDH failing is a direct consequence
of `x448_keygen` (itself just scalar-mult against the base point) already
being wrong. Not further localized within the field-arithmetic
implementation in this triage pass; needs a from-scratch verification of
the Curve448 field reduction / Montgomery-ladder implementation against a
reference.

## What NOT to do

Do not touch any of the RFC 7748 §5.2/§6.2 expected byte values.

## Affected specs

- `test/unit/lib/crypto/curve448_rfc7748_kat_spec.spl` (all scalar-mult and
  ECDH examples fail)

**Revalidated 2026-11-02: still plausible because OPEN. Do not touch the expected vectors — RFC 7748 §5.2/§6.2; no merged fix commit with a passing regression is cited in this doc.**

## Resolution confirmed — 2026-11-25

**Status: FIXED and verified on `release/1.0.0`.** The fix landed
2026-11-03 in commit `e079bb68500` ("fix(crypto): correct Curve448 field
subtraction bias and top carry") plus follow-up `79a47bf02cb`; both are
ancestors of `origin/release/1.0.0` (verified with
`git merge-base --is-ancestor` on 2026-11-25).

**Root cause (confirmed):** `_f448_sub` in `src/os/crypto/curve448.spl`
added an all-`0x1FFFFFFE` per-limb bias before subtracting. That bias is
`2*(2^448 - 1)`, which is **not** a multiple of p = 2^448 − 2^224 − 1, so
every subtraction returned a result off by a constant multiple of the
field, corrupting every Montgomery-ladder step. The correct bias is 2p,
whose limb 8 is `0x1FFFFFFC` (2·(2^28 − 2)) and all other limbs
`0x1FFFFFFE`. Clamping, A24 = 39081, the Goldilocks fold, and the 56-byte
little-endian encoding were all correct; the defect was solely the
subtraction bias (not a shared X25519 primitive — the Curve448 field code
is self-contained in `src/os/crypto/curve448.spl`; `src/os/crypto/x448.spl`
is a thin wrapper and `src/lib/common/crypto/typed/ctypes.spl` contains no
X448 code).

**Before evidence (2026-11-25, worktree on `release/1.0.0` with
`src/os/crypto/curve448.spl` temporarily restored to `e079bb68500~1`):**

```
SIMPLE_LIB=src bin/simple.exe test test/01_unit/lib/crypto/curve448_rfc7748_kat_spec.spl --mode=interpreter
✗ TV1 / TV2 / 1-iteration / Alice pub / Bob pub / Alice DH / Bob DH
SPEC FILE VERDICT: ... outcome=ERROR executed=7 passed=0 failed=7
Results: 7 total, 0 passed, 7 failed
```

**After evidence (2026-11-25, unmodified `release/1.0.0` tree):**

```
SIMPLE_LIB=src bin/simple.exe test test/01_unit/lib/crypto/curve448_rfc7748_kat_spec.spl --mode=interpreter
SPEC FILE VERDICT: ... outcome=OK declared>=7 executed=7 passed=7 failed=0
Results: 7 total, 7 passed, 0 failed
```

Sibling Curve448 specs run once on the same tree, both green:
`curve448_field_sub_spec.spl` (2/2) and
`curve448_field_boundaries_spec.spl` (4/4). The Ed448 KAT spec
(`ed448_rfc8032_kat_spec.spl`) exercises a separate Ed448 implementation
untouched by this fix and exceeds practical interpreter runtimes
(documented perf cliff); it was not used as a gate here.

No code change was required on 2026-11-25; this section records the
independent re-verification and closes the loop on the stale "OPEN"
revalidation note above.

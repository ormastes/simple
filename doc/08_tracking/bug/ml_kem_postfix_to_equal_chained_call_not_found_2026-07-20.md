# ML-KEM-768: postfix `.to_equal()` matcher unresolved when receiver is a chained call

- **Date:** 2026-07-20
- **Area:** SSpec matcher dispatch (test-runner), exercised via
  `test/unit/lib/crypto/ml_kem_768_kat_spec.spl`
- **Severity:** medium — blocks all algebraic-correctness assertions in this
  spec (ByteEncode/ByteDecode round-trip, NTT round-trip, NTT pointwise
  multiply, SHAKE-128 KAT); the underlying ML-KEM-768 arithmetic is
  UNVERIFIED as a result (assertions never execute).
- **Status:** OPEN.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/ml_kem_768_kat_spec.spl --no-session-daemon
```

```
ML-KEM-768 polynomial arithmetic
  ✓ ITEM-1 q is 3329
  ✓ ITEM-2 Compress_1 boundaries match FIPS 203 §4.2.1
  ✗ ITEM-3 ByteEncode_12 / ByteDecode_12 round-trip
    semantic: method 'to_equal' not found on value of type i64 in nested call context
  ✗ ITEM-4 NTT round-trip INTT(NTT(p)) == p
    semantic: method 'to_equal' not found on value of type i64 in nested call context
  ✗ ITEM-5 NTT pointwise multiply matches mod (X^256+1)
    semantic: method 'to_equal' not found on value of type i64 in nested call context

ML-KEM-768 size invariants
  ✓ ITEM-6a ek = 1184 bytes         (ml_kem_768_ek_bytes().to_equal(1184))
  ✓ ITEM-6b dk = 2400 bytes
  ✓ ITEM-6c ciphertext = 1088 bytes
  ✓ ITEM-6d shared secret = 32 bytes

FIPS 202 SHAKE-128 KAT (sanity for ML-KEM-768 sponge dependency)
  ✗ ITEM-7 SHAKE-128('') first 16 bytes
    semantic: method 'to_equal' not found on value of type i64 in nested call context

W12-A probe — postfix value.to_equal   (spec's own diagnostic scaffolding,
    labeled "DO NOT COMMIT (will be reverted)" — left untouched per
    hard-prohibition on deleting it/describe blocks)
  ✗ PROBE postfix int must FAIL
    expected 3329 to equal 99999      (intentional mismatch, resolves fine)
  ✗ PROBE postfix bare int literal must FAIL
    expected 1 to equal 99999         (intentional mismatch, resolves fine)
```

12 examples, 8 failures.

## Root-cause hypothesis

The spec uses a bare **postfix** matcher form directly on an expression,
without an `expect(...)` wrapper:

```simple
# ITEM-3 (fails):
enc.len().to_equal(384)        # receiver = enc.len() -- a CHAINED call

# ITEM-6a (passes):
ml_kem_768_ek_bytes().to_equal(1184)   # receiver = a single direct call

# W12-A probe (passes, correctly reports the intentional mismatch):
ml_kem_q().to_equal(99999)             # single direct call
(1).to_equal(99999)                    # literal
```

The spec's own "W12-A probe" section isolates the exact boundary: postfix
`.to_equal()` resolves correctly when the receiver is a **single/direct**
call or literal (`X().to_equal(Y)`), but fails with `method 'to_equal' not
found on value of type i64 in nested call context` when the receiver is
itself the result of a **prior chained method call**
(`X.foo().to_equal(Y)` — here `X.foo()` is `enc.len()` or `out.get(0)`).

This is consistent with the postfix `.to_equal()` sugar being expanded /
pattern-matched by the SSpec frontend only for simple (non-chained)
receiver expressions; a chained-call receiver falls through un-rewritten
and hits real method dispatch on the underlying primitive value (`i64`),
which has no `.to_equal` method — hence "nested call context" in the
diagnostic. Also plausibly related to the documented language limitation
"Chained methods on erased receivers" (`.claude/rules/language.md`).

## What NOT to do

- Do not delete or soften the "W12-A probe" `it` blocks (hard prohibition:
  never remove `it`/`describe` blocks). They are deliberately failing
  diagnostic scaffolding the spec author left in to pin down this exact
  bug; despite the "DO NOT COMMIT" comment, removing them is out of scope
  for a triage pass.
- Do not rewrite ITEM-3/4/5/7 to use `expect(...).to_equal(...)` instead of
  the postfix form purely to reach green — that changes what's being
  tested (whether postfix-chained matcher dispatch works) and would mask
  the real defect rather than fix it.
- The underlying ML-KEM-768 ByteEncode/NTT/SHAKE-128 arithmetic correctness
  is UNKNOWN — these assertions have never actually executed.

## Affected specs

- `test/unit/lib/crypto/ml_kem_768_kat_spec.spl` (ITEM-3, ITEM-4, ITEM-5,
  ITEM-7 — 4 of 8 failures directly; the 2 W12-A probe failures are
  intentional self-diagnostic, not bugs)

## Triage 2026-11-25 (P2 ledger sweep, Windows worktree)

The affected spec no longer exercises the failing form. It now lives at
`test/01_unit/lib/crypto/ml_kem_768_kat_spec.spl` and was rewritten to the
`expect(...).to_equal(...)` form by `9c5595b146d` ("fix(test): repair
mechanical unit-spec failures (crypto, engine)") — e.g. ITEM-3 is now
`expect(enc.len()).to_equal(384)`. The W12-A postfix probe blocks are gone
from the current spec. So the four reported failures no longer exist in the
suite in that shape.

Note, per this record's own "What NOT to do" section: that rewrite is exactly
the masking shape the section warned about (it changes what is tested). It
was done by another lane, not this sweep. Consequence: whether postfix
`.to_equal()` on a CHAINED receiver (`x.f().to_equal(y)`) resolves is now
untested anywhere in the tree, and the underlying dispatch defect is neither
fixed nor disproven — only unexercised.

The defect is also unverifiable at this HEAD: `bin/simple.exe test` fails
repo-wide because the pinned tracked seed rejects `@representation_boundary`
(added by `cfd89933699`) inside the test runner itself, so no spec — postfix
probe included — can run. Status stays OPEN for the postfix-chained dispatch
defect itself; the concrete next step is a minimal postfix-form probe spec
run once the tracked seed accepts the decorator or a self-hosted binary is
deployed. No source change made by this sweep.

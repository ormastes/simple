# Ed25519 `ed_scalar_mul`/`ed_scalar_mul_basepoint` regressed to a branch-on-secret-bit form (constant-time regression)

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

- **Date:** 2026-07-20
- **Area:** `src/os/crypto/ed25519_ops.spl` (pure-Simple Ed25519 point arithmetic)
- **Severity:** high (timing side-channel on the secret-scalar code path — the
  exact class of bug previously fixed and guarded against).
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  full evidence for a follow-up implementation session.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/ed25519_ct_property_spec.spl --no-session-daemon
```

```
✗ structural CT: ed_scalar_mul body contains no `if` branch on a scalar bit
```//1 example failure inside "Ed25519 Constant-Time Property Spec"; 4 other
examples in the same file pass.

## Repro / evidence

The spec (`test/unit/lib/crypto/ed25519_ct_property_spec.spl:116-144`) reads
the *live source* of `fn ed_scalar_mul` from `src/os/crypto/ed25519.spl` and
asserts the body contains none of the old leaky fingerprints
(`if ((byte_val...`, `if scalar[...`, `) & 1) == 1`) and does contain a call
to `ed_point_cselect` (the constant-time select helper).

Two independent problems, both confirmed by direct source inspection:

1. **Stale read path.** `fn ed_scalar_mul` no longer lives in
   `src/os/crypto/ed25519.spl` — it was refactored out into
   `src/os/crypto/ed25519_ops.spl` (imported back into `ed25519.spl` via
   `use os.crypto.ed25519_ops.{... ed_scalar_mul ...}`, `ed25519.spl:19`).
   `rt_file_read_text("src/os/crypto/ed25519.spl")` therefore never finds the
   function header at all.

2. **The regression the check exists to catch is real.** Even reading the
   *correct* current file (`src/os/crypto/ed25519_ops.spl:862-887`), the
   actual body is:

   ```
   fn ed_scalar_mul(scalar: [u8], p: EdPoint) -> EdPoint:
       """Constant-time scalar multiplication: ... XOR-mask cselect ..."""
       var result = ed_point_identity()
       var base = p
       var seen_nonzero = false
       var bit_idx: u64 = 0
       while bit_idx < 256:
           if _ed_scalar_bit(scalar, bit_idx) == 1:
               if seen_nonzero:
                   result = ed_point_add(result, base)
               else:
                   result = base
                   seen_nonzero = true
           base = ed_point_double(base)
           bit_idx = bit_idx + 1
       result
   ```

   This branches directly on the secret scalar bit
   (`if _ed_scalar_bit(scalar, bit_idx) == 1:`), with different work done
   (an `ed_point_add` call, or not) depending on that bit — a textbook
   timing side-channel. The docstring's claim of "XOR-mask cselect" /
   "16-entry table" does not match the code beneath it.

   `ed_point_cselect` **is defined** (`ed25519_ops.spl:422`) but is **never
   called anywhere in the file** (`grep -n ed_point_cselect
   src/os/crypto/ed25519_ops.spl` only matches its own definition and the
   unrelated `_small_ed_point_cselect`). The constant-time helper exists as
   dead code while the actual hot path bypasses it.

   The sibling function `ed_scalar_mul_basepoint` (used for public-key
   derivation) delegates to `ed_scalar_mul_basepoint_simple`
   (`ed25519_ops.spl:938`), which has the **identical** branch-on-secret-bit
   pattern.

## Root-cause hypothesis

Both `ed_scalar_mul` and `ed_scalar_mul_basepoint_simple` were likely
rewritten (or reverted to an earlier draft) during the file split from
`ed25519.spl` into `ed25519_ops.spl`, losing the cselect-based constant-time
form that the original fix for
`doc/08_tracking/bug/ed25519_scalar_mul_not_constant_time_2026-05-01.md`
(referenced in the function's own docstring) put in place. No claim is made
here about exploitability or which commit introduced the regression — that
needs separate investigation (`git log` on this path returned only unrelated
sync-noise commits in this session, not attributable history).

## What NOT to do

- Do NOT "fix" the spec by pointing `rt_file_read_text` at
  `src/os/crypto/ed25519_ops.spl` — the structural assertion would still
  correctly fail (see problem #2 above), so this is GENUINE-BUG, not
  STALE-TEST.
- Do NOT touch the KAT expectation or weaken the `if`-branch assertions.

## Possibly related

`ed25519_rfc8032_spec.spl`'s `T_SHA_ABC` vector fails on the *derived public
key* (see `doc/08_tracking/bug/ed25519_rfc8032_t_sha_abc_pubkey_mismatch_2026-07-20.md`),
and public-key derivation goes through this same `ed_scalar_mul_basepoint`
path. T3 (a different vector) passes both sign and verify, so the two bugs
are not obviously the same fault — but both touch this code path and a
future fix session should check whether resolving the CT regression also
resolves the T_SHA_ABC value mismatch, or whether they are independent.

## Affected specs

- `test/unit/lib/crypto/ed25519_ct_property_spec.spl`

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STILL-OPEN (corrected line refs)

Both functions still exist in `src/os/crypto/ed25519_ops.spl`:

```
966: fn ed_scalar_mul_basepoint_simple(scalar: [u8]) -> EdPoint:
976: fn ed_scalar_mul_basepoint(scalar: [u8]) -> EdPoint:
```

No constant-time selection primitive is present (`grep -n "ct_select\|conditional_select"`
returns nothing in this file). The cited line 938 sits inside the `_simple`
body, which also still carries per-byte `serial_println("[ed25519-scalar] byte8")`
debug tracing. Use :966 / :976 as the reference points.
NOT PROVEN: that the constant-time property actually regresses at runtime — that
needs execution/timing, which this triage did not perform.

## 2026-08-20 canonical common-verifier repair (static only)

At source level, the pure-Simple owner used by release/evidence verification
now has fixed-work secret-scalar paths.  Its public `ed25519.spl` facade uses a
fixed 64-window schedule, four doublings and one addition per window, a full
16-entry table scan, and XOR-mask point selection.  A follow-up review found
additional secret-dependent branches in scalar reduction and multiplication;
`ed25519_scalar.spl` now performs every conditional subtraction and multiply
accumulation through mask selection over fixed loops.  Dormant branch-indexed
cached selectors were removed.  Field arithmetic lives in the cohesive
`ed25519_field.spl` module.  The same repair adds strict canonical point
decoding, square-root revalidation, negative-zero rejection, `S < L`,
prime-subgroup membership, and small-order rejection.

The original row names `src/os/crypto/ed25519_ops.spl`; that separate owner was
outside this bounded repair and remains OPEN.  The common-owner fix is also
STATIC-ONLY: no valid deployed self-hosted Simple runtime was available.  The
fixed-work statement above describes source control flow only; it is not an
executable constant-time or compiler-codegen proof.  Neither the RFC signing
KAT nor timing/codegen evidence has run yet.  Do not enable evidence signature
admission until the focused common-owner spec passes under the self-hosted
runtime and the native code path is reviewed.

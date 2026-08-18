# Adding an unused function changes the results of unrelated examples (interpreter, silent wrong result)

## Status

STILL-OPEN — P1, but **NO LONGER REPRODUCIBLE** on the seed rebuilt
2026-08-17 12:58:51 UTC. The A/B pair from the Reproduction section was
re-run byte-for-byte on that binary and produced **identical** results
(14 total, 13 passed, 1 failed — the same single known fixture defect in
both). The five-example flip is gone. Kept OPEN rather than closed FIXED
because the root cause was never located and no source change was made
here, so this is an observation that the symptom vanished under a rebuilt
binary, not a demonstrated fix. See the 2026-08-17 verification section.

## Severity rationale

This is a **silent wrong result**, the highest-priority class in the current
sweep. Nothing crashes, nothing warns, the exit code is a normal test failure,
and the spec reports confident PASS/FAIL verdicts that are simply **wrong**.
Worse, it corrupts *other* specs' verdicts in both directions: it manufactured a
false P1 authentication-bypass report, and it can equally turn a genuine failure
green.

## Summary

Inserting a single trivial, **unused** function into a spec module changes the
observable results of examples that do not call it, do not reference it, and are
defined elsewhere in the file. Five examples flipped from FAIL to PASS with no
change to any code path they execute.

## Reproduction

Anchor: `test/unit/lib/crypto/paseto_v4_kat_spec.spl` at blob `79ad784175ab~1`
(the version before the tamper-fixture repair).

```sh
git show 79ad784175ab~1:test/unit/lib/crypto/paseto_v4_kat_spec.spl > /tmp/base.spl

# (A) baseline, unmodified
sh scripts/resource/test-slot.shs bin/simple test <base.spl copy> --no-session-daemon --timeout 2400

# (B) identical file, plus ONE unused function inserted after line 183
awk 'NR==183{print; print ""; print "fn _zz_probe_unused() -> i64:"; print "    1"; next}1' \
    /tmp/base.spl > <variant copy>
sh scripts/resource/test-slot.shs bin/simple test <variant copy> --no-session-daemon --timeout 2400
```

### (A) baseline

```
Results: 14 total, 8 passed, 6 failed
  ✗ 4-E-1 decrypts to original payload
  ✗ 4-E-3 decrypts to original payload
  ✗ tampered ciphertext is rejected by BLAKE2b MAC
  ✗ correct footer allows decryption
  ✗ 4-S-1 verifies and payload matches
  ✗ tampered token signature is rejected
```

### (B) same file + one unused function

```
Results: 14 total, 13 passed, 1 failed
  ✓ 4-E-1 decrypts to original payload
  ✓ 4-E-3 decrypts to original payload
  ✓ tampered ciphertext is rejected by BLAKE2b MAC
  ✓ correct footer allows decryption
  ✓ 4-S-1 verifies and payload matches
  ✗ tampered token signature is rejected      <- unrelated, genuine fixture defect
```

**Five examples flipped.** The inserted function is never called and never
referenced. The example count is unchanged (14 in both). The only difference is
module layout: one extra declaration, and every subsequent line shifted.

The single remaining failure in (B) is a real and independent defect in the
spec's own fixture (a "tamper" that substituted `"X"` at an index that was
already `"X"`, so the token was unmodified) — see
`paseto_v4_tampered_token_signature_accepted_2026-07-20.md`. Its persistence
across both variants is a useful control: it shows (B) is not uniformly
"everything passes now".

## What has been ruled out

- **Host degradation / earlyoom.** Both runs above were on a quiet host via
  `scripts/resource/test-slot.shs`. The baseline RED is deterministic and has
  been observed on a loaded host and a quiet one alike.
- **The session daemon.** The repaired spec is 16/16 GREEN with the daemon
  ENABLED and DISABLED; the daemon changes nothing.
- **Long string literals bound to a local `val`, duplicated in one module.**
  Directly probed and correct — `test/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.spl`
  is 7/7 GREEN. This shape is NOT the trigger.
- **Anything cryptographic.** All encrypt/sign KATs reproduce their RFC vectors
  byte-exactly in every variant. Only consumption paths are affected, and they
  are fixed by an unrelated layout change, so PASETO itself is not implicated.

## Observations that constrain the cause

Grouping baseline failures by helper rather than by name:

| example | helper | (A) | (B) |
|---|---|---|---|
| 4-E-1 / 4-E-3 decrypt to payload | `_local_payload` | ✗ | ✓ |
| tampered ciphertext rejected | `_local_ok` | ✗ | ✓ |
| correct footer allows decryption | `_local_ok_with_footer` | ✗ | ✓ |
| **wrong footer is rejected** | **`_local_ok_with_footer`** | **✓** | ✓ |
| 4-S-1 verifies and payload matches | `_public_payload` | ✗ | ✓ |
| v3.local / v3.public rejected | *inline `match`, no helper* | ✓ | ✓ |
| all encrypt / sign KATs | *no decrypt/verify* | ✓ | ✓ |

Two constraints for whoever picks this up:

1. The **same** helper (`_local_ok_with_footer`) both passes and fails in (A)
   depending on which example calls it — so this is not "one helper is broken".
2. The two consumption examples that bypass the `_*_ok` wrappers with an inline
   `match` pass in (A). The affected path involves calling through a wrapper
   helper that pattern-matches a `Result`-shaped enum and returns a `bool`.

Whether the trigger is declaration **count**, declaration **order**, or absolute
**line offset** is not yet distinguished — the `awk` insertion changed all three
at once. That is the next bisect: insert the same function at a different
position, and separately insert a blank-line block with no declaration.

## Impact

Any spec in the tree may be silently affected; the corruption is invisible
because examples simply return wrong answers. This mechanism can:

- turn a real defect green (a spec "passes" while the code is broken), and
- turn correct code red (what happened here — it produced a plausible,
  security-shaped false P1 that survived a source review of the verifier).

It also means **an edit that appears to fix a spec may only have perturbed the
module layout.** Any "fix" verified solely by a spec flipping to green in the
same file is suspect until this is resolved.

## Scope / ownership

Root cause is in the interpreter (`src/compiler_rust/**`), outside the test
lane's file scope. Filed as **diagnosis only** — no source change made.

## Verification 2026-08-17 (re-run of the exact A/B pair)

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
size 59537240, mtime 2026-08-17 12:58:51 UTC (Rust seed, rebuilt 2026-08-17).
Host load average at start: 16.64.

Variants reconstructed exactly as the Reproduction section specifies:

```sh
S=<scratchpad>
git show 79ad784175ab~1:test/unit/lib/crypto/paseto_v4_kat_spec.spl > $S/base_spec.spl   # 345 lines
cp $S/base_spec.spl $S/A/paseto_v4_kat_spec.spl
awk 'NR==183{print; print ""; print "fn _zz_probe_unused() -> i64:"; print "    1"; next}1' \
    $S/base_spec.spl > $S/B/paseto_v4_kat_spec.spl                                       # 348 lines
```

Insertion confirmed in place (B lines 184-187, an unused `fn _zz_probe_unused`
between `_decrypt_4e3` and `_tampered_local_ok`).

Commands and exact verdicts:

```
$ bin/simple test $S/A/paseto_v4_kat_spec.spl --no-session-daemon --timeout 2400
EXIT=1
Results: 14 total, 13 passed, 1 failed
  ✗ tampered token signature is rejected

$ bin/simple test $S/B/paseto_v4_kat_spec.spl --no-session-daemon --timeout 2400
EXIT=1
Results: 14 total, 13 passed, 1 failed
  ✗ tampered token signature is rejected
```

**A and B are now identical**, down to the identity of the single failing
example. The recorded baseline (A) of `14 total, 8 passed, 6 failed` did not
reproduce; A now matches what the record documented only for B. The five
examples that previously flipped (`4-E-1`/`4-E-3 decrypts to original payload`,
`tampered ciphertext is rejected by BLAKE2b MAC`, `correct footer allows
decryption`, `4-S-1 verifies and payload matches`) pass in **both** variants.

The one remaining failure is the independently-filed fixture defect
(`paseto_v4_tampered_token_signature_accepted_2026-07-20.md`), unchanged and
present in both — the same control the original record used, and it still
shows this is not a uniform "everything passes now".

No source change was made for this record. The interpreter root cause was never
localized to a `src/compiler_rust/**` file:line, so this is recorded as a
symptom that no longer manifests on the current seed, not as a fix. The next
bisect the record proposes (separating declaration count / order / line offset)
cannot be run until a binary that reproduces the baseline RED is identified.

## Related

- `paseto_v4_tampered_token_signature_accepted_2026-07-20.md` — the anchor,
  whose P1 verdict is blocked on this.
- `shellout_specs_target_refusing_production_wrapper_2026-08-17.md` — a sibling
  in kind: test infrastructure producing plausible, defect-shaped false REDs.

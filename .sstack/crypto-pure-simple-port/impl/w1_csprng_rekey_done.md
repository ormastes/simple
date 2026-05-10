# W-1 — CSPRNG rekey silent noop fix (B-CSPRNG-REKEY-NOOP)

**Wave:** 3
**Track:** crypto-pure-simple-port
**Status:** DONE 2026-04-26

## Deliverables

- **Fix:** `src/os/crypto/random.spl` — extracted `_csprng_mix_seed_into_key`
  (pure), `_csprng_install_seed_bytes` (init path), and
  `_csprng_xor_in_seed_bytes` (reseed path). All cross-`g_csprng` writes
  are wholesale `g_csprng.<field> = expr`, never `g_csprng.<field>[i] = x`.
  - md5: `160f6dd8bcc12486490ed8503210f18f`
- **Regression spec:** `test/unit/os/crypto/random_rekey_persistence_spec.spl`
  — 4 tests, exercises the pure helper.
  - md5: `d2d77c49a45085a5f5411ddb69a0e32c`
  - Run: `bin/simple test/unit/os/crypto/random_rekey_persistence_spec.spl`
  - Result: `4 examples, 0 failures`
- **Bug doc:** `doc/08_tracking/bug/bug_csprng_rekey_silent_noop_2026-04-26.md`
  — RESOLVED with fix details, audit, CT discipline note, atomicity note.

## Audit

Searched `src/os/crypto/random.spl` for `g_csprng.<field>[i] = x` index-assign
sites. None remain (only doc-comment mentions of the old bug pattern). Other
`g_csprng.<scalar> = x` and `g_csprng.<field> = <whole_array>` assignments
are unaffected by the bug — they were already in the works-pattern.

## Verification

- Direct invocation: `bin/simple test/unit/os/crypto/random_rekey_persistence_spec.spl`
  → `4 examples, 0 failures`.
- Deliberate-fail probe: flipped `expect(all_equal).to_equal(true)` to
  `to_equal(false)` in test #4. Runner reported `4 examples, 1 failure`
  with one red. Reverted; md5 returned to
  `d2d77c49a45085a5f5411ddb69a0e32c`. Runner is executing assertions
  correctly.
- Neighbor: `test/unit/os/crypto/rsa_contract_parity_spec.spl` — already
  red on a pre-existing unrelated `str.to_bytes()` issue. Not regressed
  by this change.

## Adjacent findings (out of scope)

1. `random_bytes` always returns soft-RNG bytes via the early-return at
   line 301; the CSPRNG path is unreachable from the public API. Logged
   as a follow-up in the bug doc.
2. The interpreter additionally throws `variable g_csprng not found`
   when cross-module function calls attempt module-global writes
   (`g_csprng.<field> = expr`). This is broader than the brief described
   and means the regression spec can only test the **pure** helper
   `_csprng_mix_seed_into_key`, not the full `_csprng_xor_in_seed_bytes`
   path. Belongs to W-23's lane (interpreter fixes).

## Advisor checkpoints

- **Pre-write:** advisor flagged that the bug docs at the referenced
  paths didn't exist (treat as create-not-update); pointed out the test
  needed to be reframed away from "known seed via init+reseed" because
  there is no software-seed API and `rt_rdrand` isn't available in the
  interpreter; identified the `_csprng_install_seed_bytes` /
  `_csprng_xor_in_seed_bytes` refactor shape.
- **Mid-task:** when the cross-module-write `g_csprng not found` error
  appeared, advisor's pre-emptive fallback ("if cross-module-write path
  is broken, ship the fix + audit + bug doc + done note, document the
  block, don't synthesize a passing test that doesn't exercise the
  fix") landed exactly. Pivoted to a pure-helper testable surface
  rather than fabricating a green that masked the limitation.

## Files modified

- `src/os/crypto/random.spl`

## Files created

- `test/unit/os/crypto/random_rekey_persistence_spec.spl`
- `doc/08_tracking/bug/bug_csprng_rekey_silent_noop_2026-04-26.md`
- `.sstack/crypto-pure-simple-port/impl/w1_csprng_rekey_done.md` (this file)

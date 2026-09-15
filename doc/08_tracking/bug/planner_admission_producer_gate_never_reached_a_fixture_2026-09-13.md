# The planner-admission-v2 producer gate died before its first fixture (macOS, 2026-09-13)

- Status: FIXED (2026-09-13) for the four defects below; see "Still open".
- Area: bootstrap Stage 2 -> Stage 3 handoff; planner admission v2 producer
- Found by: macOS lane F74, re-walking site 20
  (`stage3_resume_receipt_chain_unreachable_from_seed_producer_2026-09-13.md`)
  and its root record
  (`bootstrap_admission_v2_circular_and_cannot_express_imported_parent_2026-08-18.md`).

## Correction to the premise

Both records say "nothing in the repo ever WRITES the two receipts the gate
reads". That is no longer true, and the producers are not missing:

| artifact | producer | wired at |
|---|---|---|
| `admission.env` (`simple-bootstrap-stage2-admission-v2`, `status=admitted`) | `bootstrap_stage3_write_stage2_admission_receipt` (`scripts/check/lib/bootstrap-stage3/sanity.shs:571`) | `scripts/bootstrap/bootstrap-from-scratch.sh:3188` |
| `stage2-sanity.receipt` + `stage2-provenance.receipt` (the two parent receipts the planner producer reads) | `scripts/bootstrap/publish-stage2-parent-receipts.shs` | `scripts/bootstrap/bootstrap-from-scratch.sh:3226`, trust-root lane only |
| the planner receipt itself (`--bootstrap-receipt`) | `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs` | operator-invoked; **not auto-invoked** |

What was actually broken is that the producer's own fail-closed gate,
`scripts/check/check-bootstrap-planner-admission-producer.shs`, **never reached
a single fixture assertion**, so nothing had ever exercised the producer end to
end on this host. Its verdict was
`FAIL — could not create fixture Stage-2 admission`.

## The four defects, in the order they fire

1. **`SIMPLE_ABI_POLICY` unset kills every fixture.**
   `bootstrap_stage3_write_stage2_admission_receipt` refuses to write a receipt
   when the ABI policy is unset (`sanity.shs:592-598`) — correct, fail-closed.
   `bootstrap-from-scratch.sh:1222` exports it, but the gate is invoked
   standalone (by `produce-…--selftest` and by the gate manifest) with nothing
   exporting it, so fixture construction died before any producer assertion ran.
   Fixed: the harness defaults to `v1` (its fixtures are v1 by construction) and
   an explicit value still wins.

2. **BSD `wc -c` right-padding on the WRITING side.**
   The fixture wrote `bytes_captured="$(wc -c <log)"`, which on macOS is
   `"      20"`. The verifier requires `^[0-9]+$`, so every fixture probe was
   rejected `bounded-nonnegative-syntax`. `sanity.shs` already carries `$(( ))`
   normalisation on the READING side, with a comment about exactly this trap;
   the fixture writer was never given the same treatment. Fixed with `$(( ))`.

3. **The producer refused its own fixture: ambient storage root vs `--root`.**
   `produce-bootstrap-planner-admission-v2.shs` preset its bootstrap output to
   `$SIMPLE_BOOTSTRAP_BUILD_ROOT`, which centralized storage keys to the REAL
   worktree. Every `--root=<fixture>` invocation — i.e. the whole selftest —
   then failed `bootstrap-output-outside-allowlisted-root`, because the storage
   root is not under the fixture's `build/`. Fixed by resolving the default
   AFTER argv parsing: ambient storage for the real root, `<root>/build/bootstrap`
   otherwise. Live behaviour on the real worktree is unchanged.

4. **A negative fixture was unsound (POSIX prefix-assignment leak).**
   `bootstrap_planner_v2_verify` is a shell FUNCTION, so `VAR=x func` persists
   in the shell after the call. The positive external-output case leaked
   `SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT` into the negative case beneath it,
   which then verified and reported
   `external-output receipt verified without its explicit allowlist` — a failure
   of the fixture, not of the guard. Fixed: positive case in a subshell,
   variable explicitly `unset` before the negative assertion.

## Result

`sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs --selftest`
-> `PASS — 13 fixture(s) checked` (rc 0), on macOS aarch64, where it had never
passed. `scripts/check/check-stage2-parent-receipt-candidate-binding.shs`
-> `PASS — 3 check(s) run, 0 failed`.

No guard was weakened: every negative fixture still refuses, and defect 4 made
one of them STRICTER (it had been vacuously passing its positive twin's leak).

## Still open

- **Site 20's operational gap is narrowed, not closed.** Nothing auto-invokes
  `produce-bootstrap-planner-admission-v2.shs` after a Stage 2 admission, so
  `--resume-stage3-from-admitted` and a continuous `--full-bootstrap` still exit
  64 `reason-receipt-required` unless the operator runs the producer and passes
  `--bootstrap-receipt=`. The pieces now all exist and the producer gate is
  green; the wiring is the remaining work.
- `scripts/check/check-bootstrap-reason-receipt-guard.shs` fails on this host
  with `FAIL: None receipt did not return the canonical diagnostic`. Measured
  cause: the guard drives `bootstrap-from-scratch.sh` and greps its combined
  output for `bootstrap-policy-error: malformed-or-untrusted-planner-admission-v2`.
  Replaying the guard's exact `reason=none` invocation by hand, the run is still
  REFUSED (rc 1) — the control holds — but the only line on stdout/stderr is

  ```
  bootstrap-scheduler-error: stage-engine-failed; evidence: <output>/scheduler/bootstrap-<ts>/failure-manifest.env
  ```

  i.e. a scheduler wrapper now captures the stage engine's diagnostic into an
  evidence manifest instead of passing it through, so the text the guard pins
  never reaches the caller. Not touched here, and not on the path of this
  change: the diff is confined to `produce-bootstrap-planner-admission-v2.shs`
  and its own gate, neither of which this guard invokes. Filed as a separate
  concern for whoever owns the scheduler's diagnostic passthrough.

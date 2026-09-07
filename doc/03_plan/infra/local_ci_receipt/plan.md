# Plan — local CI receipt and signing

Status: in progress, 2026-09-06. Target `origin/main` `4699194f81e`.
Research: `doc/01_research/infra/local_ci_receipt/local_ci_receipt_and_signing_2026-09-06.md`.
Design: `doc/05_design/infra/local_ci_receipt/design.md` — that document is the specification;
this one is only the order of work and the bar each step must clear.

## Why — the required check cannot complete, measured

`main` is not branch-protected; enforcement is ruleset `spipe-vcs-v3-main`, which requires exactly two
contexts: `Code Idiom & Structural Ratchet Gates` (produced by `repo-hygiene.yml`) and
`SPipe Self Review Admission`. Every other job a PR triggers is optional.

The required idiom context **never succeeds on a pull request**. Last 60 runs of `repo-hygiene.yml`,
split by event (measured 2026-09-06):

| event | outcome | count |
|---|---|---|
| pull_request | cancelled | 31 |
| pull_request | queued, never started | 24 |
| pull_request | failure | 4 |
| push | failure | 1 |

Zero successes. **Correction to an earlier reading of this data:** the cancellations are not main-push runs
cancelling each other — 59 of the 60 runs are `pull_request`, and a PR run groups on `refs/pull/N/merge`,
which main moving does not disturb. The actual mechanism is a death spiral between two repo policies:

1. The ruleset requires branches to be up to date, so a PR must rebase whenever main advances — measured at
   162 commits/24 h on main, roughly one every 8.9 min.
2. Each rebase force-pushes the PR head, which fires `synchronize`, which starts a new run and
   `cancel-in-progress: true` (`repo-hygiene.yml:10-12`) kills the in-flight one.
3. Queue depth is 322 repo-wide against 5 in progress; the one success anywhere in recent history
   (run `33716483100`, 2026-09-03) waited **2112 s queued** for **172 s of execution** — 92% queue.

The queue wait (~35 min) is longer than the rebase interval (~9 min), so a run is cancelled and restarted
before it is ever scheduled. It is not slow; it is unreachable.

**This is why the concurrency setting is NOT the fix, and why the receipt is.** Setting
`cancel-in-progress: false` would let runs complete but pile up stale runs against an already-saturated
queue. The only thing that closes the loop is a required-context run short enough to finish inside the
window between two rebases — the ~60 s `sanity` path — combined with a receipt bound to the jj **change-id**,
which by construction survives the rebase that invalidates everything else. Judge the work against that bar.

## What is deliberately NOT being built

- No new CI system. The manifest (`config/check/must_check_gates.sdn`), the ledger
  (`doc/08_tracking/check/must_check_db.sdn`, `simple.must-check-ledger/v3`) and
  `validate_ledger_text()`'s manifest-ledger cross-check already exist and are reused.
- No new crypto stack. `ssh-keygen -Y sign|verify` (sshsig) only. The pure-Simple twin over
  `src/lib/common/crypto/ed25519.spl` is future work, blocked on a CLI binary being deployed to CI,
  and is recorded as a TODO rather than built.
- No change to what the gates themselves check. This work changes WHERE and WHETHER they run, never
  their verdicts.

## Phases

### P1 — Signer and verifier (in progress)
`scripts/check/sign-local-ci-receipt.shs`, `scripts/check/verify-local-ci-receipt.shs`,
`config/check/ci_receipt_allowed_signers`.
Done when: `--selftest` passes on both and is fatal and runs before every scan; fixtures cover valid,
tampered payload, unknown signer, tree mismatch, stale manifest, missing row id, non-pass row, absent
receipt (0 verified => caller ERROR), byte-identical canonical serialization across two runs, change-ids
matching with a differing tree producing the rebase-distinguishing verdict, and a plain-git commit with no
`change-id` header failing as unbindable. Exit status is read into a variable on the line after the
command, never through a pipe. `ssh-keygen -Y verify` exits **255** on tamper, not 1 — pinned by fixture.

### P2 — Manifest and readers (in progress)
Columns `|id, tier, push_blocking, mode, command, ci_job, inputs, description|`.
`ci_job` maps a row to the CI job that may skip it; `inputs` carries the path set that `escalate` intersects
against the rebase diff — a `ci` tier alone cannot express that second thing, which is why the column form
was taken despite its wider blast radius.
Done when: `src/app/sj/gate_manifest.spl` (`:61` `fields.len() != 6`, `:66` tier allowlist) accepts the new
shape; `validate_ledger_text`'s awk and its selftest move together; `test/01_unit/scripts/must_check_tiering_test.shs`
passes; `sh scripts/check/check-guard-wiring.shs` is green — a manifest row without a byte-matching dispatch
case hits the fail-closed `*)` arm and blocks every push.

### P3 — CI modes (in progress)
`repo-hygiene.yml` consults a verified receipt first.

| binding | mode | what runs | budget |
|---|---|---|---|
| change-ids match, tree matches | `sanity` | receipt verify + conflict-tree + conflict-markers + tree-size | <= 60 s |
| change-ids match, tree differs | `escalate` | sanity set, then only gates whose `inputs` intersect the changed paths | bounded by the diff |
| change-id missing / differs / anything undecidable | `full` | every gate, as today | unchanged |

Done when: the mode and its reason are emitted as a greppable log line; every undecidable input demonstrably
lands in `full`; the allowed-signers file, the verifier and the skip logic are read from BASE via
`pull_request_target`, never from the PR head.

**The trap this phase must not fall into.** A `needs:`/`if:` job gate reports *skipped*, which rulesets treat
as passing only by convention, and the obvious positive condition is fail-OPEN in the landing state: with the
kill-switch variable unset, `mode` is `''`, every gate step skips, and the job goes green with zero gates run.
The design mandates the negated per-step form plus an always-exit-0 wrapper coercing anything not explicitly
`sanity`/`escalate` to `full`. Any implementation that cannot demonstrate the unset-variable case running the
full gates is rejected.

### P4 — Acceptance spec
A runnable, device-free spec pinning: fail-closed on each invalid input class, the three-mode decision table,
and the unset-variable fail-open case above.

### P5 — Land
Detached worktree -> PR. LLM wiki entries refreshed in the same change
(`doc/00_llm_process/feature_expert/`, `layer_expert/`). No bootstrap at any point.

## Open items carried, not hidden

1. **Trust class.** A dev-key signature proves WHO produced the receipt, not THAT the gates ran — the same
   class as `review-admission.yml`'s `self_attestation`, whose own input description reads "this is not
   independent authentication". The existing `check-external-must-check-receipt.shs` has a stronger idea,
   a `producer_id != reviewer_key_id` independence check, which a self-signed local receipt cannot satisfy.
   Adopt it if a second signer ever exists; until then this is a known ceiling, not an oversight.
2. **`escalate` degrades to `full` when the attested tree cannot be materialized** on the runner. Stated in
   the design; the optional fix is a non-identity `attested_commit` fetch hint.
3. **Input M relaxed** from `manifest_sha` blob equality to "BASE `ci` rows == TESTED `ci` rows", because
   blob equality is not implementable when the attested blob is unreachable, and would force `full` whenever
   any unrelated push/bootstrap row lands. `manifest_sha` stays in the signed payload for audit.
4. **Coverage honesty.** The idiom job runs 27 guard scripts; exactly 1 is in the manifest today, and they do
   not share a verdict grammar (`check-cpu-hotloop-idiom.shs` prints `cpu_lane_hotloop_ok=true`), so receipt
   rows key on exit status. The receipt must claim coverage only of rows it actually ran. Claimed-but-unrun
   coverage is the one defect that makes this feature worse than no feature.
5. **Pre-existing, filed separately, not fixed here:** `check-push-must-pass.shs:88-89` (`fingerprint_rev`)
   reads `$?` after a pipeline — the false-green pattern the repo rules forbid. `repo-hygiene.yml:69,76,83,89`
   lack the `if: ${{ !cancelled() }}` the file's own comment at `:48` claims every gate carries.
   `.github/` is outside the 8-root `source_fingerprint`, so only the receipt's `tree` binding detects a
   workflow edit.

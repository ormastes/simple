# Stage 4 cannot continue from an admitted resumed Stage 3

## Status

FIXED (source and sabotage contract). Live execution evidence remains pending
until an admitted Stage 3 lane and planner receipt are available; no Stage 3 or
Stage 4 build was launched without those authorities.

## Required repair

Add `--resume-stage4-from-admitted=<output>` to the canonical bootstrap wrapper.
It must require a planner-authored `//bootstrap:stage4` typed-reason receipt,
validate the existing Stage 3 candidate and provenance manifest, acquire the
output lock, bind a continuation-lock receipt without mutating Stage 2/3, then
enter the existing Stage 4, essential-tools, provenance, and deployment gates.

The candidate repair is `scripts/bootstrap/resume-stage4-from-admitted.sh`, sourced by
the canonical wrapper only after receipt validation and portable output-lock
acquisition. `SimpleBootstrapStage4ContinuationV1` binds the planner receipt,
Stage 3 manifest/candidate, current continuation lock, and immutable snapshot.

## Acceptance

- Stage 2 and Stage 3 candidate hashes are unchanged before/after continuation.
- The Stage 3 provenance verifier passes before any Stage 4 process starts.
- `full/x86_64-unknown-linux-gnu/simple` and adjacent provenance are produced.
- Candidate validity, `-c` smoke, source-check smoke, redeploy gate, and all
  essential-tools receipts pass.
- The deployed candidate hash equals the full candidate and
  `bin/release/x86_64-unknown-linux-gnu/bootstrap-deploy-receipt.env` records
  `schema=bootstrap-deploy-receipt-v1` and `deployment_status=pass`.
- No Rust seed or fallback row is accepted as Stage 4 evidence.

## Unblock command shape

After implementation and an admitted Stage 3:

```sh
env BOOTSTRAP_NATIVE_CACHE_TTL_DAYS=0 SIMPLE_NO_STUB_FALLBACK=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --bootstrap-receipt=<planner-stage4-receipt> \
  --resume-stage4-from-admitted=build/restart12-build11-a-r5/output \
  --deploy --jobs=1
```


## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: the record states its own blocker precisely -- "live acceptance remains blocked
until an admitted Stage 3 lane and planner receipt are available". Neither
exists on this host. The source-only continuation path and sabotage contract are
already written; what is missing is an execution environment, not code.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.

## Closure audit 2026-08-17

The canonical wrapper exposes `--resume-stage4-from-admitted`, requires the
planner-authored `//bootstrap:stage4` receipt, re-verifies the Stage-3 candidate
and provenance before compilation, holds the parent output lock, snapshots and
rechecks immutable Stage-2/3 directories, suppresses Rust seed authority, and
continues through candidate validity, `-c`, source-check, redeploy,
essential-tools, candidate-provenance, deployment, and terminal continuation
receipt gates. Deployment now additionally compares the installed binary hash
against the admitted full Stage-4 candidate and records both in the v1 deploy
receipt; mismatch is fatal before a pass receipt can be published.

Focused executable sabotage contract:

`sh test/01_unit/scripts/bootstrap_resume_stage4_from_admitted_contract_test.shs`

passed once with: `PASS: admitted Stage 4 resume is planner-bound, locked,
immutable, collision-safe, and uses existing gates`. No admitted Stage-3
artifact and planner receipt were present in this worktree, so the live Stage-4
continuation was correctly not started.

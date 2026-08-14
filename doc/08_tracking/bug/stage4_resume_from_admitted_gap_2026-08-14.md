# Stage 4 cannot continue from an admitted resumed Stage 3

## Status

OPEN / EXECUTION BLOCKED. The source-only continuation path and sabotage
contract now exist. Live acceptance remains blocked until an admitted Stage 3
lane and planner receipt are available; this change deliberately did not run a
Stage 3 or Stage 4 build.

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

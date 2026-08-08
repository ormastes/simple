# System Test Plan: SPipe LLM Fine-Tune Process

Date: 2026-06-02

## Goal

Verify that SPipe is separated into a reusable project while the Simple host can
link it, initialize fine-tune evidence, record LLM-backed app/server attempts,
and route verification failures into retry/retune actions.

## Test Surfaces

- `examples/05_stdlib/spipe/scripts/build.shs`
- `.spipe/spipe/scripts/build.shs`
- `scripts/setup/install-spipe-dev-command.shs --check`
- `node examples/05_stdlib/spipe/cli/spipe.js doctor .`
- `node examples/05_stdlib/spipe/cli/spipe.js fine-tune-status <attempt_id>`
- `node examples/05_stdlib/spipe/cli/spipe.js fine-tune-next <attempt_id>`
- `node examples/05_stdlib/spipe/cli/spipe.js fine-tune-verify <record.sdn>`

`fine-tune-next` and `fine-tune-doctor` intentionally exit nonzero for
unfinished retry states. In automation, assert on their printed `next_action`
instead of chaining them as green checks unless the attempt is ready.

## Required Scenarios

1. Submodule separation:
   - `.gitmodules` contains `.spipe/spipe` and `examples/05_stdlib/spipe`.
   - Parent index records both paths as `160000` gitlinks.
   - `examples/05_stdlib/spipe` and `.spipe/spipe` match apart from `.git`.

2. Host link wiring:
   - `.spipe/doc` resolves to configured host doc root.
   - `.spipe/spipe_project` resolves to `examples/05_stdlib/spipe`.
   - Common links for domain expert, SPipe docs, template, project expert, and
     tool expert resolve into the separated SPipe project.

3. Fine-tune process evidence:
   - `fine-tune-init` creates all required registries.
   - Data downloads and data checks can be recorded.
   - Process docs can be scaffolded and recorded.
   - Requirement selection is recordable but not auto-selected.
   - Model research and model architecture can be recorded.
   - Base-model and tuning-method selections can be recorded.
   - Training script scaffolding and training evidence can be recorded.
   - Eval and decision evidence can be recorded.
   - Retry attempts and retune requests can be created.
   - App/server handoff can be recorded and reported.

4. Readiness behavior:
   - Missing attempt reports `next_action=create-attempt`.
   - Seeded dry-run attempt reports `next_action=requirements-selection`.
   - Complete accepted attempt reports `next_action=ready`.
   - Placeholder or incomplete attempt fails `fine-tune-ready`.

5. Layout guard:
   - `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

## Current Automated Coverage

The two SPipe build scripts cover scenarios 1 through 4 with temporary host
fixtures and full attempt-record verification. The repository-level installer
check covers SPipe command routing. The `doc/06_spec` guard covers scenario 5.

2026-06-25 retry-attempt evidence:

- `.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry1.sdn`
  passes the structural attempt verifier.
- `fine-tune-status llm_backed_app_server_dry_run_retry1` reports every
  registry present.
- `fine-tune-next` and `fine-tune-doctor` for
  `llm_backed_app_server_dry_run_retry1` report
  `next_action=retry-data-research`, the recorded `retry_target`, and
  `next_attempt=llm_backed_app_server_dry_run_retry2`.
- `fine-tune-ready llm_backed_app_server_dry_run_retry1` intentionally fails
  `decision_accepted` because the recorded MedGemma evidence is below the
  target and must not be treated as deployable.

2026-06-25 retry2 fixed-format evidence:

- `.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry2.sdn`
  passes the structural attempt verifier.
- `.spipe/llm-finetune-process/scripts/check_fixed_format_data_quality.shs`
  passes on the repo-local synthetic MCQ fixture with `records=3` and
  `invalid_records=0`.
- `fine-tune-status llm_backed_app_server_dry_run_retry2` reports every
  registry present.
- `fine-tune-next` and `fine-tune-doctor` for
  `llm_backed_app_server_dry_run_retry2` route to
  `next_action=retry-implementation` and
  `next_attempt=llm_backed_app_server_dry_run_retry3`.
- `fine-tune-ready llm_backed_app_server_dry_run_retry2` intentionally fails
  `model_artifact_created` and `decision_accepted`; retry2 is a data-format
  gate, not a trained or accepted model.

2026-06-25 retry3 implementation dry-run evidence:

- `.spipe/llm-finetune-process/scripts/run_retry3_local_artifact_eval.shs`
  passes the fixed-format fixture gate, writes
  `.spipe/llm-finetune-process/artifacts/llm_backed_app_server_dry_run_retry3/model_manifest.json`,
  and writes
  `.spipe/llm-finetune-process/artifacts/llm_backed_app_server_dry_run_retry3/eval_result.json`.
- `.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry3.sdn`
  passes the structural attempt verifier.
- `fine-tune-status llm_backed_app_server_dry_run_retry3` reports every
  registry present.
- `fine-tune-doctor` and `fine-tune-next` for
  `llm_backed_app_server_dry_run_retry3` route to
  `next_action=retry-implementation` and
  `next_attempt=llm_backed_app_server_dry_run_retry4`. Both commands
  intentionally exit nonzero for unfinished retry states.
- `fine-tune-ready llm_backed_app_server_dry_run_retry3` intentionally fails
  `model_artifact_created` and `decision_accepted`; retry3 has an
  implementation dry-run manifest, but it is `deployable=false` and no real
  target model eval has run.

2026-06-25 retry4 license/data-access gate evidence:

- `.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry4.sdn`
  passes the structural attempt verifier.
- `.spipe/llm-finetune-process/scripts/check_retry4_license_gate.shs
  llm_backed_app_server_dry_run_retry4` reports
  `license_review=missing`, `data_access=missing`,
  `training_allowed=false`, and `STATUS: WARN retry4-license-gate`.
- `fine-tune-status llm_backed_app_server_dry_run_retry4` reports every
  registry present.
- `fine-tune-next` and `fine-tune-doctor` for
  `llm_backed_app_server_dry_run_retry4` route to
  `next_action=retry-data-research` and
  `next_attempt=llm_backed_app_server_dry_run_retry5`.
- `fine-tune-ready llm_backed_app_server_dry_run_retry4` intentionally fails
  `model_artifact_created` and `decision_accepted`; retry4 is a license/data
  gate, not a trained or accepted model.

2026-06-26 retry5 licensed data cache/checksum gate evidence:

- `.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry5.sdn`
  records the current licensed data acquisition/cache gate.
- `.spipe/llm-finetune-process/scripts/check_retry5_data_access_gate.shs
  llm_backed_app_server_dry_run_retry5` reports
  `license_review=missing`, `data_access=missing`,
  `cache_checksum=missing`, `training_allowed=false`, and
  `STATUS: WARN retry5-data-access-gate`.
- `fine-tune-status llm_backed_app_server_dry_run_retry5` now executes the
  recorded `data_checks.sdn` checker and reports `data_check_execution=warn`
  with `data_check_status="STATUS: WARN retry5-cache-manifest"` instead of
  treating registry-row presence as ready evidence.
- Retry5 must continue to fail `fine-tune-ready` until licensed data access,
  cache path, checksum evidence, real QLoRA training, target-reaching eval, and
  an accepted decision are all recorded.

2026-06-26 retry6 real-training/eval gate evidence:

- `.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry6.sdn`
  records the next concrete attempt after retry5.
- `.spipe/llm-finetune-process/scripts/check_retry6_training_eval_gate.shs
  llm_backed_app_server_dry_run_retry6` wraps the retry5 normal-review handoff
  and then checks for retry6 model/eval artifacts. It currently reports
  `upstream_review_status=WARN retry5-review-handoff`,
  `training_allowed=false`, `model_manifest_exists=false`,
  `eval_result_exists=false`, `acceptance_allowed=false`, and
  `STATUS: WARN retry6-training-eval-gate`.
- Retry6 must continue to fail `fine-tune-ready` until retry5 licensed cache
  review passes, real QLoRA writes a model manifest, target eval reaches the
  selected threshold, safety/deployment/app handoff evidence is recorded, and a
  normal LLM records an accepted decision.
- `test/03_system/tools/spipe/llm_finetune_retry6_training_eval_gate_spec.spl`
  covers retry6's direct gate behavior with deterministic retry5 cache
  fixtures. It proves below-target eval remains
  `BLOCKED_MODEL_OR_TARGET_EVAL_INCOMPLETE` and threshold-met eval only reaches
  `TARGET_EVAL_REVIEW_REQUIRED`; `acceptance_allowed=false` remains true in
  both cases.
- `doc/06_spec/03_system/tools/spipe/llm_finetune_retry6_training_eval_gate_spec.md`
  is the operator manual for that retry6 handoff evidence.

2026-06-26 retry7 normal acceptance-review gate evidence:

- `.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry7.sdn`
  records the normal acceptance-review gate requested by retry6.
- `.spipe/llm-finetune-process/scripts/check_retry7_acceptance_gate.shs
  llm_backed_app_server_dry_run_retry7` wraps the retry6 training/eval gate and
  blocks acceptance while retry6 lacks real model and eval artifacts.
- Retry7 must continue to fail `fine-tune-ready` until retry6 has target eval,
  license constraints, safety evaluation, deployment evidence, and an accepted
  normal-review decision.
- `test/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.spl`
  covers the retry7 gate script, `fine-tune-status`, `fine-tune-ready`, and the
  public-output rule that blocked readiness must not surface raw `nil`.
- `doc/06_spec/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.md`
  is the operator manual for that system evidence.

## Manual Gate

Final SPipe fine-tune process requirements are selected in
`doc/02_requirements/language/tools/spipe_llm_finetune_process.md` and
`doc/02_requirements/nfr/spipe_llm_finetune_process.md`.

The remaining manual gate is model acceptance and licensed data access: do not
mark a fine-tune attempt ready until the decision registry records `accepted`
after target-reaching eval evidence, license review, cache/checksum evidence,
and app/server handoff verification. The current concrete next attempt is
`llm_backed_app_server_dry_run_retry7`; it is blocked by retry6 training/eval
evidence and is not itself a training attempt.

2026-06-26 app/server handoff evidence gate:

- `fine-tune-record-app` now requires explicit `license_constraints`,
  `safety_eval`, and `deployment_evidence` fields.
- Both `spipe fine-tune-verify` and
  `.spipe/llm-finetune-process/scripts/verify_attempt.shs` fail records that
  omit those fields, so medical QA handoffs cannot pass as production evidence
  with only a free-form usage string.
- Current retry records and `app_handoffs.sdn` carry explicit non-deployment
  evidence until license/distribution review, refusal/boundary/clinical
  disclaimer checks, and runtime/memory/latency/fallback deployment evidence
  are real.

2026-06-28 operator guide sync:

- Added `doc/07_guide/app/llm/spipe_llm_finetune_process.md` as the focused
  operator guide for retry5/retry6/retry7 handoff, current retry7 blocked
  semantics, command entrypoints, evidence locations, and promotion rules.
- The guide keeps retry7 documented as a normal-review acceptance gate, not a
  training attempt, and it records that blocked public output must use explicit
  status text rather than internal absence markers.

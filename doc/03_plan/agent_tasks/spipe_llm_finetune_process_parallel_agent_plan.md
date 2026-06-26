# SPipe LLM Fine-Tune Process Parallel Agent Plan

## Goal

Prove that a small SPipe implementation task can be checked by a Spark-model
agent and then reviewed by a normal LLM process without losing artifact
traceability.

## Agent Split

- Lead Codex owns integration, file edits, final verification, and handoff.
- Spark sidecar owns bounded small-task verification only. It may run focused
  checks and report PASS/FAIL, but it does not commit or overwrite files.
- Normal LLM sidecar owns process evidence review: attempt records, eval
  results, handoff state, and missing documentation.

## Current Small Task

Host/GPU lane marker and Engine2D event-flow evidence:

- `test/03_system/feature/language/host_gpu_lane_spec.spl`
- `test/03_system/feature/language/host_gpu_event_path_spec.spl`
- `src/lib/gc_async_mut/gpu/engine2d/host_gpu_event_queue.spl`
- `src/lib/gc_async_mut/gpu/engine2d/host_gpu_draw_ir_event_flow.spl`

## Evidence Contract

- Spark verification must record exact commands, pass/fail status, and gaps.
- Normal LLM verification must update `.spipe/llm-finetune-process` only after
  an actual attempt/eval/handoff is present.
- Lead Codex must run the final SPipe specs, generated-doc guard, and relevant
  runtime/backend evidence scripts.

## 2026-06-14 Status

- Spark small-task verifier passed interpreter host/GPU marker and event-flow
  checks and reported a native-mode SSpec gap.
- Normal LLM process explorer found no existing proof that a normal LLM attempt
  reached acceptance.

## 2026-06-25 Retry1 Evidence

Retry attempt `llm_backed_app_server_dry_run_retry1` now has complete structural
registry evidence, but it is intentionally not accepted because the recorded
MedGemma evidence remains below the target threshold.

Evidence:

- `.spipe/llm-finetune-process/scripts/verify_attempt.shs
  .spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry1.sdn`
  reports `STATUS: PASS llm-finetune-attempt-record`.
- `fine-tune-status llm_backed_app_server_dry_run_retry1` reports all
  registries present and `STATUS: PASS llm-finetune-status`.
- `fine-tune-next llm_backed_app_server_dry_run_retry1` reports
  `next_action=retry-data-research`,
  `retry_target=complete fixed-format data-quality retry and rerun
  target_accuracy>=90.0 eval before app/server acceptance`, and
  `next_attempt=llm_backed_app_server_dry_run_retry2`.
- `fine-tune-doctor llm_backed_app_server_dry_run_retry1` reports the same
  retry routing with `STATUS: WARN llm-finetune-doctor`.

## 2026-06-25 Retry2 Fixed-Format Gate

Retry attempt `llm_backed_app_server_dry_run_retry2` now exists and records a
synthetic fixed-format MCQ data-quality gate. It is intentionally not accepted:
no new model artifact exists and no target model eval has been rerun.

Evidence:

- `.spipe/llm-finetune-process/scripts/check_fixed_format_data_quality.shs
  .spipe/llm-finetune-process/data/llm_backed_app_server_dry_run_retry2_fixed_format_sample.jsonl`
  reports `records=3`, `invalid_records=0`, and
  `STATUS: PASS fixed-format-data-quality`.
- `.spipe/llm-finetune-process/scripts/verify_attempt.shs
  .spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry2.sdn`
  reports `STATUS: PASS llm-finetune-attempt-record`.
- `fine-tune-status llm_backed_app_server_dry_run_retry2` reports every
  registry present and `STATUS: PASS llm-finetune-status`.
- `fine-tune-doctor llm_backed_app_server_dry_run_retry2` reports
  `WARN placeholder model_artifact=not-created`,
  `next_action=retry-implementation`, and
  `STATUS: WARN llm-finetune-doctor`.
- `fine-tune-ready llm_backed_app_server_dry_run_retry2` reports
  `model_artifact_created=pending`, `decision_accepted=pending`, and
  `STATUS: FAIL llm-finetune-ready`.

## 2026-06-25 Retry3 Implementation Dry-Run

Retry attempt `llm_backed_app_server_dry_run_retry3` now exists and records a
local implementation artifact/eval manifest after the fixed-format data gate.
It is intentionally not accepted: the artifact declares `deployable=false`, the
eval record is a dry-run failure sentinel, and no real target model eval has
run.

Evidence:

- `.spipe/llm-finetune-process/scripts/run_retry3_local_artifact_eval.shs`
  reports the retry3 artifact and eval artifact paths after checking the
  fixed-format fixture.
- `.spipe/llm-finetune-process/scripts/verify_attempt.shs
  .spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry3.sdn`
  reports `STATUS: PASS llm-finetune-attempt-record`.
- `fine-tune-status llm_backed_app_server_dry_run_retry3` reports every
  registry present and `STATUS: PASS llm-finetune-status`.
- `fine-tune-ready llm_backed_app_server_dry_run_retry3` reports
  `model_artifact_created=pending`, `decision_accepted=pending`, and
  `STATUS: FAIL llm-finetune-ready`.

## 2026-06-25 Retry4 License/Data-Access Gate

Retry attempt `llm_backed_app_server_dry_run_retry4` now exists and records a
license/data-access gate before real QLoRA. It is intentionally not accepted:
no licensed data cache, model artifact, target eval, or accepted decision
exists yet.

Evidence:

- `.spipe/llm-finetune-process/scripts/check_retry4_license_gate.shs
  llm_backed_app_server_dry_run_retry4` reports `license_review=missing`,
  `data_access=missing`, `training_allowed=false`, and
  `STATUS: WARN retry4-license-gate`.
- `.spipe/llm-finetune-process/scripts/verify_attempt.shs
  .spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry4.sdn`
  reports `STATUS: PASS llm-finetune-attempt-record`.
- `fine-tune-status llm_backed_app_server_dry_run_retry4` reports every
  registry present and `STATUS: PASS llm-finetune-status`.
- `fine-tune-next llm_backed_app_server_dry_run_retry4` reports
  `next_action=retry-data-research` and
  `next_attempt=llm_backed_app_server_dry_run_retry5`.
- `fine-tune-ready llm_backed_app_server_dry_run_retry4` reports
  `model_artifact_created=pending`, `decision_accepted=pending`, and
  `STATUS: FAIL llm-finetune-ready`.

Next normal-LLM work: obtain licensed fixed-format data access and
cache/checksum evidence, then run real QLoRA/eval or route to another strategy.
Record an accepted decision only if eval reaches the target and license/handoff
checks pass.

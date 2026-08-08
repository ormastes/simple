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

## 2026-06-26 Retry5 Handoff

Retry attempt `llm_backed_app_server_dry_run_retry5` now exists as the current
licensed data acquisition/cache-checksum gate. It is intentionally not accepted:
no licensed cache path, checksum, trained artifact, target eval, or accepted
decision exists yet.

Evidence:

- `.spipe/llm-finetune-process/scripts/check_retry5_data_access_gate.shs
  llm_backed_app_server_dry_run_retry5` reports `license_review=missing`,
  `data_access=missing`, `cache_checksum=missing`,
  `training_allowed=false`, and `STATUS: WARN retry5-data-access-gate`.
- `.spipe/llm-finetune-process/scripts/check_retry5_cache_manifest.shs
  llm_backed_app_server_dry_run_retry5
  .spipe/llm-finetune-process/data/llm_backed_app_server_dry_run_retry5_cache_manifest.sdn`
  is the deterministic cache/checksum gate for retry5. It reports
  `STATUS: WARN retry5-cache-manifest` while the manifest is missing, and only
  reports PASS when `license_review=approved`, `data_access=granted`, the cache
  path exists, and `checksum` matches the cached file's `sha256:<hex>`. The
  gate emits parseable proof fields for review: `manifest_exists`,
  `cache_path_exists`, `expected_checksum`, `actual_checksum`, and
  `checksum_match`.
- `.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry5.sdn`
  records the retry target as licensed data acquisition, cache/checksum
  verification, QLoRA rerun, and target eval.
- `.spipe/llm-finetune-process/scripts/check_retry5_review_handoff.shs
  llm_backed_app_server_dry_run_retry5` wraps the attempt verifier, cache
  manifest gate, and data-access gate into the normal-review handoff surface.
  It reports `STATUS: WARN retry5-review-handoff`,
  `normal_review_status=blocked`, and `acceptance_allowed=false` while licensed
  cache evidence is missing, and carries the manifest/file/checksum proof
  fields from the cache gate. Even after the cache gate passes, acceptance stays
  false until real QLoRA target eval and app handoff evidence are recorded.
- `fine-tune-status llm_backed_app_server_dry_run_retry5` now runs the
  repo-local checker recorded in `data_checks.sdn` and reports
  `STATUS: WARN llm-finetune-status` with
  `data_check_status="STATUS: WARN retry5-cache-manifest"` while the licensed
  cache manifest is missing or incomplete.
- `.spipe/llm-finetune-process/README.md` now documents the retry5 cache
  manifest and normal-review handoff commands, including the proof fields and
  the rule that `acceptance_allowed=false` remains true until target eval plus
  app handoff evidence exist.

Next normal-LLM work: obtain licensed data approval and write cache/checksum
evidence for retry5 before any real training or acceptance claim.

## 2026-06-26 Retry6 Training/Eval Gate

Retry attempt `llm_backed_app_server_dry_run_retry6` now exists as the concrete
real-training/eval gate after retry5. It is intentionally not accepted: retry5
licensed cache review is still WARN, no model manifest exists, no target eval
exists, and no accepted decision exists.

Evidence:

- `.spipe/llm-finetune-process/scripts/check_retry6_training_eval_gate.shs
  llm_backed_app_server_dry_run_retry6` reports
  `upstream_review_status=WARN retry5-review-handoff`,
  `training_allowed=false`, `model_manifest_exists=false`,
  `eval_result_exists=false`, `acceptance_allowed=false`, and
  `STATUS: WARN retry6-training-eval-gate`.
- `.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry6.sdn`
  passes the structural attempt verifier while recording non-deployable
  license, safety, and deployment evidence.
- `fine-tune-status llm_backed_app_server_dry_run_retry6` is expected to report
  WARN until retry5 cache review, real QLoRA, target eval, app handoff, and an
  accepted decision are all present.

Next normal-LLM work: complete retry5 licensed cache/checksum evidence before
running retry6 training. Do not synthesize model/eval artifacts or accept the
attempt without real evidence.

## 2026-06-26 Retry7 Normal Acceptance Gate

Retry attempt `llm_backed_app_server_dry_run_retry7` now exists as the normal
acceptance-review gate after retry6. It is intentionally not accepted: retry6
has not produced a real model manifest, target eval, accepted decision, safety
review, deployment evidence, or app handoff evidence.

Evidence:

- `.spipe/llm-finetune-process/scripts/check_retry7_acceptance_gate.shs
  llm_backed_app_server_dry_run_retry7` reports
  `upstream_retry6_result=BLOCKED_UPSTREAM_LICENSED_DATA_NOT_READY`,
  `training_allowed=false`, `model_manifest_exists=false`,
  `eval_result_exists=false`, `acceptance_allowed=false`, and
  `STATUS: WARN retry7-acceptance-gate`.
- `test/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.spl`
  verifies the retry7 script, attempt record, `fine-tune-status`, and
  `fine-tune-ready` behavior while keeping public output internal-marker-free.
- Generated manuals exist at
  `doc/06_spec/test/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.md`
  and
  `doc/06_spec/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.md`.
- 2026-06-26 manual hardening: retry7 absence assertions now use an internal
  marker helper, the focused system spec still passes 4/4, and both generated
  manuals were refreshed so public expected-code snippets do not expose the
  internal absence marker.
- 2026-06-26 readiness hardening: `fine-tune-ready
  llm_backed_app_server_dry_run_retry7` now surfaces
  `license_constraints_reviewed`, `safety_eval_complete`,
  `deployment_evidence_ready`, and `app_handoff_doc_ready` alongside model,
  target-eval, and decision checks. The retry7 system spec asserts the current
  license/safety/deployment blockers remain pending and the app handoff doc is
  present, so the ready gate fails closed against the full non-acceptance
  checklist.
- 2026-06-26 doctor hardening: shared readiness routing now includes the same
  license, safety, deployment, and app-handoff gates used by `fine-tune-ready`.
  `fine-tune-doctor llm_backed_app_server_dry_run_retry7` reports the current
  `license_constraints=pending`, `safety_eval=not-run`, and
  `deployment_evidence=not-deployable` placeholders explicitly, and the focused
  retry7 system spec now passes 5/5 with that contract.
- 2026-06-26 retry6 target-eval hardening: `check_retry6_training_eval_gate.shs`
  no longer treats model/eval file presence as sufficient handoff evidence.
  Once retry5 is PASS, retry6 only reports `TARGET_EVAL_REVIEW_REQUIRED` when
  the model manifest is deployable and the eval artifact exposes
  `target_accuracy` or `final_accuracy` meeting the 90.0 threshold. Retry7 now
  propagates `target_accuracy` and `target_eval_reached` so normal acceptance
  cannot advance on empty or below-target eval files.
- 2026-06-26 retry6 direct gate evidence: the retry6 checker now accepts
  optional upstream attempt-record and cache-manifest paths for deterministic
  verifier fixtures. `llm_finetune_retry6_training_eval_gate_spec.spl` proves a
  checksum-matched retry5 cache still blocks below-target retry6 evals and only
  reaches `TARGET_EVAL_REVIEW_REQUIRED` after deployable model plus
  `target_accuracy>=90.0`; acceptance remains false pending normal review.
- 2026-06-26 retry6 operator-surface hardening: `fine-tune-status` and
  `fine-tune-doctor` now parse retry checker key/value output and print
  `result`, `target_accuracy`, `required_accuracy`, `target_eval_reached`, and
  `acceptance_allowed` directly. The retry6 system spec covers both public
  surfaces so target-eval blockers are not hidden behind only
  `data_check_status`.
- 2026-06-26 next-action status hardening: `fine-tune-next` now prints
  `STATUS: WARN llm-finetune-next` for non-ready attempts and
  `STATUS: PASS llm-finetune-next` only when readiness is complete. The retry7
  system spec covers the current `retry-implementation` next action, retry
  target, WARN status, and public absence-marker policy.
- 2026-06-28 app handoff readiness hardening: `fine-tune-ready` and
  `fine-tune-next` now treat an app handoff doc path as pending while the
  handoff record still says `do not deploy`, license constraints are pending,
  safety eval is `not-run`, or deployment evidence is `not-deployable`. Retry7
  now reports `app_handoff_doc_ready=pending`, matching the acceptance gate's
  full license/safety/deployment/app-handoff requirement instead of accepting a
  placeholder architecture doc path as release-ready evidence.
- 2026-06-28 next-action blocker hardening: `fine-tune-next` now prints
  `readiness_blocker=<gate>` for retry-decision and readiness-blocked attempts.
  Retry7 currently reports `readiness_blocker=model-artifact`, so operators can
  see the first unmet release gate without separately invoking
  `fine-tune-ready`.
- 2026-06-28 local artifact readiness hardening: `fine-tune-ready` now requires
  local filesystem model artifact paths to exist before `model_artifact_created`
  can become ready. Explicit artifact URIs such as `model://...` remain valid
  provider-managed artifacts. The SPipe build smoke includes a missing-local
  artifact fixture that must fail readiness and report
  `readiness_blocker=model-artifact`.
- 2026-06-28 data-checker path hardening: executable fine-tune data-check
  scripts are resolved under `.spipe/llm-finetune-process/scripts/`, and path
  traversal outside that directory reports
  `STATUS: FAIL llm-finetune-data-gate` instead of executing. The SPipe build
  smoke includes an `unsafe_checker` traversal fixture.
- 2026-06-28 local handoff-doc readiness hardening: `fine-tune-ready` now
  requires local filesystem app handoff doc paths to exist before
  `app_handoff_doc_ready` can become ready. Explicit doc URIs remain valid
  externally managed evidence. The SPipe build smoke includes a
  missing-local-handoff-doc fixture that must fail readiness and report
  `readiness_blocker=app-handoff-doc`.
- 2026-06-28 doctor local-reference diagnostics: `fine-tune-doctor` now prints
  `WARN missing_local_model_artifact` and `WARN missing_local_handoff_doc` when
  non-placeholder local paths do not exist, matching the stricter
  `fine-tune-ready` gates instead of leaving operators to infer the blocker
  from `fine-tune-next`.
- 2026-06-28 doctor target-eval diagnostics: `fine-tune-doctor` now prints
  `WARN target_eval_not_reached` with a machine-readable reason plus the target
  and metrics text when eval evidence is malformed, missing the metric, below
  threshold, or not marked pass. The SPipe build smoke covers a below-target
  eval fixture.
- 2026-06-28 status readiness visibility: `fine-tune-status` now prints
  `readiness_blocker=<gate>` so a present set of eval/model/handoff rows cannot
  hide the first release-gate blocker. Attempts whose release gate is ready
  print `readiness_blocker=none`; status may still fail separately for missing
  required registry evidence.

Next normal-LLM work: finish retry5 licensed cache/checksum evidence and retry6
real training/eval before retry7 can become an acceptance gate with a PASS
result. Do not synthesize model/eval artifacts or record an accepted decision
without real evidence.

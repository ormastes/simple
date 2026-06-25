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
  passed; retry attempt `llm_backed_app_server_dry_run_retry1` remains mostly
  empty.
- Next normal-LLM work: complete retry1 research/requirements/model/eval fields,
  run `.spipe/llm-finetune-process/scripts/verify_attempt.shs`, then record
  `eval_results.sdn` and `app_handoffs.sdn` only if the attempt passes.

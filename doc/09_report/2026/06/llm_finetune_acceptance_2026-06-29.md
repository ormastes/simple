# LLM Fine-Tune Acceptance Evidence

- status: `fail`
- reason: `BLOCKED_RETRY6_NOT_READY`
- attempt: `llm_backed_app_server_dry_run_retry7`
- required_gates: `retry6_training_eval,training_allowed,model_manifest,eval_result,target_eval,decision,license,safety,deployment,app_handoff`
- blocked_gates: `retry6_training_eval|training_allowed|model_manifest|eval_result|target_eval|decision|license|safety|deployment|app_handoff`
- primary_blocked_gate: `retry6_training_eval`
- gate_status: `WARN retry7-acceptance-gate`
- acceptance_allowed: `false`
- training_allowed: `false`
- upstream_retry6_result: `BLOCKED_UPSTREAM_LICENSED_DATA_NOT_READY`
- upstream_attempt_record: `/home/ormastes/dev/pub/simple-llm-runtime-workspace-20260629/.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry5.sdn`
- upstream_cache_manifest: `/home/ormastes/dev/pub/simple-llm-runtime-workspace-20260629/.spipe/llm-finetune-process/data/llm_backed_app_server_dry_run_retry5_cache_manifest.sdn`
- attempt_record: `/home/ormastes/dev/pub/simple-llm-runtime-workspace-20260629/.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry7.sdn`
- model_manifest: `/home/ormastes/dev/pub/simple-llm-runtime-workspace-20260629/.spipe/llm-finetune-process/artifacts/llm_backed_app_server_dry_run_retry6/model_manifest.json`
- model_manifest_exists: `false`
- model_manifest_deployable: `missing`
- eval_result: `/home/ormastes/dev/pub/simple-llm-runtime-workspace-20260629/.spipe/llm-finetune-process/artifacts/llm_backed_app_server_dry_run_retry6/eval_result.json`
- eval_result_exists: `false`
- target_eval_reached: `false`
- target_accuracy: `missing`
- required_accuracy: `90.0`
- retry6_next_action: `complete retry5 licensed cache/checksum review before retry6 training`
- attempt_record_status: `PASS llm-finetune-attempt-record`
- decision_status: `retry-implementation`
- license_constraints: `pending`
- safety_eval: `not-run`
- deployment_evidence: `not-deployable`
- handoff_doc: `doc/04_architecture/app/spipe/spipe_llm_finetune_model_architecture.md`
- handoff_usage: `do not deploy; retry7 has no accepted retry6 model/eval/safety/deployment evidence`
- app_handoff_doc_ready: `false`
- next_action: `complete retry6 training/eval gate before normal acceptance review`
- env: `build/llm_finetune_acceptance/evidence.env`

This evidence consumes the retry7 normal acceptance gate. It only passes when retry7 itself passes with `acceptance_allowed=true` and every normalized required gate is unblocked. Otherwise it records the required gate list, compact blocked-gates list, model/eval/license/safety/deployment/app-handoff fields, and next action while keeping strict fine-tune readiness failed.

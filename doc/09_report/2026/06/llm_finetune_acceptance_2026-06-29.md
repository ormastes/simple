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
- model_manifest_exists: `false`
- eval_result_exists: `false`
- target_eval_reached: `false`
- target_accuracy: `missing`
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

This evidence consumes the retry7 normal acceptance gate. It only passes when retry7 itself passes with `acceptance_allowed=true`; otherwise it records the required gate list, compact blocked-gates list, model/eval/license/safety/deployment/app-handoff fields, and next action while keeping strict fine-tune readiness failed.

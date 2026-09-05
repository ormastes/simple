# LLM Fine-Tune Acceptance Evidence

- status: `fail`
- reason: `BLOCKED_RETRY6_NOT_READY`
- attempt: `llm_backed_app_server_dry_run_retry7`
- gate_status: `WARN retry7-acceptance-gate`
- acceptance_allowed: `false`
- upstream_retry6_result: `BLOCKED_UPSTREAM_LICENSED_DATA_NOT_READY`
- target_eval_reached: `false`
- target_accuracy: `missing`
- license_constraints: `pending`
- safety_eval: `not-run`
- deployment_evidence: `not-deployable`
- app_handoff_doc_ready: `false`
- env: `build/llm_finetune_acceptance/evidence.env`

This evidence consumes the retry7 normal acceptance gate. It only passes when retry7 itself passes with `acceptance_allowed=true`; otherwise it records the concrete model/eval/license/safety/deployment/app-handoff blockers and keeps strict fine-tune readiness failed.

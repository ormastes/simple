# LLM Goal Evidence

- status: `fail`
- strict_host: `true`
- warn_count: `0`
- fail_count: `4`
- warn_gates: `none`
- failed_gates: `vllm_host|svllm_local|torch_optimizer|finetune_guard`
- failed_gate_hints: `vllm_host:local vLLM/GPU host evidence through check-llm-runtime-vllm-host-probe.shs --strict|svllm_local:check-llm-runtime-svllm-native-streaming-evidence.shs evidence with svllm_native_streaming_status=pass|torch_optimizer:Simple/libtorch CUDA optimizer evidence through check-llm-runtime-torch-cuda-optimizer-probe.shs --strict|finetune_guard:check-llm-finetune-acceptance-evidence.shs evidence with llm_finetune_acceptance_status=pass`
- env: `build/llm_goal_evidence/evidence.env`
- lane_timeout_seconds: `180`

| lane | status | expected | exit | log |
|------|--------|----------|------|-----|
| context_ponytail | `pass` | `pass` | `0` | `build/llm_goal_evidence/context_ponytail.log` |
| dashboard | `pass` | `pass` | `0` | `build/llm_goal_evidence/dashboard.log` |
| vllm_host | `fail` | `pass` | `1` | `build/llm_goal_evidence/vllm_host.log` |
| svllm_local | `fail` | `pass` | `1` | `build/llm_goal_evidence/svllm_local.log` |
| torch_optimizer | `fail` | `pass` | `1` | `build/llm_goal_evidence/torch_optimizer.log` |
| finetune_guard | `fail` | `pass` | `1` | `build/llm_goal_evidence/finetune_guard.log` |
| public_absence | `pass` | `pass` | `0` | `build/llm_goal_evidence/public_absence.log` |

## Strict Evidence Hints

- context_ponytail: `check-llm-tooling-context-ponytail-full-replacement.shs evidence with llm_tooling_context_ponytail_full_replacement_status=pass`
- dashboard: `check-llm-dashboard-live-evidence.shs evidence with llm_dashboard_live_status=pass`
- vllm_host: `local vLLM/GPU host evidence through check-llm-runtime-vllm-host-probe.shs --strict`
- svllm_local: `check-llm-runtime-svllm-native-streaming-evidence.shs evidence with svllm_native_streaming_status=pass`
- torch_optimizer: `Simple/libtorch CUDA optimizer evidence through check-llm-runtime-torch-cuda-optimizer-probe.shs --strict`
- finetune_guard: `check-llm-finetune-acceptance-evidence.shs evidence with llm_finetune_acceptance_status=pass`
- public_absence: `public absence rendering guard must pass`

## Blocker Details

| lane | required_gates | blocked_gates | reason |
|------|----------------|---------------|--------|
| vllm_host | `local_vllm,local_gpu,serve_preflight,endpoint_reachable,models_listed` | `local_vllm|serve_preflight|endpoint_reachable|models_listed` | `missing_local_vllm` |
| svllm_local | `native_read_range,pinned_buffer,device_staging` | `native_read_range|pinned_buffer|device_staging` | `native_read_range_unavailable` |
| torch_optimizer | `libtorch,cuda,parameter_cuda,autograd_gradient,optimizer_step_decreases_parameter_sum` | `libtorch` | `libtorch_unavailable` |
| finetune_guard | `retry6_training_eval,training_allowed,model_manifest,eval_result,target_eval,decision,license,safety,deployment,app_handoff` | `retry6_training_eval|training_allowed|model_manifest|eval_result|target_eval|decision|license|safety|deployment|app_handoff` | `BLOCKED_RETRY6_NOT_READY` |

This aggregate is strict host evidence: full context/Ponytail replacement, live dashboard operation, live vLLM serving, native svLLM streaming, fine-tune acceptance, and Simple/libtorch CUDA optimizer execution must pass through their focused strict wrappers. Any WARN or FAIL lane keeps the aggregate failed.

# LLM Goal Evidence

- status: `pass`
- strict_host: `false`
- warn_count: `2`
- fail_count: `0`
- warn_gates: `vllm_host|torch_optimizer`
- failed_gates: `none`
- failed_gate_hints: `none`
- env: `build/llm_goal_evidence/evidence.env`

| lane | status | expected | exit | log |
|------|--------|----------|------|-----|
| context_ponytail | `pass` | `pass` | `0` | `build/llm_goal_evidence/context_ponytail.log` |
| dashboard | `pass` | `pass` | `0` | `build/llm_goal_evidence/dashboard.log` |
| vllm_host | `warn` | `warn` | `0` | `build/llm_goal_evidence/vllm_host.log` |
| svllm_local | `pass` | `pass` | `0` | `build/llm_goal_evidence/svllm_local.log` |
| torch_optimizer | `warn` | `warn` | `0` | `build/llm_goal_evidence/torch_optimizer.log` |
| finetune_guard | `pass` | `pass` | `0` | `build/llm_goal_evidence/finetune_guard.log` |
| public_absence | `pass` | `pass` | `0` | `build/llm_goal_evidence/public_absence.log` |

This aggregate proves the current local LLM tooling evidence lanes remain reproducible. WARN lanes are expected only for host-dependent gates that are still open on this machine: live vLLM serving and Simple/libtorch CUDA optimizer execution. The context/Ponytail lane is local mimic evidence only in default mode, the dashboard lane is route/collector evidence only in default mode, the svLLM lane is local file-backed readiness only in default mode, and the fine-tune lane is guard evidence only in default mode. This report is not release-completion evidence for those live host gates; rerun with `--strict-host` on a configured host when full context/Ponytail replacement, live dashboard operation, live vLLM, native svLLM streaming, fine-tune acceptance, and Simple/libtorch CUDA optimizer gates must pass.

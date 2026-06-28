# LLM Runtime vLLM Host Probe

- command: `release/x86_64-unknown-linux-gnu/simple run src/app/llm_runtime/control_cli.spl -- --action preflight --base-model base-model --endpoint http://127.0.0.1:8000/v1 --detect-resources`
- status: `unavailable`
- reason: `missing_local_vllm`
- preflight_status: `skipped`
- endpoint_status: `not_checked`
- models_status: `not_fetched`
- models_reason: `environment_skipped`
- exit_code: `0`
- env: `build/llm_runtime_vllm_host_probe/evidence.env`
- log: `build/llm_runtime_vllm_host_probe/preflight.log`

This wrapper records repeatable local vLLM host preflight evidence. It does not prove live serving readiness; `unavailable` means the host lacks local vLLM/GPU resources or only reached preflight planning. Run with `--strict` when unavailable hosts must fail the lane.

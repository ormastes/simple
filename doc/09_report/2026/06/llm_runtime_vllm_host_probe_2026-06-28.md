# LLM Runtime vLLM Host Probe - 2026-06-28

## Scope

This report records the local host preflight for `FR-LLM-RUNTIME-0001`.
It is host evidence only. It does not prove live vLLM serving readiness.

## Command

```sh
release/x86_64-unknown-linux-gnu/simple run src/app/llm_runtime/control_cli.spl -- --action preflight --base-model base-model --endpoint http://127.0.0.1:8000/v1 --detect-resources
```

## Result

```json
{"event":"llm_runtime_vllm_dashboard_control_execution","action":"preflight","status":"skipped","reason":"missing_local_vllm","pid":0,"running":"not_started","endpoint":"not_checked","models_status":"not_fetched","models_reason":"environment_skipped","http_status":0,"started_pid":0,"stopped_pid":0}
```

## Interpretation

The host did not have a locally detectable `vllm` command at probe time. The
feature remains `request` because serving readiness still requires a configured
local vLLM endpoint returning `/v1/models` with the selected base model.

# LLM Runtime vLLM Host Probe

- command: `release/x86_64-unknown-linux-gnu/simple run src/app/llm_runtime/control_cli.spl -- --action readiness --base-model base-model --endpoint http://127.0.0.1:8000/v1 --detect-resources`
- status: `unavailable`
- reason: `missing_local_vllm`
- required_gates: `local_vllm,local_gpu,serve_preflight,endpoint_reachable,models_listed`
- blocked_gates: `local_vllm|serve_preflight|endpoint_reachable|models_listed`
- primary_blocked_gate: `local_vllm`
- base_model: `base-model`
- endpoint: `http://127.0.0.1:8000/v1`
- local_vllm_status: `missing`
- vllm_command_path: `missing`
- python_vllm_module_status: `missing`
- local_gpu_status: `available`
- readiness_status: `skipped`
- preflight_status: `skipped`
- endpoint_status: `not_checked`
- models_status: `not_fetched`
- models_reason: `environment_skipped`
- log_size: `96660`
- log_sha256: `fe9cdac733c972f4e5ee309bbbd6c3867115c1e8f363c6499c7bc7935d7c14fd`
- serve_readiness_run_event_count: `1`
- pass_integrity_status: `not_applicable`
- pass_integrity_reason: `not_applicable`
- next_action: `install or expose the local vllm executable, then rerun the strict vLLM host probe`
- exit_code: `0`
- env: `build/llm_runtime_vllm_host_probe/evidence.env`
- log: `build/llm_runtime_vllm_host_probe/preflight.log`

This wrapper records repeatable local vLLM host preflight evidence. It only proves live serving readiness when all required gates pass. A `status=pass` wrapper result must also have no blocked gates, exactly one serve-readiness run event in a non-empty hashed log, zero CLI exit, local vLLM and GPU availability, ready preflight/readiness, a configured endpoint, `models_status=ready`, and `models_reason=models_endpoint_ready`. `unavailable` records the compact blocked-gates list for missing local vLLM/GPU resources, skipped serve preflight, endpoint reachability, or model-listing evidence; run with `--strict` when unavailable hosts must fail the lane.

# LLM Runtime svLLM Local Readiness Evidence

- status: `fail`
- strict_native: `true`
- native_streaming: `fail`
- native_reason: `native_streaming_pass_integrity_missing`
- native_blocked_gates: `native_pass_integrity`
- native_primary_blocked_gate: `native_pass_integrity`
- native_next_action: `rerun native svLLM streaming evidence and require svllm_native_streaming_pass_integrity_status=pass`
- native_pass_integrity_status: `missing`
- native_env: `/tmp/svllm_status_only_native.env`
- spec_timeout_seconds: `120`
- manifest: `pass` exit=`0` log=`build/llm_runtime_svllm_local_readiness/manifest.log`
- tensor_bytes: `pass` exit=`0` log=`build/llm_runtime_svllm_local_readiness/tensor_bytes.log`
- stream_plan: `pass` exit=`0` log=`build/llm_runtime_svllm_local_readiness/stream_plan.log`
- transport: `pass` exit=`0` log=`build/llm_runtime_svllm_local_readiness/transport.log`
- std_fs: `pass` exit=`0` log=`build/llm_runtime_svllm_local_readiness/std_fs.log`
- streaming_readiness: `pass` exit=`0` log=`build/llm_runtime_svllm_local_readiness/streaming_readiness.log`
- svllm_pack_cli: `pass` exit=`0` log=`build/llm_runtime_svllm_local_readiness/svllm_pack_cli.log`
- svllm_pack_log_modes: `pass` exit=`0` log=`build/llm_runtime_svllm_local_readiness/svllm_pack_log_modes.log`
- env: `build/llm_runtime_svllm_local_readiness/evidence.env`

This strict native check requires a separate native svLLM streaming evidence env with `svllm_native_streaming_status=pass` and `svllm_native_streaming_pass_integrity_status=pass`. Local file-backed readiness alone is not completion evidence for NVFS async scheduling, pinned buffer registration, device staging, or true streaming model loads.

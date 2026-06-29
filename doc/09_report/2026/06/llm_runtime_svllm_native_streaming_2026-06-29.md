# LLM Runtime svLLM Native Streaming Evidence

- status: `fail`
- reason: `native_read_range_unavailable`
- local_readiness: `pass`
- capability_source: `env_or_default`
- read_range: `unsupported`
- pinned_buffer: `unsupported`
- device_staging: `unsupported`
- local_read_bytes: `ready`
- local_spec_timeout_seconds: `120`
- env: `build/llm_runtime_svllm_native_streaming/evidence.env`

This evidence consumes the local svLLM readiness gate and records native streaming capability statuses from `SVLLM_NATIVE_READ_RANGE_STATUS`, `SVLLM_NATIVE_PINNED_BUFFER_STATUS`, and `SVLLM_NATIVE_DEVICE_STAGING_STATUS` (default `unsupported`). It only passes when local readiness passes and all three native capability statuses are `ready`. Local file-backed bytes alone remain explicit bring-up evidence, not native streaming completion.

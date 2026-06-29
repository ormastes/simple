# LLM Runtime svLLM Native Streaming Evidence

- status: `fail`
- reason: `native_read_range_unavailable`
- local_readiness: `pass`
- read_range: `unsupported`
- pinned_buffer: `unsupported`
- device_staging: `unsupported`
- local_read_bytes: `ready`
- local_spec_timeout_seconds: `120`
- env: `build/llm_runtime_svllm_native_streaming/evidence.env`

This evidence consumes the local svLLM readiness gate and records the native streaming blockers. It only passes when native read_range, pinned buffer registration, and device staging are all ready. Local file-backed bytes alone remain explicit bring-up evidence, not native streaming completion.

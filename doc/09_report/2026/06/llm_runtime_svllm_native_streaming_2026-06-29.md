# LLM Runtime svLLM Native Streaming Evidence

- status: `fail`
- reason: `capability_evidence_invalid`
- blocked_gates: `capability_evidence`
- primary_blocked_gate: `capability_evidence`
- next_action: `set SVLLM_NATIVE_CAPABILITY_EVIDENCE_PATH to a structured probe artifact whose schema, event, exit, and reported native statuses match the ready capability claims`
- local_readiness: `pass`
- capability_source: `manual_probe`
- capability_provenance: `ready`
- capability_evidence_path: ``
- capability_evidence: `missing`
- capability_evidence_sha256: `missing`
- capability_evidence_size: `0`
- capability_evidence_mtime: `0`
- capability_evidence_schema_version: `missing`
- capability_probe_event: `missing`
- capability_probe_status: `missing`
- capability_probe_exit: `missing`
- capability_evidence_reported_read_range: `missing`
- capability_evidence_reported_pinned_buffer: `missing`
- capability_evidence_reported_device_staging: `missing`
- pass_integrity_status: `not_applicable`
- pass_integrity_reason: `not_applicable`
- read_range: `ready`
- pinned_buffer: `ready`
- device_staging: `ready`
- local_read_bytes: `ready`
- local_spec_timeout_seconds: `120`
- env: `build/llm_runtime_svllm_native_streaming/evidence.env`

This evidence consumes the local svLLM readiness gate and records native streaming capability statuses from `SVLLM_NATIVE_READ_RANGE_STATUS`, `SVLLM_NATIVE_PINNED_BUFFER_STATUS`, and `SVLLM_NATIVE_DEVICE_STAGING_STATUS` (default `unsupported`). It only passes when local readiness passes, all three native capability statuses are `ready`, `SVLLM_NATIVE_CAPABILITY_SOURCE` names the host probe or artifact that proved those ready statuses, and `SVLLM_NATIVE_CAPABILITY_EVIDENCE_PATH` points at a non-empty schema-v1 probe artifact with `svllm_native_capability_probe_event=svllm_native_capability_probe`, `svllm_native_capability_probe_status=pass`, `svllm_native_capability_probe_exit=0`, and reported native statuses matching the wrapper inputs. Local file-backed bytes alone remain explicit bring-up evidence, not native streaming completion.

# LLM Runtime svLLM Native Capability Probe

- status: `pass`
- source: `local_simple_svllm_capability_probe`
- reason: `native_runtime_capabilities_not_linked`
- read_range: `unsupported`
- pinned_buffer: `unsupported`
- device_staging: `unsupported`
- local_read_range_bytes: `ready`
- local_read_range_bytes_reason: `std_fs_read_range_bytes_spec_passed`
- std_fs_spec_status: `pass`
- std_fs_spec_exit: `0`
- std_fs_spec_log: `build/llm_runtime_svllm_native_capability_probe/std_fs_nvfs_client_spec.log`
- std_fs_spec_log_size: `1420`
- std_fs_spec_log_sha256: `54af94a13720f623164e37d7d541351861c33a8834936617353127e4b46c0824`
- std_fs_spec_timeout_seconds: `120`
- next_action: `implement native read_range, pinned-buffer registration, and device staging, then rerun this probe`
- surface_manifest: `build/llm_runtime_svllm_native_capability_probe/svllm_native_capability_probe_surface_manifest.tsv`
- surface_manifest_count: `7`
- surface_manifest_size: `947`
- surface_manifest_sha256: `e78bb764053c26464a7f2f3a50a1c6950a28af4a2a71ffb1972dcc7a8135b60c`
- env: `build/llm_runtime_svllm_native_capability_probe/evidence.env`

This probe is a fail-closed local capability artifact. It proves the local probe ran and records that native read_range, pinned-buffer registration, and device staging are not linked on this host. It separately executes the StdFs NVFS client spec and records local `read_range_bytes` bring-up evidence when that bounded file-backed helper passes. That local byte evidence is not caller-buffer DMA, pinned-buffer registration, or device staging, so it is provenance for an unsupported native state, not native streaming completion evidence.

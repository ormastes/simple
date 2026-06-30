# LLM Runtime svLLM Native Capability Probe

- status: `pass`
- source: `local_simple_svllm_capability_probe`
- reason: `native_runtime_capabilities_not_linked`
- read_range: `unsupported`
- pinned_buffer: `unsupported`
- device_staging: `unsupported`
- next_action: `implement native read_range, pinned-buffer registration, and device staging, then rerun this probe`
- surface_manifest: `build/llm_runtime_svllm_native_capability_probe/svllm_native_capability_probe_surface_manifest.tsv`
- surface_manifest_count: `5`
- surface_manifest_size: `691`
- surface_manifest_sha256: `0817ebbda9845e7ca400f419966c7fd5e0833627b1b6fa9af6922e24695738dd`
- env: `build/llm_runtime_svllm_native_capability_probe/evidence.env`

This probe is a fail-closed local capability artifact. It proves the local probe ran and records that native read_range, pinned-buffer registration, and device staging are not linked on this host. It is provenance for an unsupported native state, not native streaming completion evidence.

# Agent Task Plan: LLM Runtime vLLM/Torch Interface

Date: 2026-06-25

## Requirement Selection

Selected on 2026-06-25 from the user's request to do the first option first:

- Feature option: Option A from
  `doc/02_requirements/feature/llm_runtime_vllm_torch_interface_options.md`.
- NFR option: Option A from
  `doc/02_requirements/nfr/llm_runtime_vllm_torch_interface_options.md`.

Final requirements:

- `doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md`
- `doc/02_requirements/nfr/llm_runtime_vllm_torch_interface.md`

## Lane 1: vLLM Readiness Bridge

Owner: Codex

Status: implemented for Option A local readiness evidence.

Files:

- `src/app/llm_runtime/__init__.spl`
- `src/app/llm_runtime/manifest.spl`
- `src/app/llm_runtime/probe.spl`
- `src/app/llm_runtime/serve_plan.spl`
- `test/01_unit/app/llm_runtime/vllm_readiness_spec.spl`
- `test/unit/app/llm_runtime/vllm_readiness_spec.spl`
- `test/03_system/app/llm_runtime/feature/vllm_torch_readiness_spec.spl`
- `doc/06_spec/03_system/app/llm_runtime/feature/vllm_torch_readiness_spec.md`

Tasks:

1. Implement manifest validation and static readiness probe. Status: done.
2. Emit one absence-safe JSONL evidence event. Status: done.
3. Reuse dashboard diagnostics rendering for readback. Status: done.
4. Add absence-rendering unit and system tests. Status: done.
5. Run direct-env/runtime guard. Status: done.
6. Emit sanitized static vLLM serve-plan metadata without starting vLLM.
   Status: done.
7. Surface malformed adapter entries and invalid endpoint strings. Status: done.
8. Parse already-fetched `/v1/models` responses for the live vLLM lane.
   Status: done for response parsing only. This does not start vLLM, fetch HTTP,
   or call chat completions.
9. Build sanitized live request-plan metadata for vLLM endpoints.
   Status: done for plan-only `/v1/models` and `/v1/chat/completions` metadata.
   This redacts endpoint credentials, rejects invalid endpoints, reports missing
   chat bodies, and blocks unsupported chat parameters before transport.
10. Parse already-fetched `/v1/chat/completions` responses for the live vLLM
    lane. Status: done for response parsing only. This does not fetch HTTP,
    supervise vLLM, evaluate generated answer quality, or prove GPU serving.
11. Add live HTTP transport wrapper for planned vLLM requests.
    Status: done for using the owner HTTP facade after request planning. This
    does not start vLLM or prove a local endpoint is serving.
12. Add `vllm serve` lifecycle wrapper.
    Status: done for process-facade start/poll/stop boundaries. Endpoint
    readiness still requires the live transport/probe evidence path.
13. Add serve-readiness orchestration over lifecycle and `/v1/models` evidence.
    Status: done for pure preflight, observed-evidence summary, a policy-driven
    live orchestrator, and a synthetic sequence runner for unit evidence. This
    does not prove an installed local vLLM server or GPU serving.

Evidence:

- `simple check` passed for `src/app/llm_runtime` and the readiness specs.
- `test/01_unit/app/llm_runtime/vllm_readiness_spec.spl` passed after adding
  path-like model redaction and conservative Torch-blocked default coverage.
- `test/unit/app/llm_runtime/vllm_readiness_spec.spl` passed with the same
  mirrored coverage.
- `test/03_system/app/llm_runtime/feature/vllm_torch_readiness_spec.spl`
  passed after covering dashboard readback, Torch placeholder blocking,
  dynamic LoRA blocking, static serve-plan metadata, path/credential redaction,
  explicit absence rendering, and the local under-2s NFR.
- `test/01_unit/app/llm_runtime/vllm_live_models_probe_spec.spl` covers ready
  `/v1/models` responses, auth rejection, malformed bodies, wrong-model
  responses, invalid endpoints, and sensitive model redaction.
- `test/unit/app/llm_runtime/vllm_live_models_probe_spec.spl` mirrors the live
  response parsing coverage.
- `test/01_unit/app/llm_runtime/vllm_live_request_plan_spec.spl` covers
  sanitized request planning for models and chat-completions endpoints.
- `test/unit/app/llm_runtime/vllm_live_request_plan_spec.spl` mirrors the same
  request-plan coverage.
- `test/01_unit/app/llm_runtime/vllm_live_chat_probe_spec.spl` covers ready chat
  completion responses, auth rejection, malformed bodies, empty choices,
  missing assistant content, invalid endpoints, and generated-content redaction.
- `test/unit/app/llm_runtime/vllm_live_chat_probe_spec.spl` mirrors the same
  chat response parsing coverage.
- `test/01_unit/app/llm_runtime/vllm_live_transport_spec.spl` covers transport
  summary from fetched models/chat responses and no-fetch behavior for invalid
  or unsafe request plans.
- `test/unit/app/llm_runtime/vllm_live_transport_spec.spl` mirrors the same
  transport-wrapper coverage.
- `test/01_unit/app/llm_runtime/vllm_serve_lifecycle_spec.spl` covers no-spawn
  planning failures, spawned-pid adaptation, spawn failures, invalid pid status,
  and invalid pid stop behavior.
- `test/unit/app/llm_runtime/vllm_serve_lifecycle_spec.spl` mirrors the same
  lifecycle coverage.
- `test/01_unit/app/llm_runtime/vllm_serve_readiness_spec.spl` covers no-side
  effect preflight, invalid manifests, running-plus-ready observations,
  spawned-but-unpolled state, invalid endpoint plans, synthetic ready
  orchestration, wait-before-probe behavior, spawn failure, timeout cleanup, and
  auth-rejection cleanup policy.
- `test/unit/app/llm_runtime/vllm_serve_readiness_spec.spl` mirrors the same
  readiness-orchestration coverage.
- `test/01_unit/app/llm_runtime/vllm_live_environment_spec.spl` covers explicit
  `skipped` and `ready` live environment evidence for local vLLM/GPU
  availability combinations plus GPU label redaction.
- `test/unit/app/llm_runtime/vllm_live_environment_spec.spl` mirrors the same
  live environment evidence coverage.
- Resource-aware serve-readiness specs now cover skipped preflight and
  orchestrator short-circuit behavior before spawn/fetch when local vLLM/GPU
  resources are missing.
- `direct-env-runtime-guard` passed.
- `scripts/check/check-llm-tooling-public-absence-rendering.shs` passed and
  verifies public LLM/runtime manuals and evidence do not expose the internal
  Option-none marker outside folded executable source.
- `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.

## Lane 2: Torch/svLLM Placeholder Blockers

Owner: Codex if a later lane selects real Torch/svLLM readiness work.

Reported files:

- `src/lib/common/torch/dyn_sffi_ops.spl`
- `src/lib/gc_async_mut/torch/backend.spl`
- `src/lib/nogc_sync_mut/torch/backend.spl`
- `src/lib/gc_async_mut/torch/torch_training.spl`
- `src/lib/nogc_sync_mut/torch/torch_training.spl`
- `src/lib/gc_async_mut/svllm/model_executor/model_loader/manifest.spl`
- `src/lib/gc_async_mut/svllm/model_executor/model_loader/loader.spl`

Tasks:

1. Replace hard-disabled availability with real owner-module readiness.
   Status: partially done for `std.common.torch.dyn_sffi_ops.dyn_torch_available`;
   it now delegates to `rt_torch_available()` instead of returning `false`.
2. Replace placeholder returns with SFFI calls or explicit unavailable errors.
   Status: partially done for
   `std.common.torch.dyn_sffi_ops.dyn_torch_tensor_linalg_solve`; it now checks
   `rt_torch_available()` and delegates to existing
   `rt_torch_torchtensor_linalg_solve(a, b)` instead of returning unconditional `0`.
3. Stop hardcoded CUDA device behavior from being user-visible as correct.
   Status: done for public GC/NoGC backend CUDA placement, `Tensor.cuda`,
   stream creation, and optimizer state initialization. Explicit `device_id`
   arguments now flow through to the Torch SFFI instead of forcing CUDA device
   `0`; optimizer state no longer implicitly moves state tensors to CUDA `0`
   while no device-aware optimizer-state SFFI contract exists.
4. Make seed helpers either functional or explicitly unsupported.
   Status: done for GC async, NoGC async, and NoGC sync Torch training helpers;
   they now return `unsupported` instead of silently no-oping while no owner
   runtime manual-seed symbol exists.
5. Add loader tests for manifest parsing and non-throwing pack load behavior.
   Status: done for canonical v0 manifests, including non-empty tensor/chunk
   metadata materialization, digest-shape validation, and typed unavailable
   missing-root/missing-manifest handling. Filesystem-backed `manifest.sdn`
   loading and chunk existence/byte-length/SHA-256 verification are wired to
   the existing owner file facade. The interpreter file-hash owner path now
   computes real SHA-256 instead of returning the old 16-hex placeholder, and
   the Simple facade falls back to `sha256sum` only when running against an
   older runtime placeholder.
6. Prove manifest tensor offsets map to real chunk bytes.
   Status: done for single-chunk and sequential multi-chunk tensor byte ranges
   from a validated pack.
   `load_tensor_bytes_from_pack(root, tensor_name)` returns the declared byte
   range or typed errors such as `tensor_not_found`, `tensor_range_invalid`, and
   `chunk_error`. This does not claim async NVFS scheduling or device staging.
7. Expose deterministic stream-read segments for the future NVFS scheduler.
   Status: done for plan-only streamer metadata.
   `load_tensor_stream_plan_from_pack(root, tensor_name, pin_extents,
   device_staging)` validates the pack, returns ordered chunk read segments,
   carries pin/device-staging intent flags, and reports
   `plan_only_not_scheduled`.
8. Prevent false NVFS readiness claims in the bring-up std_fs adapter.
   Status: done for explicit unsupported coverage.
   The std_fs adapter specs assert `read_range`, `register_buffer`, and
   `unregister_buffer` return `unsupported`.

Evidence:

- `release/x86_64-unknown-linux-gnu/simple check
  src/lib/common/torch/dyn_sffi_ops.spl
  test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl
  test/unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl` passed.
- `test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl` passed.
- `test/unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl` passed.
- Generated/manual spec:
  `doc/06_spec/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.md`.
- The same spec now covers dynamic linalg solve delegation to the existing
  runtime SFFI.
- `release/x86_64-unknown-linux-gnu/simple check
  src/lib/nogc_sync_mut/io_runtime.spl
  src/lib/io_runtime.spl
  src/lib/gc_async_mut/svllm/model_executor/model_loader/loader.spl
  test/01_unit/lib/gc_async_mut/svllm/model_loader_manifest_spec.spl
  test/unit/lib/gc_async_mut/svllm/model_loader_manifest_spec.spl` passed.
- `test/01_unit/lib/gc_async_mut/svllm/model_loader_manifest_spec.spl` passed
  with 7/7 scenarios.
- `test/unit/lib/gc_async_mut/svllm/model_loader_manifest_spec.spl` passed
  with 7/7 scenarios.
- `direct-env-runtime-guard --working`, `direct-env-runtime-guard --staged`,
  `check-llm-tooling-public-absence-rendering.shs`, and the `doc/06_spec`
  executable-spec layout check passed after the file-backed pack loader slice.
- `release/x86_64-unknown-linux-gnu/simple check
  src/lib/gc_async_mut/svllm/model_executor/model_loader/loader.spl
  src/lib/gc_async_mut/svllm/model_executor/model_loader/__init__.spl
  test/01_unit/lib/gc_async_mut/svllm/model_loader_tensor_bytes_spec.spl
  test/unit/lib/gc_async_mut/svllm/model_loader_tensor_bytes_spec.spl` passed.
- `test/01_unit/lib/gc_async_mut/svllm/model_loader_tensor_bytes_spec.spl`
  passed with multi-chunk span coverage.
- `test/unit/lib/gc_async_mut/svllm/model_loader_tensor_bytes_spec.spl` passed
  with multi-chunk span coverage.
- `test/01_unit/lib/gc_async_mut/svllm/model_loader_stream_plan_spec.spl`
  covers single-segment plans, cross-chunk ordered segments, pin/device-staging
  intent flags, and `plan_only_not_scheduled`.
- `test/unit/lib/gc_async_mut/svllm/model_loader_stream_plan_spec.spl` mirrors
  the same stream-plan coverage.
- `test/01_unit/lib/gc_async_mut/svllm/nvfs_client/std_fs_spec.spl` and
  `test/unit/lib/gc_async_mut/svllm/nvfs_client/std_fs_spec.spl` cover explicit
  unsupported status for `read_range`, `register_buffer`, and
  `unregister_buffer`.
- `release/x86_64-unknown-linux-gnu/simple check
  src/lib/gc_async_mut/torch/backend.spl
  src/lib/nogc_sync_mut/torch/backend.spl
  src/lib/gc_async_mut/torch/mod.spl
  src/lib/nogc_sync_mut/torch/mod.spl
  src/lib/gc_async_mut/torch/torch_training.spl
  src/lib/nogc_sync_mut/torch/torch_training.spl
  src/lib/gc_async_mut/torch/optim.spl
  src/lib/nogc_sync_mut/torch/optim.spl
  test/01_unit/lib/common/torch/torch_device_placement_status_spec.spl
  test/unit/lib/common/torch/torch_device_placement_status_spec.spl` passed.
- `test/01_unit/lib/common/torch/torch_device_placement_status_spec.spl`
  passed with 4/4 scenarios.
- `test/unit/lib/common/torch/torch_device_placement_status_spec.spl` passed
  with 4/4 scenarios.

Still open:

- Full svLLM streaming through NVFS remains open: async scheduling, native
  `read_range` execution, pinned buffer registration, and device staging are not
  covered by the filesystem byte range reader or plan-only stream metadata.
- Live CUDA placement against libtorch and device-preserving optimizer state for
  already-CUDA parameters remain open.

Runtime-adjacent decision record for seed helpers:

- `runtime_need`: deterministic Torch random seed configuration.
- `facade_checked`: `std.*.torch.torch_training` helpers, Torch SFFI exports,
  C++ `torch_sffi` runtime exports, and Rust runtime Torch exports.
- `chosen_path`: `reuse-facade` with explicit unsupported status in the Torch
  owner training facade.
- `rejected_shortcuts`: adding a raw `rt_torch_manual_seed` alias without
  owner runtime implementation and deterministic seed parity coverage.

## Lane 3: Static LoRA Serve Harness

Owner: Codex

Tasks:

1. Generate sanitized vLLM serve command metadata. Status: done.
2. Probe `/v1/models` on a configured endpoint. Status: deferred to live
   serving selection for actual HTTP transport; request planning and response
   parsing are implemented.
3. Record base model and adapter ids. Status: partially done; public metadata
   records a redacted base model and adapter count only.
4. Add skipped evidence state for missing local vLLM/GPU. Status: done for the
   pure evidence classifier and resource-aware serve-readiness preflight.
   Missing resources emit explicit `skipped` reasons before spawn/fetch.
5. Surface vLLM readiness evidence in the dashboard diagnostics panel. Status:
   done for JSONL readback; the dashboard collector recognizes
   `llm_runtime_vllm_*` events and renders latest status/reason without
   exposing internal absence markers. This is evidence readback only, not a
   live start/stop control surface.
6. Add dashboard operator controls for vLLM lifecycle intent. Status: done for
   dashboard action-intent readback. The web dashboard now renders
   `preflight`, `start`, `poll`, `probe`, and `stop` controls and exposes
   `/api/vllm/control` JSONL evidence for those intents. The dashboard collector
   now derives those decisions from `app.llm_runtime.dashboard_live_control`;
   live process execution remains in runtime-owned lifecycle/readiness facades
   rather than being imported directly by dashboard rendering.
7. Add owner-side dashboard control execution under `app.llm_runtime`. Status:
   done for runtime-owned control decisions and live wrapper. The pure
   `dashboard_live_control` module validates `preflight`, `start`, `poll`,
   `probe`, and `stop` without importing process/HTTP backends; the
   `dashboard_live_control_executor` module composes `serve_lifecycle`,
   `serve_readiness`, and `live_transport` for actual live execution when the
   runtime owner wires it. Unit coverage stays on the pure boundary to avoid
   live process teardown diagnostics.

## Sidecars

- Spark/explorer: smallest vLLM/Torch scope review.
- Normal reviewer: planning and evidence gap review.

## Deferred

- PEFT/TRL training loop.
- Dynamic LoRA resolver.
- Torch model execution beyond readiness probes.
- Live endpoint availability evidence against an installed local `vllm`.
- Live dashboard route wiring of start, poll, probe, and stop against an
  installed local `vllm`; the runtime owner now has a live wrapper, but the web
  dashboard route remains intent-only until integration evidence proves the
  process/HTTP imports do not reintroduce dashboard test teardown diagnostics.

Runtime-adjacent decision record for live HTTP transport:

- `runtime_need`: HTTP GET/POST to a configured local vLLM-compatible endpoint.
- `facade_checked`: `app.io.http_sffi`, `std.nogc_sync_mut.io.http_sffi`,
  `std.nogc_async_mut.io.http_sffi`, pure HTTP parser/builders, and process
  facades.
- `chosen_path`: `reuse-facade` with `std.nogc_sync_mut.io.http_sffi.http_request`.
- `rejected_shortcuts`: direct `rt_http_request`, shell/curl, or process-run
  transport inside `app.llm_runtime`.

Runtime-adjacent decision record for vLLM lifecycle:

- `runtime_need`: process lifecycle for local `vllm serve`.
- `facade_checked`: `app.io.mod` process exports and owner `app.io.process_ops`.
- `chosen_path`: `reuse-facade` with `app.io.mod.process_spawn_async`,
  `process_is_running`, and `process_kill`.
- `rejected_shortcuts`: direct `rt_process_*` imports, shell lifecycle wrappers,
  and treating process spawn as endpoint readiness.
Runtime-adjacent decision record for vLLM serve-readiness orchestration:

- `runtime_need`: summarize process lifecycle and `/v1/models` readiness as one
  dashboard-consumable state.
- `facade_checked`: existing `serve_lifecycle`, `live_request_plan`, and
  `live_transport` module APIs.
- `chosen_path`: `reuse-facade` with pure composition over existing lifecycle
  and transport result objects.
- `rejected_shortcuts`: hidden process polling inside unit-only readiness,
  shell/curl readiness checks, and treating spawned PID as endpoint readiness.

Runtime-adjacent decision record for dashboard live control execution:

- `runtime_need`: execute dashboard-requested vLLM `preflight`, `start`,
  `poll`, `probe`, and `stop` actions without making dashboard rendering own
  process or HTTP backends.
- `facade_checked`: `serve_lifecycle`, `serve_readiness`, `live_transport`,
  `serve_plan`, `live_request_plan`, and `live_environment`.
- `chosen_path`: split pure decision evidence from `dashboard_live_control`
  and live execution in `dashboard_live_control_executor`.
- `rejected_shortcuts`: importing process/HTTP modules into dashboard
  collectors, shell lifecycle wrappers, and exposing model ids or response
  bodies in JSONL evidence.

- Full dashboard controls for vLLM lifecycle.

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
  path-like model redaction, explicit Torch-unavailable evidence, and injected
  Torch-ready coverage.
- `test/unit/app/llm_runtime/vllm_readiness_spec.spl` passed with the same
  mirrored coverage.
- `test/03_system/app/llm_runtime/feature/vllm_torch_readiness_spec.spl`
  passed after covering dashboard readback, Torch unavailable evidence,
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
  absence marker outside folded executable source.
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
   Status: done for the static vLLM readiness bridge and dynamic Torch facade.
   `std.common.torch.dyn_sffi_ops.dyn_torch_available` delegates to
   `rt_torch_available()` instead of returning `false`, and
   `app.llm_runtime.probe.llm_runtime_probe_manifest(...)` now reports default
   Torch readiness from that facade as `ready` or `unavailable` instead of
   hard-coding `blocked`. Deterministic specs use
   `llm_runtime_probe_manifest_with_torch_status(...)` to prove both
   unavailable and ready outcomes without depending on host libtorch.
2. Replace placeholder returns with SFFI calls or explicit unavailable errors.
   Status: partially done for
   `std.common.torch.dyn_sffi_ops.dyn_torch_tensor_linalg_solve`; it now checks
   `rt_torch_available()` and delegates to existing
   `rt_torch_torchtensor_linalg_solve(a, b)` instead of returning unconditional `0`.
   A status-returning companion,
   `dyn_torch_tensor_linalg_solve_result(a, b)`, now reports
   `libtorch_unavailable`, `invalid_handle`, or
   `runtime_returned_null_handle` explicitly while the legacy handle-returning
   API remains compatible. The C++ Torch runtime boundary now returns `0` for
   missing linalg-solve tensor handles instead of panicking before the Simple
   status wrapper can classify the failure.
   Follow-up status wrappers now cover the dynamic tensor construction/value
   copy surface in `std.common.torch.dyn_sffi_tensor_ops`:
   `dyn_torch_tensor_from_values_1d_result`,
   `dyn_torch_tensor_from_values_2d_result`, and
   `dyn_torch_tensor_copy_values_result` report `libtorch_unavailable`,
   `invalid_shape`, `invalid_handle`, `empty_or_invalid_tensor`,
   `buffer_allocation_failed`, or `runtime_copy_failed` while legacy
   handle/array-returning APIs remain compatible.
3. Stop hardcoded CUDA device behavior from being user-visible as correct.
   Status: done for public GC/NoGC backend CUDA placement, `Tensor.cuda`,
   stream creation, and optimizer state initialization. Explicit `device_id`
   arguments now flow through to the Torch SFFI instead of forcing CUDA device
   `0`; optimizer state now queries `rt_torch_torchtensor_device(param)` and
   moves zero state tensors to the same CUDA device when parameters are already
   CUDA-backed.
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
   Status: done for explicit unsupported coverage, then advanced with a local
   byte-returning read helper.
   The std_fs adapter specs assert trait `read_range`, `register_buffer`, and
   `unregister_buffer` remain unsupported until a real caller-buffer write
   primitive and pinned-buffer adapter exist. They also cover
   `read_range_bytes`, a local helper that returns bounded file-backed bytes
   through the owner file facade without claiming pinned DMA or device staging.

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
- The same spec now covers explicit dynamic linalg solve status readback for
  unavailable or invalid-handle cases without claiming live libtorch execution.
- The same spec now covers C++ runtime/header alignment so invalid native
  linalg-solve handles return the failure handle contract instead of panicking.
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
  `test/unit/lib/gc_async_mut/svllm/nvfs_client/std_fs_spec.spl` cover
  unsupported trait `read_range`/buffer registration, local `read_range_bytes`
  payload correctness, and out-of-bounds rejection.
- `src/lib/gc_async_mut/svllm/model_executor/model_loader/streaming_readiness.spl`
  adds a single readiness gate that combines the existing tensor stream plan
  with native `read_range`, pinned-buffer, and device-staging capability
  statuses. The default pack readiness reports `blocked` with
  `native_read_range_unavailable`; tests also prove it only reports `ready`
  when all native statuses are `ready`.
- The streaming readiness gate now emits sanitized JSONL evidence
  (`svllm_streaming_readiness`) with plan status, execution status, segment
  count, total byte length, and normalized native capability statuses. Specs
  prove blocked, ready, loader-error, and unknown-status normalization paths
  without requiring live NVFS scheduling, pinned buffers, or device staging.
- The streaming readiness gate also records `local_read_bytes` evidence for
  file-backed pack roots. `svllm_streaming_readiness_from_local_pack(...)`
  proves local byte reads match the planned byte length and emits
  `local_read_bytes=ready` while keeping full streaming `blocked` until native
  `read_range`, pinned-buffer registration, and device staging are ready.
  Missing tiny pack chunk fixtures were restored so the tensor-byte,
  stream-plan, and local-read readiness specs execute in clean workspaces.
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
  passed with 5/5 scenarios, including same-parameter-device optimizer state
  initialization.
- `test/unit/lib/common/torch/torch_device_placement_status_spec.spl` passed
  with 5/5 scenarios, including same-parameter-device optimizer state
  initialization.
- `test/01_unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.spl` passed
  with 3/3 scenarios, proving explicit dynamic tensor construction and value
  copy statuses without requiring live libtorch.
- `test/unit/lib/common/torch/dyn_sffi_tensor_ops_status_spec.spl` passed with
  3/3 mirrored scenarios.

Still open:

- Full svLLM streaming through NVFS remains open: async scheduling, true pinned
  buffer registration, and device staging are now surfaced by absence-safe JSONL
  streaming readiness evidence but still report unavailable until real native
  adapters are implemented. The std_fs adapter only proves local file-backed
  byte reads through `read_range_bytes`, and readiness now reports that local
  evidence separately as `local_read_bytes`; trait `read_range` remains
  unsupported because no pointer-write primitive exists for caller buffers.
- Live CUDA placement against libtorch remains open; source-contract coverage
  now proves optimizer state preserves the parameter device for already-CUDA
  parameters, but end-to-end optimizer execution against a live libtorch CUDA
  installation remains unproven.

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
8. Add runtime control response surface. Status: done for in-process JSONL
   response generation and direct app execution through
   `src/app/llm_runtime/control_cli.spl`; the source CLI dispatcher also
   registers `llm-runtime-control`, and the tracked release binary smoke now
   proves the rebuilt top-level command dispatches to the runtime control CLI
   instead of treating `llm-runtime-control` as a source filename.
9. Harden pure vLLM planning evidence constructors. Status: done for
   `serve_plan`, `live_request_plan`, `live_environment`, and
   `dashboard_live_control`; these now precompute JSONL without post-construction
   field mutation, and request/serve private helpers use module-specific names.
10. Add rebuilt standalone command evidence. Status: done for
    `src/app/llm_runtime/control_cli.spl`: `native-build` produced
    `build/llm_runtime/llm_runtime_control_cli`, and the rebuilt binary emitted
    public JSONL for planned preflight, skipped start, and usage/error cases.
    Public pid absence renders as `0` so native negative-sentinel formatting
    cannot leak huge integer values.
11. Add local resource detection for runtime control command. Status: done for
    direct app/source execution: `--detect-resources` uses the
    `app.io.mod.process_run_timeout` facade for bounded `vllm --version` and
    `nvidia-smi --query-gpu=name --format=csv,noheader` probes before any serve
    spawn or HTTP readiness plan. Explicit `--vllm-available` and
    `--gpu-available` flags still override detection for deterministic tests and
    harnesses. This classifies local host capability only; it does not prove a
    live endpoint is serving models.
12. Add focused top-level command registration evidence. Status: done for
    source and Rust-driver registration: mirrored SPipe specs now prove
    `llm-runtime-control` is present in `src/app/cli/dispatch/table.spl`, routed
    by `src/app/cli/main_part2.spl` to `src/app/llm_runtime/control_cli.spl`,
    shown in CLI help, and registered in the Rust driver app-command table plus
    Simple-app dispatch allow-list. `cargo check -p simple-driver` passes for
    the driver table change, `cargo build -p simple-driver` produced a rebuilt
    debug driver, and `src/compiler_rust/target/debug/simple
    llm-runtime-control ...` now reaches the Simple control CLI with planned,
    usage, and missing-local-vLLM JSONL outputs instead of treating the command
    name as a missing file. Release artifact evidence is done for the tracked
    `release/x86_64-unknown-linux-gnu/simple` binary: it was refreshed from
    `cargo build --manifest-path src/compiler_rust/Cargo.toml --release -p
    simple-driver --bin simple`, and the focused binary smoke
    `test/03_system/feature/app/cli/llm_runtime_control_binary_smoke_spec.spl`
    proves `simple llm-runtime-control --action preflight ...` emits
    `llm_runtime_vllm_dashboard_control_execution` JSONL instead of
    `file not found: llm-runtime-control`.
13. Move web dashboard control route onto the dashboard-safe vLLM collector
    facade. Status: done for `/api/vllm/control` returning
    `llm_dashboard_vllm_control_panel` JSONL from
    `collect_llm_dashboard_vllm_control_action(...)`. The collector delegates to
    `llm_runtime_execute_dashboard_control(...)` for planning, but the web
    dashboard server does not import the live executor or perform process/HTTP
    teardown. Live side effects remain runtime-owner-only behind the dedicated
    boundary.
14. Add pure dashboard/live-executor boundary evidence. Status: done for
    `llm_runtime_dashboard_live_boundary(...)` and
    `llm_runtime_dashboard_live_boundary_jsonl(...)`. The evidence classifies
    `preflight` as `intent-only`, side-effecting actions as
    `executor-required` only when local vLLM/GPU resources are available, and
    missing-resource cases as `blocked` with `process_access=not_used`,
    `http_access=not_used`, and `acceptance_status=not_live_evidence`. This is
    not live endpoint proof; it is a dashboard-safe gate that keeps process/HTTP
    execution owned by `dashboard_live_control_executor`. Follow-up hardening
    aligned the JSONL helper with the object path so planned `preflight` evidence
    remains `requires_runtime_executor=false`.
15. Accept dashboard/query-style runtime control arguments. Status: done for
    `--key=value` and `key=value` forms on action, base model, endpoint, pid,
    and resource flags. This keeps direct app execution and future dashboard
    bridge calls from degrading to usage JSONL when arguments arrive in
    query-string shape.
16. Accept dashboard web route query-style runtime control arguments. Status:
    done for `/api/vllm/control?action=...&base_model=...&endpoint=...` plus
    `vllm_available`/`gpu_available` resource flags. The route forwards these
    values through the dashboard-safe collector facade into the runtime-owned
    planner, so missing local resources produce explicit `skipped` evidence and
    endpoint/model overrides can plan preflight without exposing model ids.
17. Wire side-effect dashboard actions through runtime-owner execution JSONL.
    Status: done for deterministic
    `/api/vllm/control?action=start|poll|probe|stop` evidence:
    `src/app/web_dashboard/server.spl` keeps preflight on the collector path but
    routes side-effect API responses through
    `llm_runtime_execute_dashboard_control_jsonl(...)`.
    `test/03_system/feature/app/web_dashboard/vllm_control_route_spec.spl`
    proves the route returns `llm_runtime_vllm_dashboard_control_execution`
    JSONL for missing-resource or invalid-pid inputs, so no process is spawned
    or stopped during the system spec. The host-dependent live executor remains
    in `app.llm_runtime.dashboard_live_control_executor`. The route spec also
    proves authenticated preflight and query-style override preflight keep
    `requires_runtime_executor=false`, preserving the dashboard-intent boundary.

## Sidecars

- Spark/explorer: smallest vLLM/Torch scope review.
- Normal reviewer: planning and evidence gap review.

## Deferred

- PEFT/TRL training loop.
- Dynamic LoRA resolver.
- Torch model execution beyond readiness probes.
- Live endpoint availability evidence against an installed local `vllm`.
- Host-dependent live dashboard execution of start, poll, probe, and stop
  against an installed local `vllm`; dashboard route wiring is implemented and
  already emits runtime-owner execution JSONL for side-effect actions, but proof
  that the executor starts, probes, and stops a real local process remains
  deferred until a suitable host is available.

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

Runtime-adjacent decision record for runtime control resource detection:

- `runtime_need`: classify local vLLM/GPU capability for control preflight
  without requiring manual resource flags.
- `facade_checked`: `app.io.mod.process_run_timeout`.
- `chosen_path`: `reuse-facade` with bounded command probes in the runtime
  control CLI before side-effecting serve or HTTP checks are planned.
- `rejected_shortcuts`: raw `rt_process_run` imports, shell pipelines, dashboard
  owned detection, and treating local tool presence as endpoint readiness.

- Live-executed dashboard controls for vLLM lifecycle. The dashboard route now
  accepts query-style action/model/endpoint/resource inputs and returns
  runtime-owned plan evidence, but it still deliberately avoids owning live
  process or HTTP side effects until integration evidence proves the
  `dashboard_live_control_executor` path is safe to call from the web route.

## 2026-06-26 Public Absence Assertion Hardening

The vLLM/Torch readiness, live probe, live transport, live request-plan, serve
readiness, serve lifecycle, and system readiness specs now assert public
absence/redaction through split-count checks instead of boolean
negative-containment wrappers. This keeps the executable evidence
aligned with the public absence-marker policy while preserving the same observable
behavior: missing/private values must render as explicit statuses or be absent
from JSONL, never as the internal absence marker.

Evidence:

- Focused `simple check` passed for the 17 edited vLLM/Torch spec files.
- Focused interpreter tests passed for the edited unit/system specs; serve
  lifecycle/readiness still emit the known subprocess diagnostic line while the
  runner reports all examples passed and exits successfully.
- `simple spipe-docgen` regenerated 17 matching manuals with 100% complete docs.
- The targeted source/manual scan found no remaining boolean
  negative-containment or forced-failure placeholder wrappers in the vLLM/Torch
  readiness artifacts.

## 2026-06-26 Public Manual Absence Marker Helper Hardening

The vLLM lifecycle, control CLI, live environment, models probe, serve
readiness, chat probe, dashboard live control, live transport, and request-plan
specs now route internal absence-marker assertions through `absence_marker()`
helpers instead of embedding the literal marker in executable assertions. This
keeps generated operator manuals from displaying the internal marker in public
expected-code snippets while preserving the same rendered-output contract.

Evidence:

- Focused `simple check` passed for the 18 edited vLLM spec files.
- Focused interpreter tests passed for the 18 edited unit specs; lifecycle,
  control CLI, serve readiness, and dashboard live control still emit the known
  subprocess diagnostic line inside passing runs.
- `simple spipe-docgen` regenerated 18 matching manuals with 100% complete docs.
- Targeted source scan found no remaining direct literal-marker split
  assertions in `test/01_unit/app/llm_runtime` or
  `test/unit/app/llm_runtime`.

## 2026-06-26 vLLM Control CLI JSON Escaping Hardening

The runtime control CLI now builds
`llm_runtime_vllm_dashboard_control_execution` JSONL with the shared escaped
JSON helper path instead of manual string concatenation. This keeps rejected
user-supplied action text from breaking public JSONL while preserving explicit
missing-resource and absence-marker behavior.

Evidence:

- Focused `simple check` passed for `src/app/llm_runtime/control_cli.spl` and
  both mirrored `vllm_control_cli_spec.spl` files.
- Both mirrored control CLI specs now include 9 scenarios, including quoted
  rejected-action JSON escaping and absence-marker split-count checks.
- Focused interpreter test runs reported 9 passed and 0 failed for both mirrored
  specs; the runner still prints its known per-file subprocess diagnostic line.
- `simple spipe-docgen` regenerated the matching manuals and `doc/06_spec/INDEX.md`.

## 2026-06-26 vLLM Runtime Manual Sync

The stale canonical `doc/06_spec/01_unit/app/llm_runtime/` and
`doc/06_spec/unit/app/llm_runtime/` manual copies for the seven vLLM
live/serve specs were synced from their generated mirrors. This keeps the
operator manuals aligned with the current absence-safe generated scenario
blocks for live chat, environment, models, request plan, transport, serve
lifecycle, and serve readiness.

Evidence:

- `simple check` passed for the seven affected `test/01_unit/app/llm_runtime`
  source specs.
- Interpreter smoke passed for `vllm_live_chat_probe_spec.spl`.
- Canonical/manual duplicate comparisons returned `0` for the seven synced
  `01_unit` and `unit` vLLM manuals.
- `check-llm-tooling-public-absence-rendering.shs`, direct env/runtime guards,
  and the `doc/06_spec` executable-spec layout guard passed.

## 2026-06-28 vLLM Dashboard PID Public Rendering Hardening

The dashboard runtime-owner JSONL path and dashboard collector panel now match
the direct `llm-runtime-control` CLI public PID policy: non-positive internal
process sentinels render as `0` in public text, HTML, and JSONL while the
in-memory execution object may still carry `-1` for internal control flow. This
keeps missing/invalid process identifiers out of dashboard evidence without
weakening the fail-closed invalid-pid behavior.

## 2026-06-28 Requirement Sync for Implemented Live Boundary

The selected Option A requirement docs now include the implemented live request
planning, response parsing, serve lifecycle, dashboard control boundary,
bounded resource detection, and Torch/svLLM unavailable-status contracts. The
same sync keeps host-dependent proof explicitly deferred: real local vLLM/GPU
serving, live dashboard execution against an installed vLLM server, full NVFS
streaming, and live CUDA/libtorch optimizer execution remain open until the
host resources and native adapters are available.

## 2026-06-28 Runtime Operator Guide Sync

Added `doc/07_guide/app/llm/llm_runtime_vllm_torch_interface.md` as the
operator-facing guide for the runtime evidence boundary. It records the public
absence-text contract, dashboard-control ownership rules, implemented evidence,
and remaining host-dependent gates so the runtime tracking rows no longer rely
only on the generic dashboard guide.

## 2026-06-29 svLLM Native Streaming Evidence Hardening

`scripts/check/check-llm-runtime-svllm-native-streaming-evidence.shs` now
produces the `SVLLM_NATIVE_EVIDENCE_ENV` contract consumed by strict svLLM
readiness and the aggregate LLM gate. The checker runs the local svLLM
readiness wrapper, records local file-backed byte-read evidence separately, and
keeps native streaming failed with concrete blockers until native read_range,
pinned buffer registration, and device staging all report `ready`.
It also hashes the nested local-readiness env, log, and report so the strict
native wrapper can prove exactly which local readiness run it consumed before
evaluating native capability evidence.

The native streaming wrapper now consumes explicit host capability inputs:
`SVLLM_NATIVE_READ_RANGE_STATUS`, `SVLLM_NATIVE_PINNED_BUFFER_STATUS`, and
`SVLLM_NATIVE_DEVICE_STAGING_STATUS`. Missing inputs default to `unsupported`,
but a configured host can provide `ready` values without editing tests or
source fixtures. The wrapper records `svllm_native_streaming_capability_source`,
`svllm_native_streaming_capability_provenance_status`,
`svllm_native_streaming_blocked_gates`,
`svllm_native_streaming_primary_blocked_gate`, and
`svllm_native_streaming_next_action`; strict local readiness forwards those
native blocker fields, and the aggregate forwards them in
`llm_goal_evidence_svllm_local_detail`.

Strict native evidence also requires a non-default
`SVLLM_NATIVE_CAPABILITY_SOURCE` naming the host probe or artifact that proved
ready native capabilities. Setting all native status env values to `ready`
without that provenance now fails with `capability_provenance` instead of
claiming native streaming completion from env defaults alone.
It also requires `SVLLM_NATIVE_CAPABILITY_EVIDENCE_PATH` to point at a
non-empty schema-v1 probe artifact with
`svllm_native_capability_source` matching
`SVLLM_NATIVE_CAPABILITY_SOURCE`,
`svllm_native_capability_probe_event=svllm_native_capability_probe`,
`svllm_native_capability_probe_status=pass`,
`svllm_native_capability_probe_exit=0`, and reported read-range, pinned-buffer,
and device-staging statuses that match the wrapper inputs. Ready native status
env values plus a source label but without that artifact fail with
`capability_evidence`, and the wrapper records artifact SHA-256, size, mtime,
source, schema version, probe event/status/exit, reported native statuses,
`svllm_native_streaming_pass_integrity_status` plus
`svllm_native_streaming_pass_integrity_reason` so aggregate detail can
distinguish a real native pass from env-only status injection.

Follow-up hardening binds `SVLLM_NATIVE_CAPABILITY_SOURCE` to the probe
artifact itself through `svllm_native_capability_source`. A ready-status env
plus an artifact from another source now remains `capability_evidence` instead
of satisfying native streaming completion.

## 2026-06-29 Torch Optimizer Evidence Hardening

`scripts/check/check-llm-runtime-torch-cuda-optimizer-probe.shs` now normalizes
the Simple/libtorch CUDA optimizer evidence contract even when the probe exits
early. The probe reports the required gate list, the current blocked gate, and
normalized libtorch/CUDA/parameter/gradient/optimizer-step fields. On this host
the lane remains `unavailable` with `blocked_gate=libtorch`; strict-host
aggregate runs should fail that gate until a configured libtorch CUDA runtime
executes the optimizer step and reports `status=pass`.

The optimizer wrapper now also emits `torch_cuda_optimizer_probe_blocked_gates`
and `torch_cuda_optimizer_probe_primary_blocked_gate` while preserving the
legacy singular `torch_cuda_optimizer_probe_blocked_gate` key. The aggregate
uses the plural key when available and forwards both the compact list and first
blocked gate in `llm_goal_evidence_torch_optimizer_detail`.
It also records Python Torch host visibility (`python_torch_module_status`,
version, CUDA availability, device count), `system_libtorch_status`, and a
hashed system libtorch probe log, so a host with Python Torch/CUDA installed
but no Simple-visible libtorch is reported as a Simple/runtime integration
blocker rather than a general CUDA absence and the blocker is tied to the exact
`ldconfig`/availability probe that ran.
The wrapper now writes a Torch optimizer surface manifest with path, size, and
SHA-256 rows for the live probe, Torch facades, backend/optimizer/training
sources, and focused Torch specs. The aggregate forwards the manifest count,
size, and SHA-256 in `llm_goal_evidence_torch_optimizer_detail` so a strict
review can bind WARN/PASS evidence to the checked source surface.

Follow-up hardening makes wrapper PASS stricter than the probe status line
alone. If the Simple probe emits `status=pass`, the wrapper now independently
requires zero wrapper exit, a non-empty hashed probe log, exactly one complete
proof record for status, required gates, libtorch/CUDA availability, CUDA
parameter placement, gradient handle, optimizer step, and before/after sums,
plus normalized libtorch/CUDA availability, CUDA parameter placement, a nonzero
gradient handle, an attempted optimizer step, and numeric `after_sum <
before_sum`; otherwise it rewrites the lane to fail with
`wrapper_pass_integrity_failed:*` and `blocked_gate=probe_log_integrity`. The
aggregate forwards the log SHA-256, log size, record counts,
`torch_cuda_optimizer_probe_sum_decreased_status`,
`torch_cuda_optimizer_probe_pass_integrity_status`, and
`torch_cuda_optimizer_probe_pass_integrity_reason`.

## 2026-06-29 Fine-Tune Acceptance Evidence Hardening

`scripts/check/check-llm-finetune-acceptance-evidence.shs` now preserves the
retry7 normal-acceptance gate as a machine-readable blocker contract. The env
records required gates, compact blocked gates, training allowance, upstream
attempt/cache refs, model-manifest/eval-result paths and presence, deployable
model-manifest status, target-eval status, required accuracy, decision status,
license, safety, deployment, app-handoff doc, handoff usage, retry6 next action,
and final next action.
It also records provenance and local artifact integrity for the retry7 gate log,
the upstream retry5 attempt/cache artifacts, the retry7 attempt record, model
manifest, eval result, and handoff doc: artifact status, SHA-256, size,
model-manifest schema version, manifest attempt id, base model/revision,
model-artifact status/hash, eval schema version, eval status, metric
name/value/target, dataset id/split/checksum, sample count, and
`llm_finetune_acceptance_pass_integrity_status`.
On this host the lane remains failed with `BLOCKED_RETRY6_NOT_READY` and
blocked gates for retry6 training/eval, model/eval artifacts, target eval,
decision, license, safety, deployment, and app handoff.

The acceptance wrapper now also records
`llm_finetune_acceptance_primary_blocked_gate` and derives
`llm_finetune_acceptance_next_action` from the first normalized blocked gate.
Strict aggregate review can therefore distinguish a retry6 training/eval
blocker from later model manifest, eval result, target eval, review decision,
license, safety, deployment, or app-handoff blockers without parsing the whole
gate log. The aggregate detail forwards the gate-log and upstream retry5
artifact hashes so a blocker report can be traced to the exact cached data and
attempt evidence it consumed.

The acceptance wrapper pass condition is intentionally stricter than the retry7
gate line alone: it requires retry7 `acceptance_allowed=true` and normalized
`llm_finetune_acceptance_blocked_gates=none`, plus
`llm_finetune_acceptance_pass_integrity_status=pass` from local artifact
hashing and schema/linkage extraction. Follow-up hardening also requires a
hashable model artifact, deployable model manifest, passing eval result, eval
target metadata, dataset checksum, eval sample count, and deployable handoff
usage before PASS integrity can be `pass`. The strict fine-tune guard also
rejects an acceptance env that reports `llm_finetune_acceptance_status=pass`
without that pass-integrity field. A future retry7 PASS cannot mask missing
model/eval/license/safety/deployment/app-handoff evidence, non-deployable
handoff text, or status-only artifact placeholders.

## 2026-06-29 vLLM Host Evidence Hardening

`scripts/check/check-llm-runtime-vllm-host-probe.shs` now normalizes the local
vLLM live-serving proof into required and blocked gates. The env records the
required gate list, compact blocked gates, selected base model, endpoint,
`vllm` command path, Python `vllm` module status, local vLLM/GPU command
statuses, readiness status, endpoint status, models-list status, and
models-list reason, plus readiness-log size, SHA-256, and serve-readiness run
event count. It also writes bounded local host probe logs with SHA-256 hashes
for `vllm --version`, Python `vllm` module/version discovery, and `nvidia-smi`,
so unavailable-host evidence is tied to concrete command/module probes instead
of status labels alone.
It now also writes a vLLM host surface manifest with path, size, and SHA-256
rows for the runtime control/readiness sources and unit specs that define the
readiness path, and the aggregate vLLM detail forwards the manifest count,
size, and SHA-256. Missing-host vLLM evidence is therefore tied to both the
host probes and the exact checked local source/spec surface.
On this host the lane remains `unavailable` with
`blocked_gates=local_vllm|python_vllm_module|serve_preflight|endpoint_reachable|models_listed`;
strict-host aggregate runs should fail that gate until the local vLLM
executable and Python module are installed, serve readiness reaches `ready`,
the endpoint is configured, and `/v1/models` lists the selected base model.

The host probe now records
`llm_runtime_vllm_host_probe_primary_blocked_gate` and derives next action from
that first normalized blocker. Its models-list gate treats
`models_status=ready` as satisfying `models_listed`, matching the strict pass
condition and avoiding a false blocker on configured hosts.
The host probe PASS integrity also requires `models_reason=models_endpoint_ready`
and exactly one `llm_runtime_vllm_serve_readiness_run` event in the non-empty
hashed readiness log. Follow-up hardening also makes the Python `vllm` module a
required gate: a PASS now requires `python_vllm_module_status=available` with a
non-missing origin, so an executable-only host cannot satisfy strict local vLLM
completion.

The runtime control CLI now exposes a `readiness` action that routes through
`llm_runtime_vllm_serve_readiness_orchestrate_with_resources(...)` instead of
the plan-only preflight path. The host probe uses that action, so a configured
host can produce a real pass from `llm_runtime_vllm_serve_readiness_run` with
`status=ready`, `endpoint=configured`, and `models_status=ready`; missing local
vLLM/GPU hosts still produce bounded `skipped` evidence without spawning.

Follow-up hardening makes the wrapper PASS stricter than those normalized
status fields alone. A PASS now also requires
`llm_runtime_vllm_host_probe_pass_integrity_status=pass`, which verifies
`blocked_gates=none`, event `llm_runtime_vllm_serve_readiness_run`, zero CLI
exit, local vLLM executable availability, Python `vllm` module availability and
origin, GPU availability, readiness `ready`, endpoint `configured`, and models
status `ready`. The aggregate forwards the pass-integrity status and reason in
`llm_goal_evidence_vllm_host_detail`.

The aggregate LLM evidence report now includes `torch_optimizer` in the detail
table and forwards normalized Simple/libtorch CUDA optimizer fields: status,
reason, Python Torch/CUDA host visibility, system libtorch visibility,
system libtorch probe-log hash, libtorch/CUDA availability, parameter CUDA
placement, gradient handle, optimizer-step attempt, before/after sums, and
wrapper exit. The same aggregate
also expands `finetune_guard` detail with retry7 gate exit/status, compact
blocked gates, target eval, license, safety, deployment, and app-handoff fields,
so strict-host review can distinguish retry/eval blockers from deployment or
safety blockers without opening the focused env files first.

The fine-tune guard wrapper now emits its own default-mode blocker contract:
required gates, blocked gates, primary blocked gate, blocker reason, and next
action. Default aggregate mode reads those fields from
`build/llm_finetune_guard_evidence/evidence.env` instead of relying on a
previous acceptance env; strict host mode still reads the freshly-generated
acceptance env.
The guard wrapper also writes a fine-tune guard surface manifest with path,
size, and SHA-256 rows for the fixed-format data file, retry6/retry7 gate
scripts, retry6/retry7 SSpec files, and each produced guard/spec log. The
aggregate fine-tune detail forwards the manifest hash plus per-log size and
SHA-256 fields, so guard-only PASS evidence cannot be accepted as a status-only
claim.

## 2026-06-29 Aggregate Blocker Detail Hardening

`scripts/check/check-llm-goal-evidence.shs` now copies focused blocker contracts
into the aggregate env and report for the vLLM, svLLM, Torch optimizer, and
fine-tune lanes. The aggregate records per-lane required gates, blocked gates,
primary blocked gate, and blocker reasons in `llm_goal_evidence_<lane>_*` keys
and adds a Blocker Details table to the Markdown report, so strict-host
failures can be triaged from one artifact instead of opening every focused
wrapper output first.

Follow-up hardening aligns the strict context/Ponytail and live dashboard
wrappers with the vLLM, Torch, and fine-tune contracts: both now emit
`primary_blocked_gate` fields in their focused env/report outputs, and the
aggregate strict detail rows forward those first-blocker values beside the full
blocked-gates lists.

## 2026-06-29 svLLM Readiness Timeout Hardening

`scripts/check/check-llm-runtime-svllm-local-readiness.shs` now bounds each
local svLLM spec with `SVLLM_READINESS_SPEC_TIMEOUT_SECONDS` and records every
subgate exit code in the env/report. Timeout failures write the top-level
readiness report instead of leaving it missing. The native streaming producer
passes the same timeout through its nested local-readiness run and records
`svllm_native_streaming_local_spec_timeout_seconds` beside the native
read-range, pinned-buffer, and device-staging blockers.
The local readiness wrapper now also writes a local readiness surface manifest
with path, size, and SHA-256 rows for the eight checked specs and their produced
logs, plus per-log size/SHA-256 fields in the focused env/report. The aggregate
svLLM detail forwards the local manifest count, size, and SHA-256 so default
local-readiness PASS evidence is not a status-only claim.

## 2026-06-29 svLLM Manifest Spec Cleanup

`test/01_unit/lib/gc_async_mut/svllm/model_executor/model_loader/manifest_spec.spl`
no longer carries stale `TODO:` scenario names or intentionally failing parser
comments. The spec now asserts the implemented canonical v0 manifest parser and
`build_tensor_pack` materializer behavior directly, and the generated manual
under `doc/06_spec/test/01_unit/lib/gc_async_mut/svllm/model_executor/model_loader/`
records 11 active scenarios with no pending cases.

## 2026-06-29 svLLM Safetensors Parser Cleanup

`test/01_unit/lib/gc_async_mut/svllm/model_executor/model_loader/safetensors_spec.spl`
now uses the repo text-to-bytes helper and an arithmetic little-endian length
fixture writer, matching the parser's runtime constraints. The safetensors
parser's little-endian length reader now uses arithmetic accumulation instead
of boolean-style bitwise syntax, and stale stub comments in the safetensors and
loader modules were replaced with the current implemented boundary.

## 2026-06-29 LLM Aggregate svLLM Timeout Floor

`scripts/check/check-llm-goal-evidence.shs` now gives the `svllm_local` lane a
separate bounded timeout contract. Short global aggregate timeouts still bound
quick lanes, while svLLM local readiness uses
`LLM_GOAL_SVLLM_LANE_TIMEOUT_SECONDS` or a 120s floor so a normal local
readiness pass is not misreported as `lane_timeout_45s`. The aggregate env and
report include each lane's actual timeout seconds for review.

## 2026-06-29 svLLM Memory Transport Restore

`load_model_from_pack_streamed(...)` is restored as the bridge from already-read
manifest text and chunk bytes into the pure streamer. The memory NVFS transport
now compiles against that entry again, and `stream_pack` can gather a tensor
span across sequential chunks instead of rejecting split tensors. The new
`model_loader_transport_spec` covers success, missing transport chunks, short
chunk data, and split-tensor streaming; local svLLM readiness now includes that
transport spec as an evidence subgate.

## 2026-06-29 Torch Optimizer Probe Lowering Cleanup

The GC and NoGC Torch training optimizers now declare mutating `step` methods
with mutable receivers, and the device-placement status spec locks that source
contract for SGD, Adam, and RMSprop. The CUDA optimizer probe now returns CLI
status codes from `main() -> i64` instead of calling an unbound `exit`, so this
host reaches the intended `libtorch_unavailable` evidence boundary without the
previous RMSprop mutability or probe-exit lowering errors.

## 2026-06-29 Dashboard Agent Route Evidence Inclusion

The dashboard evidence wrappers now include the `/agents` route system spec in
the same dashboard lane as diagnostics and vLLM control. The live dashboard
wrapper requires authenticated `/agents` rendering, unauthenticated redirect,
non-prefix hijack protection, and server/guide route contracts before reporting
dashboard evidence as pass.

## 2026-06-29 vLLM Host Resource Blocker Precision

`scripts/check/check-llm-runtime-vllm-host-probe.shs` now probes `vllm` and
`nvidia-smi` explicitly and records `local_vllm_status`, `vllm_command_path`,
`python_vllm_module_status`, and `local_gpu_status` in the evidence env/report.
The blocked-gates list no longer
depends only on the collapsed control-CLI reason, so a host missing both local
vLLM and GPU tooling reports both `local_vllm` and `local_gpu` blockers before
serve preflight, endpoint, and model-listing gates.

## 2026-06-29 Aggregate LLM Evidence Detail Surfacing

`scripts/check/check-llm-goal-evidence.shs` now forwards vLLM host resource
details into `llm_goal_evidence_vllm_host_detail` and fine-tune retry7
acceptance details into `llm_goal_evidence_finetune_guard_detail`. This keeps
the default aggregate report honest: guard-only fine-tune evidence can pass
locally, while the acceptance detail still names the retry6/model/eval/license/
safety/deployment blocker and artifact refs that must pass before strict host
completion.
Default mode runs the retry7 acceptance producer as non-blocking detail
evidence first; strict mode consumes the same env as a required pass gate.

The same aggregate now forwards `llm_goal_evidence_context_ponytail_detail` and
`llm_goal_evidence_dashboard_detail`, so strict/full-replacement context mode,
Ponytail, and authenticated dashboard evidence cannot be hidden behind a single
lane status when host completion evidence is reviewed. Default dashboard detail
now carries the strict-host next action instead of `not_collected`, so the
default report still tells operators how to produce live authenticated evidence.

Default aggregate mode now also generates and consumes the repo-local
context/Ponytail full-replacement env before running the context/Ponytail lane.
This keeps the default report aligned with the completed Simple-owned
`simple_context`/`simple_ponytail` replacement surfaces, while live dashboard,
vLLM, native svLLM, fine-tune acceptance, and Torch optimizer gates remain
strict-host completion evidence.

Strict aggregate mode also clears each strict producer env before running the
producer. A timeout or early producer failure therefore leaves missing evidence
instead of reusing a stale full-replacement, live-dashboard, native-svLLM, or
fine-tune acceptance env from a prior run.

The aggregate now records `llm_goal_evidence_<lane>_producer_exit` and
`llm_goal_evidence_<lane>_producer_log`, and shows both values in the lane
table. Strict producer failures and timeouts can be distinguished from
downstream strict lane failures without hunting for the producer log path first.

The aggregate now also forwards `llm_goal_evidence_svllm_local_detail`.
Strict-native svLLM failures show the native streaming status, blocker reason,
native blocked gates, primary blocked gate, next action, local readiness,
native `read_range`, pinned-buffer, device-staging, and local file-backed
byte-read states, capability evidence artifact status, source, and
pass-integrity state in the aggregate report instead of collapsing the detail
row to `n/a`.
Strict local readiness also rejects native envs that report
`svllm_native_streaming_status=pass` without
`svllm_native_streaming_pass_integrity_status=pass`.

The svLLM aggregate blocker table is now mode-aware. Default local-readiness
mode reports `required_gates=local_readiness`, `blocked_gates=none`, and
`reason=default_local_readiness_only`; strict host mode consumes
`svllm_native_streaming_blocked_gates` directly so producer and aggregate
blocker ordering stay identical.

The focused vLLM host probe and Torch optimizer probe now write `next_action`
fields, and the aggregate forwards them through the vLLM/Torch detail rows.
The remaining WARN lanes therefore name both the blocked gate and the concrete
operator action needed before strict host completion can pass.

The aggregate now promotes next actions to first-class
`llm_goal_evidence_<lane>_next_action` env fields and a `Next Actions` report
table for vLLM, svLLM, Torch optimizer, and fine-tune. This makes the strict
host handoff actionable without parsing the longer detail strings.

The aggregate `Next Actions` table now covers every lane: context/Ponytail
replacement, live dashboard, vLLM, svLLM, Torch optimizer, fine-tune, and public
absence rendering.
Default mode explicitly points context/Ponytail and dashboard at `--strict-host`
when completion evidence is required; strict mode points failed replacement and
live-dashboard lanes at their focused wrappers.

## 2026-06-29 Public Absence Evidence Manifest

`scripts/check/check-llm-tooling-public-absence-rendering.shs` now writes
canonical evidence under `build/llm_tooling_public_absence_rendering/`. The
evidence env records status, required gates, blocked gates, failure count, next
action, and a hashed `public_absence_surface_manifest.tsv` for the public
manuals, generated/manual SPipe docs, dashboard wording, and runtime evidence
surfaces scanned for forbidden absence markers. The aggregate forwards those
fields into `llm_goal_evidence_public_absence_detail`, so public absence
completion is auditable from the aggregate report without relying on prior
terminal output.

The aggregate lane runner now unsets the aggregate `BUILD_DIR` before invoking
focused wrappers. Each wrapper writes its canonical `build/<lane>/evidence.env`,
and aggregate detail rows read fresh focused evidence instead of stale default
env files from earlier standalone runs.

## 2026-06-29 Strict Context/Dashboard Blocker Metadata

`check-llm-tooling-context-ponytail-full-replacement.shs` and
`check-llm-dashboard-live-evidence.shs` now emit wrapper-local
`required_gates`, `blocked_gates`, and `next_action` fields. The aggregate
consumes those fields in strict mode, so replacement-surface failures and live
dashboard route/auth failures are visible in the same blocker table and detail
rows as vLLM, svLLM, Torch optimizer, and fine-tune blockers.

Normal-review and Spark sidecars both flagged that route/source checks were not
live authenticated dashboard proof. The dashboard live wrapper now requires a
separate `LLM_DASHBOARD_LIVE_HTTP_EVIDENCE_ENV` with
`llm_dashboard_live_http_status=pass` and
`llm_dashboard_live_http_pass_integrity_status=pass`; without it, strict
dashboard completion fails with `live_http_authenticated_request` or
`live_http_pass_integrity` blocked instead of treating route contracts as a
live operator-dashboard pass. The HTTP producer records exact status codes,
response sizes, SHA-256 fingerprints, and the non-secret authentication source
type for the unauthenticated API rejection, dashboard HTML, agents HTML, and
authenticated control JSONL responses, so a status-only env or implicit dummy
cookie cannot satisfy strict dashboard evidence.
The live dashboard wrapper also writes a route surface manifest with path,
size, and SHA-256 rows for the checked route specs, server source, dashboard
guide, and runtime task plan, plus size/SHA-256 metadata for the nested
dashboard evidence env/log. The aggregate dashboard detail forwards those
fields, so strict live dashboard review can distinguish hashed local
route-contract proof from the still-required live HTTP proof.
The aggregate strict-host path now runs
`check-llm-dashboard-live-http-evidence.shs` before
`check-llm-dashboard-live-evidence.shs`, so a missing configured dashboard URL
is preserved as the concrete `base_url` live-HTTP blocker in dashboard detail
instead of collapsing to a missing live-HTTP env.

The context/Ponytail replacement wrapper now also runs
`test/02_integration/app/mcp_context_ponytail_dispatch_spec.spl` as
`execution_spec`. That spec calls `simple_context` and `simple_ponytail` through
`app.mcp.main_dispatch.dispatch_tool_content`, so full-replacement evidence is
no longer source-contract-only for the app MCP path.
The wrapper also writes a replacement-surface manifest with path, size, and
SHA-256 rows for the checked guide, architecture, requirements, app MCP, lower
MCP, and dispatch spec files, plus size/SHA-256 metadata for the mimic env/log
and execution-spec log. The aggregate detail row forwards those values, so a
passing context/Ponytail replacement cannot be accepted as a status-only claim.

## 2026-06-29 Strict Completion Audit

`doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md` records
the current completion state. Default aggregate evidence passes with
`warn_gates=vllm_host|torch_optimizer`; strict-host aggregate evidence fails
five lanes: live dashboard HTTP auth/base URL, local vLLM serving, native svLLM
streaming, Simple-visible libtorch optimizer execution, and fine-tune retry6/7
acceptance. Context/Ponytail full replacement is passing and is no longer a
strict blocker.
The open blocker tracker is
`doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`.

Follow-up hardening adds
`scripts/check/check-llm-strict-blocker-tracker.shs`, a cheap committed-doc
drift guard for the strict audit and blocker tracker. It validates that the
latest default aggregate report still reports
`warn_gates=vllm_host|torch_optimizer`, the tracker/audit still name the five
strict blockers, and the vLLM/Torch manifest counts and hashes recorded in the
blocker docs match the current default aggregate evidence. If the aggregate
report is absent while being regenerated, the guard falls back to the aggregate
env; if the report exists but is stale, the guard fails. This does not collect
live host evidence; it prevents stale tracker or audit text from being mistaken
for strict completion.

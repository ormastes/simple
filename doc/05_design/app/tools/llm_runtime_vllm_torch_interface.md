# Detail Design: LLM Runtime vLLM/Torch Interface

Date: 2026-06-25

## Data Shape

`LlmRuntimeManifest`:

- `base_model`: text
- `endpoint`: text
- `chat_template`: option-like text field
- `lora_adapters`: list of `{name, path}`
- `dynamic_lora`: `disabled`, `trusted`, or `blocked`
- `invalid_adapter_count`: count of malformed adapter tokens found while
  parsing manifest text

`LlmRuntimeProbeResult`:

- `status`: `ready`, `missing`, `blocked`, or `error`
- `reason`: text
- `base_model`: public model label or `redacted`
- `endpoint_status`: `configured` or `missing`
- `chat_template_status`: `none`, `present`, or `missing`
- `lora_adapter_count`: integer count without adapter paths
- `dynamic_lora_status`: `disabled`, `trusted`, or `blocked`
- `torch_ready`: `ready`, `unavailable`, `blocked`, or `unchecked` depending
  on the owner Torch/SFFI readiness facade or deterministic test injection
- `evidence_jsonl`: one SPipe/dashboard diagnostics event

`LlmRuntimeServePlan`:

- `status`: `planned`, `missing`, or `blocked`
- `reason`: text such as `static_serve_plan_only`, `invalid_endpoint`, or
  `dynamic_lora_requires_trusted_mode`
- `binary`: `vllm`
- `base_model`: public model label or `redacted`
- `endpoint_status`: `configured`, `missing`, or `invalid`
- `command_preview`: sanitized metadata string, never an executable command
  with private paths or credentials
- `lora_adapter_count`: integer count without adapter paths
- `dynamic_lora_status`: `disabled`, `trusted`, or `blocked`
- `evidence_jsonl`: one SPipe/dashboard diagnostics event

## Algorithms

1. Parse manifest from a small key/value file or construct it directly.
2. Validate required fields.
3. Validate optional chat template and adapter paths without exposing internal
   absence markers.
4. Surface malformed adapter tokens as `invalid_adapter_entry`.
5. Emit one SPipe JSONL event with normalized status and reason.
6. Generate a sanitized static serve-plan event when requested; do not start
   vLLM or probe HTTP in this slice.
7. Let the existing dashboard diagnostics collector summarize that event.
8. Parse already-fetched `/v1/models` response bodies before transport; report
   ready, auth rejection, malformed, wrong-model, invalid-endpoint, and
   redaction outcomes without exposing private model identifiers.
9. Keep live request planning separate from transport. Build sanitized
   `/v1/models` and `/v1/chat/completions` plans first, reject invalid
   endpoints, and block unsupported chat parameters at the planner boundary.
10. Build sanitized request-plan metadata for `/v1/models` and
    `/v1/chat/completions` before HTTP transport. Transport uses the existing
    owner HTTP facade only after planning succeeds.
11. Parse already-fetched `/v1/chat/completions` response bodies and redact
    generated assistant content from public evidence.
12. Gate `vllm serve` lifecycle through sanitized serve plans and owner process
    facades. Treat spawn success as process evidence only; endpoint readiness
    still requires observed transport/probe evidence.
13. Route dashboard control requests through the runtime owner boundary.
    Preflight remains intent-only; side-effecting actions return skipped,
    blocked, executor-required, or owner execution JSONL without letting
    dashboard rendering import process or HTTP backends.

## Error Handling

- Missing optional values become `none` or omitted fields.
- Missing required values become `status=missing` with a specific reason.
- Dynamic LoRA requested without trusted mode becomes `status=blocked`.
- Endpoint failures become `status=error` and include only sanitized host/path
  context.
- Invalid endpoint strings in the static serve-plan path become
  `status=missing` with `reason=invalid_endpoint`.
- Malformed adapter entries become `reason=invalid_adapter_entry` instead of
  being silently dropped.
- Known Torch/SFFI or svLLM loader placeholder behavior becomes
  `status=blocked`; it must not be normalized into `ready`.
- Missing local vLLM or GPU resources become `skipped` or `blocked` evidence
  before spawn/fetch paths are attempted.
- Non-positive internal process sentinels render as public pid `0` in JSONL,
  text, and HTML.

## Test Design

- Manifest with base model and no LoRA is blocked by default while Torch/svLLM
  placeholder readiness remains unresolved.
- Absent chat template is reported as `none`; a configured but missing chat
  template path is reported as `missing`.
- Static LoRA adapter path is recorded.
- Static LoRA adapter paths are validated locally but omitted from public
  evidence.
- Dynamic LoRA is blocked unless trusted mode is explicit.
- JSONL evidence renders absence with explicit text states.
- Dashboard renders the evidence without exposing internal absence markers.
- Public manuals and evidence are covered by
  `scripts/check/check-llm-tooling-public-absence-rendering.shs`, which ignores
  folded executable source blocks but fails prose/evidence that exposes the
  internal absence marker.
- Dashboard output for this runtime slice redacts credentials, API-key-like
  labels, and local model/adapter paths by default. Prompt and tool-payload
  redaction belongs to callers that create prompt/tool evidence.
- Static serve-plan metadata redacts base model IDs with path separators,
  endpoint credentials,
  and LoRA adapter paths.
- Malformed adapter tokens and invalid endpoints are reported explicitly.
- Live vLLM tests cover request planning and already-fetched `/v1/models` and
  `/v1/chat/completions` response parsing, including base/adapter model
  selection, auth rejection, malformed responses, wrong model, unsupported
  parameters, and generated-content redaction.
- The first live `/v1/models` slice covers already-fetched response parsing:
  ready model lists, auth rejection, malformed bodies, wrong-model responses,
  invalid endpoints, and path/sensitive model redaction without exposing the
  internal absence marker.
- Serve lifecycle and readiness tests prove no-spawn planning failures,
  process-state adaptation, timeout cleanup policy, skipped local-resource
  preflight, and observed-readiness summaries without requiring a host vLLM
  server.
- Dashboard route specs prove authenticated preflight and deterministic
  side-effect action JSONL for missing-resource or invalid-pid cases without
  spawning a process.

## Ponytail Cut

The first implementation stopped at manifest/probe/evidence, then advanced
through bounded planning, transport, lifecycle, readiness, and dashboard-control
evidence without requiring a live vLLM/GPU host. Keep that cut: no trainer, no
new scheduler, no dynamic adapter plugin, and no claim of live serving until
real endpoint evidence exists.

If implementation starts from the runtime blocker lane instead, the cut is:
clear the reported Torch availability/seed/device placeholders and svLLM loader
stubs with focused tests, then return to the readiness bridge.

## Implemented Option A Evidence

- `src/app/llm_runtime/manifest.spl`
- `src/app/llm_runtime/probe.spl`
- `src/app/llm_runtime/serve_plan.spl`
- `test/01_unit/app/llm_runtime/vllm_readiness_spec.spl`
- `test/unit/app/llm_runtime/vllm_readiness_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_readiness_spec.md`
- `doc/06_spec/unit/app/llm_runtime/vllm_readiness_spec.md`
- `test/03_system/app/llm_runtime/feature/vllm_torch_readiness_spec.spl`
- `doc/06_spec/03_system/app/llm_runtime/feature/vllm_torch_readiness_spec.md`

The implemented bridge validates required local manifest fields, reports
optional absence with explicit text states, surfaces malformed adapter tokens,
blocks untrusted dynamic LoRA, omits adapter paths and sensitive-looking model
labels from JSONL evidence, and keeps Torch/svLLM placeholder readiness as
`blocked` by default while those owner modules are known placeholders. The
static serve-plan path emits sanitized vLLM command metadata and rejects invalid
endpoints without starting vLLM or probing live HTTP endpoints.

## Implemented Live Models Response Slice

- `src/app/llm_runtime/live_models_probe.spl`
- `test/01_unit/app/llm_runtime/vllm_live_models_probe_spec.spl`
- `test/unit/app/llm_runtime/vllm_live_models_probe_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_live_models_probe_spec.md`

The live models response parser consumes an already-fetched HTTP status and
`/v1/models` response body. It reports `ready` only when a successful models
response includes the configured base model, redacts sensitive or path-like
model identifiers in public evidence, distinguishes auth rejection from
malformed responses, and rejects invalid endpoints before trusting response
bodies. It does not start vLLM, fetch HTTP, call chat completions, or prove GPU
serving readiness.

## Implemented Live Request Plan Slice

- `src/app/llm_runtime/live_request_plan.spl`
- `test/01_unit/app/llm_runtime/vllm_live_request_plan_spec.spl`
- `test/unit/app/llm_runtime/vllm_live_request_plan_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_live_request_plan_spec.md`

The live request planner produces sanitized, plan-only metadata for the
`/v1/models` GET and `/v1/chat/completions` POST surfaces. It removes endpoint
credentials from public URL previews, rejects invalid endpoints, reports missing
chat bodies without exposing request content, and blocks unsupported chat
parameters before transport. It does not fetch HTTP or supervise vLLM.

## Implemented Live Chat Response Slice

- `src/app/llm_runtime/live_chat_probe.spl`
- `test/01_unit/app/llm_runtime/vllm_live_chat_probe_spec.spl`
- `test/unit/app/llm_runtime/vllm_live_chat_probe_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_live_chat_probe_spec.md`

The live chat response parser consumes an already-fetched HTTP status and
`/v1/chat/completions` response body. It reports `ready` only when a successful
chat response includes at least one choice with assistant content, redacts
generated content from public evidence, distinguishes auth rejection from
malformed responses, and rejects invalid endpoints before trusting response
bodies. It does not fetch HTTP, evaluate answer quality, supervise vLLM, or
prove GPU serving readiness.

## Implemented Live HTTP Transport Slice

- `src/app/llm_runtime/live_transport.spl`
- `test/01_unit/app/llm_runtime/vllm_live_transport_spec.spl`
- `test/unit/app/llm_runtime/vllm_live_transport_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_live_transport_spec.md`

The live transport wrapper reuses the existing app-owned
`std.nogc_sync_mut.io.http_sffi.http_request` facade for GET/POST calls. It
gates transport through the live request planner, summarizes HTTP status and
parser status, and keeps response bodies, prompts, and generated assistant
content out of public JSONL evidence. It does not start or supervise `vllm
serve`, discover a local endpoint, or prove GPU-backed serving.

Runtime-adjacent decision record:

- `runtime_need`: perform local vLLM-compatible HTTP GET/POST once request
  planning succeeds.
- `facade_checked`: `app.io.http_sffi`, `std.nogc_sync_mut.io.http_sffi`,
  `std.nogc_async_mut.io.http_sffi`, and pure HTTP request/response modules.
- `chosen_path`: `reuse-facade` via `std.nogc_sync_mut.io.http_sffi.http_request`.
- `rejected_shortcuts`: raw `rt_http_request` imports in `app.llm_runtime`,
  shelling out to curl, and process-based fetch wrappers.

## Implemented Serve Lifecycle Slice

- `src/app/llm_runtime/serve_lifecycle.spl`
- `test/01_unit/app/llm_runtime/vllm_serve_lifecycle_spec.spl`
- `test/unit/app/llm_runtime/vllm_serve_lifecycle_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_serve_lifecycle_spec.md`

The lifecycle wrapper gates `vllm serve` startup through the static serve plan,
then uses `app.io.mod.process_spawn_async`, `process_is_running`, and
`process_kill` for process lifecycle actions. Public evidence reports process
state and sanitized command previews only. Endpoint readiness remains the
responsibility of the live request/transport/probe path.

Runtime-adjacent decision record:

- `runtime_need`: start, poll, and stop a local `vllm serve` process.
- `facade_checked`: `app.io.mod` process exports, `app.io.process_ops`, and
  raw runtime process extern locations.
- `chosen_path`: `reuse-facade` via `app.io.mod.process_spawn_async`,
  `process_is_running`, and `process_kill`.
- `rejected_shortcuts`: raw `rt_process_*` imports in `app.llm_runtime`, shell
  wrappers, and curl/process-based HTTP transport.

## Implemented Serve Readiness Orchestration Slice

- `src/app/llm_runtime/serve_readiness.spl`
- `test/01_unit/app/llm_runtime/vllm_serve_readiness_spec.spl`
- `test/unit/app/llm_runtime/vllm_serve_readiness_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_serve_readiness_spec.md`

The readiness orchestration layer composes the static serve plan, request plan,
process lifecycle result, and `/v1/models` transport result into one
dashboard-consumable state. It has a pure preflight path that does not spawn or
fetch, and an observed-evidence path that refuses to report `ready` until the
process has been polled as `running` and the models endpoint reports `ready`.
It also defines a default policy, live orchestrator, and synthetic sequence
runner. The sequence runner covers retry/cleanup decisions without real process
or HTTP side effects; the live orchestrator is ready for a later integration
slice that has an installed vLLM environment.

Runtime-adjacent decision record:

- `runtime_need`: combine lifecycle and endpoint evidence without creating a
  hidden process or HTTP side effect in unit tests.
- `facade_checked`: `serve_lifecycle`, `live_request_plan`, and
  `live_transport`.
- `chosen_path`: `reuse-facade` through pure result-object composition.
- `rejected_shortcuts`: raw process polling in the readiness summary,
  curl/shell endpoint checks, and using PID spawn success as HTTP readiness.

## Implemented Live Environment Evidence Slice

- `src/app/llm_runtime/live_environment.spl`
- `test/01_unit/app/llm_runtime/vllm_live_environment_spec.spl`
- `test/unit/app/llm_runtime/vllm_live_environment_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_live_environment_spec.md`

The live-environment evidence classifier records whether a host has observed
local vLLM and GPU availability. Missing capabilities produce explicit
`skipped` reasons (`missing_local_vllm`, `missing_local_gpu`, or
`missing_local_vllm_and_gpu`) so SPipe and dashboard evidence can distinguish an
unrun live serving check from a failed model endpoint. Serve-readiness now has
resource-aware preflight/orchestration wrappers that short-circuit with
`skipped` before process spawn or HTTP fetch when those resources are absent.

Runtime-adjacent decision record:

- `runtime_need`: represent local vLLM/GPU availability evidence for live
  serving gates.
- `facade_checked`: existing live readiness and lifecycle result APIs.
- `chosen_path`: pure evidence classifier fed by a future owner probe or
  integration harness.
- `rejected_shortcuts`: shelling out to `which vllm`, reading CUDA environment
  directly in `app.llm_runtime`, or treating missing host capability as a model
  failure.

## Implemented Dashboard Control-Intent Slice

- `src/app/llm_dashboard/collectors/vllm_control_panel.spl`
- `src/app/web_dashboard/server.spl`
- `test/01_unit/app/llm_dashboard/collectors/vllm_control_panel_spec.spl`
- `test/unit/app/llm_dashboard/collectors/vllm_control_panel_spec.spl`
- `doc/06_spec/01_unit/app/llm_dashboard/collectors/vllm_control_panel_spec.md`
- `doc/06_spec/unit/app/llm_dashboard/collectors/vllm_control_panel_spec.md`

The dashboard now renders a vLLM control panel with `preflight`, `start`,
`poll`, `probe`, and `stop` intents and exposes `/api/vllm/control` for
authenticated JSONL action evidence. This panel delegates manifest, action, and
pid decisioning to `app.llm_runtime.dashboard_live_control` and keeps missing
state rendered as `none`.

This is intentionally not the live execution owner. The dashboard module uses
the runtime-owned pure control decision boundary and does not import live
HTTP/process backends during ordinary page rendering. Actual process spawn,
polling, stop, and endpoint fetch remain in
`src/app/llm_runtime/dashboard_live_control_executor.spl`,
`src/app/llm_runtime/serve_lifecycle.spl`,
`src/app/llm_runtime/live_transport.spl`, and
`src/app/llm_runtime/serve_readiness.spl`.

Runtime-adjacent decision record:

- `runtime_need`: expose operator controls without forcing dashboard import of
  process or HTTP runtime backends.
- `facade_checked`: `dashboard_live_control`, `serve_plan`,
  `live_request_plan`, and existing `serve_lifecycle`/`serve_readiness`
  execution facades.
- `chosen_path`: `reuse-facade` for pure runtime control decisions in the
  dashboard; defer live execution to the runtime owner boundary.
- `rejected_shortcuts`: raw `rt_process_*`/HTTP imports in the dashboard,
  shelling out from dashboard routes, and treating rendered buttons as proof of
  live vLLM availability.

## Implemented Runtime Dashboard Live-Control Slice

- `src/app/llm_runtime/dashboard_live_control.spl`
- `src/app/llm_runtime/dashboard_live_control_executor.spl`
- `test/01_unit/app/llm_runtime/vllm_dashboard_live_control_spec.spl`
- `test/unit/app/llm_runtime/vllm_dashboard_live_control_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_dashboard_live_control_spec.md`
- `doc/06_spec/unit/app/llm_runtime/vllm_dashboard_live_control_spec.md`

The runtime now owns dashboard-requested vLLM control execution. The pure
control module validates `preflight`, `start`, `poll`, `probe`, and `stop`
actions, applies explicit local vLLM/GPU resource gates, and emits public JSONL
without model ids, response bodies, or internal absence markers. It returns
`live_executor_required` for valid side-effecting actions so dashboard and tests
can prove intent without importing process or HTTP backends.

The live executor module remains under `app.llm_runtime` and composes the
existing `serve_lifecycle`, `serve_readiness`, and `live_transport` facades for
actual process spawn, pid polling, `/v1/models` probing, and stop requests. It
is intentionally not imported by dashboard rendering yet; route-level live
wiring still needs integration evidence against an installed local `vllm`.

Runtime-adjacent decision record:

- `runtime_need`: honor operator dashboard controls through the runtime owner
  boundary.
- `facade_checked`: `live_environment`, `serve_plan`, `live_request_plan`,
  `serve_lifecycle`, `serve_readiness`, and `live_transport`.
- `chosen_path`: keep unit-testable control decisions pure; place live
  process/HTTP composition in a separate runtime executor module.
- `rejected_shortcuts`: dashboard-owned process/HTTP imports, shell/curl
  execution, and treating a valid pid as endpoint readiness.

## Implemented Runtime Control Response Slice

- `src/app/llm_runtime/control_cli.spl`
- `test/01_unit/app/llm_runtime/vllm_control_cli_spec.spl`
- `test/unit/app/llm_runtime/vllm_control_cli_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_control_cli_spec.md`
- `doc/06_spec/unit/app/llm_runtime/vllm_control_cli_spec.md`

The runtime exposes `control_cli.spl`, which accepts explicit action,
base-model, endpoint, pid, and local resource flags and emits public JSONL. The
in-process helper `llm_runtime_control_cli_response(argv)` is covered for
operator/agent callers, and direct app execution through
`simple run src/app/llm_runtime/control_cli.spl -- ...` emits JSONL. The source
CLI dispatcher also registers `llm-runtime-control`; the prebuilt release
binary will expose `simple llm-runtime-control` after rebuild.

Native standalone rebuild evidence is present for the command itself:
`native-build --source src/app --source src/lib --entry-closure --entry
src/app/llm_runtime/control_cli.spl --output
build/llm_runtime/llm_runtime_control_cli` links a 57 KB binary. That rebuilt
binary emits JSONL for planned preflight, skipped start, and usage/error cases.
Public pid absence is rendered as `0`, avoiding native negative-sentinel
formatting issues in public JSONL.

This slice also removed post-construction evidence mutation from
`serve_plan`, `live_request_plan`, `live_environment`, and
`dashboard_live_control` on the pure control path, and renamed request/serve
private plan helpers to avoid co-compiled private symbol collisions.

Runtime-adjacent decision record:

- `runtime_need`: provide operator/agent JSONL control evidence without routing
  through the web dashboard.
- `facade_checked`: runtime pure control decision API and existing serve/request
  planning evidence APIs.
- `chosen_path`: expose direct app execution plus source CLI dispatch through
  the runtime owner; prove the standalone command with native-build evidence and
  leave full release-binary proof for the next release rebuild.
- `rejected_shortcuts`: shelling out to dashboard routes, importing dashboard
  process/HTTP paths, or adding raw process/runtime shortcuts.

## Implemented Runtime Control CLI Registration Evidence Slice

- `test/01_unit/app/cli/llm_runtime_control_command_spec.spl`
- `test/unit/app/cli/llm_runtime_control_command_spec.spl`
- `doc/06_spec/01_unit/app/cli/llm_runtime_control_command_spec.md`
- `doc/06_spec/unit/app/cli/llm_runtime_control_command_spec.md`

Mirrored SPipe coverage now proves the top-level command is registered in the
canonical CLI command table, routed by the direct dispatcher branch, and shown
in operator help:

- `src/app/cli/dispatch/table.spl` maps `llm-runtime-control` to
  `src/app/llm_runtime/control_cli.spl`.
- `src/app/cli/main_part2.spl` routes the direct branch through
  `cli_run_file("src/app/llm_runtime/control_cli.spl", filtered_args, ...)`.
- `src/app/cli/cli_helpers.spl` documents
  `simple llm-runtime-control --action preflight --base-model <model>
  --endpoint <url>`.

Full native CLI rebuild evidence is still not complete. A focused attempt to
build the full CLI with `native-build --source src/app --source src/lib
--entry-closure --entry src/app/cli/main.spl --strip --threads 1 --timeout 240
--output build/llm_runtime/simple_cli_full` reached compiler/backend module
progress but hit the 300s external cap with exit `124` and emitted no binary.
This is tracked with the full-program native build bug rather than treated as
vLLM command logic.

## Implemented Runtime Control Resource Detection Slice

- `src/app/llm_runtime/control_cli.spl`
- `test/01_unit/app/llm_runtime/vllm_control_cli_spec.spl`
- `test/unit/app/llm_runtime/vllm_control_cli_spec.spl`
- `doc/06_spec/01_unit/app/llm_runtime/vllm_control_cli_spec.md`
- `doc/06_spec/unit/app/llm_runtime/vllm_control_cli_spec.md`

The runtime control CLI now accepts `--detect-resources` for local host
capability classification. When explicit `--vllm-available` or
`--gpu-available` flags are absent, detection runs bounded probes through the
`app.io.mod.process_run_timeout` facade: `vllm --version` for the local vLLM
entrypoint and `nvidia-smi --query-gpu=name --format=csv,noheader` for GPU
visibility. The resulting booleans feed the existing preflight/start/probe
resource gates before any serve spawn or HTTP readiness plan can proceed.

Explicit flags still override detection so tests and CI harnesses remain
deterministic. Detection is deliberately a host capability classifier, not live
endpoint proof; `/v1/models` readiness remains owned by the runtime HTTP
transport/readiness path.

Runtime-adjacent decision record:

- `runtime_need`: classify local vLLM/GPU availability for runtime control
  preflight without forcing operators to pass manual resource flags.
- `facade_checked`: `app.io.mod.process_run_timeout`.
- `chosen_path`: `reuse-facade` with bounded process probes inside
  `app.llm_runtime.control_cli`.
- `rejected_shortcuts`: raw `rt_process_run` imports, shell pipelines, dashboard
  owned detection, and treating command availability as endpoint readiness.

## Implemented Dashboard Query Control Slice

- `src/app/llm_dashboard/collectors/vllm_control_panel.spl`
- `src/app/web_dashboard/server.spl`
- `test/01_unit/app/llm_dashboard/collectors/vllm_control_panel_spec.spl`
- `test/unit/app/llm_dashboard/collectors/vllm_control_panel_spec.spl`
- `doc/06_spec/01_unit/app/llm_dashboard/collectors/vllm_control_panel_spec.md`
- `doc/06_spec/unit/app/llm_dashboard/collectors/vllm_control_panel_spec.md`

The web dashboard `/api/vllm/control` route now accepts query-style control
inputs for `action`, `pid`, `base_model`/`base-model`, `endpoint`,
`vllm_available`/`vllm-available`, and `gpu_available`/`gpu-available`. The
route applies model and endpoint overrides to the configured manifest text, then
delegates to the dashboard-safe vLLM collector facade. Resource flags feed the
runtime-owned planner before side-effecting actions can be reported as planned;
missing local resources return explicit `skipped` evidence. This remains
planner/intent evidence only. The web dashboard still does not import live
process or HTTP execution modules.

## Implemented Torch Readiness Slice

- `src/lib/common/torch/dyn_sffi_ops.spl`
- `test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl`
- `test/unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl`
- `doc/06_spec/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.md`

The dynamic Torch SFFI availability helper now delegates to
`rt_torch_available()` instead of hardcoding `false`. This removes one
owner-module placeholder without claiming full Torch readiness. The dynamic
Torch linalg-solve helper now checks runtime availability and delegates to the
documented `rt_torch_torchtensor_linalg_solve(a, b)` SFFI instead of returning an
unconditional failure handle. It also exposes
`dyn_torch_tensor_linalg_solve_result(a, b)` for callers that need explicit
`libtorch_unavailable`, `invalid_handle`, or `runtime_returned_null_handle`
status instead of interpreting handle `0` as every failure class. The C++
runtime linalg-solve bridge prechecks tensor handles and returns `0` for
invalid native handles so the Simple status wrapper is not bypassed by a
runtime panic. Torch training seed helpers now return explicit
`unsupported` status instead of silently no-oping while no owner manual-seed
SFFI exists. Explicit Torch CUDA device ids now pass through GC/NoGC backend
placement, `Tensor.cuda`, and stream creation instead of being forced to device
`0`; optimizer state initialization no longer silently moves state tensors to
CUDA `0` while device-aware optimizer-state SFFI remains unselected. svLLM
canonical v0 manifests now parse, non-empty tensor/chunk
metadata materializes into `TensorPack`, declared chunk digests are shape
validated, already-read manifests load without throwing, and filesystem-backed
pack roots load `manifest.sdn` and verify chunk existence, byte length, and
SHA-256 through the existing owner file facade. The loader can now return the
declared byte range for a named tensor from a validated pack, including spans
that start in one chunk and continue through following chunks, with explicit
`tensor_not_found`, `tensor_range_invalid`, and chunk errors. The loader now
also exposes a plan-only tensor stream plan that decomposes single-chunk and
cross-chunk tensor spans into ordered chunk read segments and carries
pin/device-staging intent as explicit flags while reporting
`plan_only_not_scheduled`. The `std_fs` NVFS adapter keeps trait
`read_range`, `register_buffer`, and `unregister_buffer` unsupported because no
caller-buffer write primitive or pinned DMA contract exists yet. It now also
offers a local `read_range_bytes` helper through the owner file facade so
bounded file-backed byte reads can be tested without claiming async NVFS
scheduling or GPU staging. Streaming readiness JSONL now carries a separate
`local_read_bytes` field so clean pack roots can prove local bytes are readable
without turning native streaming readiness green. The native capability probe
now executes the StdFs NVFS client spec and records
`svllm_native_capability_local_read_range_bytes_status` plus a reason field so
strict evidence can show local file-backed read-range progress while keeping
native `read_range`, pinned-buffer registration, and device staging
unsupported. Remaining blockers include full async NVFS scheduling,
pinned/device staging, live CUDA placement evidence, and device-preserving
optimizer state for already-CUDA parameters.

# LLM Runtime vLLM/Torch Guide

Operator guide for the LLM runtime vLLM, Torch, svLLM, and dashboard-control
evidence surfaces.

## Purpose

This guide covers the current runtime evidence boundary. It is not a claim that
local vLLM serving, CUDA Torch execution, or svLLM NVFS streaming are live on a
host. Those gates require host-specific proof and remain separate from
intent/readiness JSONL.

Use this guide with:

- `doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md`
- `doc/04_architecture/app/tools/llm_runtime_vllm_torch_interface.md`
- `doc/05_design/app/tools/llm_runtime_vllm_torch_interface.md`
- `doc/07_guide/app/dashboard.md`

## Evidence Boundary

Public runtime evidence must report absence with explicit text states such as
`none`, `missing`, `blocked`, `skipped`, `unavailable`, or `redacted`.
Operator-facing JSONL, manuals, and dashboard panels must not expose internal
absence markers.

Current implemented evidence includes:

- static vLLM manifest/readiness checks
- live request planning and sanitized `/v1/models` or chat response parsing
- owner-facade HTTP transport planning and evidence classification
- process-facade serve lifecycle planning, polling, and stop boundaries
- dashboard-safe `/api/vllm/control` readback
- runtime-owner dashboard control JSONL for side-effect action requests
- Torch owner readiness classification as `ready`, `unavailable`, or
  `unsupported`
- svLLM local file-backed read-range readiness classification

## Dashboard Controls

The authenticated web dashboard exposes `/api/vllm/control` for vLLM control
evidence. The route may render preflight, start, poll, probe, and stop intent
or runtime-owner JSONL, but dashboard rendering is not the owner of process or
HTTP side effects.

Expected public labels:

- `not_live_evidence`: dashboard output is planning/readback only
- `live_executor_required`: a valid side-effecting action needs the runtime
  owner executor path
- `skipped` or `blocked`: a local resource, endpoint, process id, or GPU
  prerequisite is missing

Live process start, endpoint probing, and stop proof are only complete when an
installed local `vllm` process and required host resources are available and
the runtime owner executor records that host-dependent evidence.

## Runtime Owner Rules

Do not add raw process, environment, HTTP, or runtime shortcuts in dashboard
code. Runtime-adjacent work must stay behind owner facades:

- HTTP transport through `app.io.http_sffi` or
  `std.nogc_sync_mut.io.http_sffi`
- process lifecycle through `app.io.mod` and `app.io.process_ops`
- dashboard-requested execution through
  `app.llm_runtime.dashboard_live_control_executor`
- pure dashboard decision/readback through
  `app.llm_runtime.dashboard_live_control`

If a new runtime capability is missing, add the smallest owner facade or record
the host/runtime blocker in the lane plan. Do not prove live readiness by
shelling out from dashboard rendering or by treating rendered buttons as
process evidence.

## Remaining Gates

The runtime lane is not fully complete until these host-dependent gates have
real evidence:

- local vLLM endpoint proof for serving readiness
- dashboard start, poll, probe, and stop execution against an installed local
  vLLM process
- svLLM NVFS streaming with async scheduling, pinned buffer registration, and
  device staging
- live CUDA optimizer execution through libtorch/CUDA
- PEFT/TRL fine-tuning orchestration and acceptance evidence

Run the canonical strict aggregate before any completion claim:

```sh
sh scripts/check/check-llm-goal-evidence.shs --strict-host
```

For operator setup triage, run the non-network prerequisite doctor first:

```sh
sh scripts/check/check-llm-strict-host-prereq-doctor.shs
```

Use `scripts/check/check-llm-strict-host-prereq-doctor-contract.shs` after
editing the doctor to verify the machine-readable env and Markdown report still
publish all per-lane `*_next_action` fields. The main
`scripts/check/check-llm-goal-evidence.shs` aggregate also runs this contract
as the `prereq_doctor_contract` lane.

The doctor does not replace the strict aggregate or the per-lane evidence
wrappers. It only reports whether this host has the dashboard auth/url, local
vLLM, native svLLM capability artifact, Simple-visible libtorch/CUDA, and
fine-tune retry artifacts needed before the strict wrappers can pass. Its
Markdown report mirrors the actionable env fields: the primary blocked gate,
dashboard URL/auth readiness, local vLLM command/module/GPU readiness, native
svLLM read-range/pinned-buffer/device-staging readiness, native svLLM
capability source/evidence schema-event-source-status matching, Torch/libtorch
readiness including Python Torch/CUDA visibility and system libtorch match
count, fine-tune retry artifact readiness, manifest metadata, a global next
operator action, and per-lane `*_next_action` fields for dashboard, vLLM,
svLLM, Torch, and fine-tune unblock routing. The vLLM prereq section also
records the base model and endpoint values, plus whether each came from
defaults or explicit env, but the
doctor does not contact the endpoint; endpoint reachability and `/v1/models`
remain strict vLLM host-probe evidence. The Torch prereq section runs the
local bridge setup wrapper, records `torch_bridge_status`,
`torch_bridge_output_status`, the exported `SIMPLE_SFFI_PATH`/`LIBTORCH`
values, and keeps `system_libtorch_status` as supporting host context only.
The fine-tune prereq section records
retry6 model-manifest and eval-result schema, attempt/base-model, deployable,
metric, dataset checksum, and sample fields when those artifacts exist; retry7
acceptance remains the strict evidence gate for licensing, safety, deployment,
decision, and app handoff.

Strict-host unblock checklist:

1. Dashboard live HTTP: export `LLM_DASHBOARD_LIVE_BASE_URL` for a running
   dashboard and exactly one non-secret auth source accepted by
   `scripts/check/check-llm-dashboard-live-http-evidence.shs`, then run that
   wrapper until `llm_dashboard_live_http_status=pass`.
2. vLLM host: install an importable Python `vllm` module and local `vllm`
   command, set `LLM_VLLM_BASE_MODEL` / `LLM_VLLM_ENDPOINT` (or the legacy
   `BASE_MODEL` / `ENDPOINT`) when defaults are not correct, start the endpoint, and run
   `scripts/check/check-llm-runtime-vllm-host-probe.shs --strict` until the
   local command, Python module, endpoint, and `/v1/models` gates pass.
   Use `scripts/check/check-llm-runtime-vllm-host-env-contract.shs` after
   editing the host probe to verify the documented `LLM_VLLM_*` env names still
   drive the base model and endpoint evidence; the main LLM goal aggregate also
   runs it as the `vllm_host_env_contract` lane.
3. svLLM native: produce a non-default native capability artifact with matching
   `SVLLM_NATIVE_CAPABILITY_SOURCE` and
   `SVLLM_NATIVE_CAPABILITY_EVIDENCE_PATH`, then run
   `scripts/check/check-llm-runtime-svllm-native-streaming-evidence.shs` and
   `SVLLM_NATIVE_EVIDENCE_ENV=build/llm_runtime_svllm_native_streaming/evidence.env sh scripts/check/check-llm-runtime-svllm-local-readiness.shs --strict-native`.
4. Torch/libtorch: run
   `scripts/setup/setup-llm-runtime-torch-sffi-bridge.shs` to build
   `libspl_torch.so` from the local Python Torch package, export the reported
   `SIMPLE_SFFI_PATH` and `LIBTORCH` values, and include the libtorch directory
   in `LD_LIBRARY_PATH`; then run
   `scripts/check/check-llm-runtime-torch-cuda-optimizer-probe.shs --strict`
   until the Simple optimizer probe records a CUDA parameter, gradient handle,
   optimizer step, and decreased parameter sum. The probe reports
   `simple_sffi_libtorch_bridge_status` separately from Python libtorch
   discovery so an exposed Python Torch bundle cannot mask a missing Simple
   SFFI bridge. Fresh runtime builds auto-discover `libspl_torch.so` from
   `SIMPLE_SFFI_PATH`; older deployed binaries may need
   `SIMPLE_TORCH_RUNTIME_PATH` pointed at the generated bridge as a temporary
   diagnostic override.
5. Fine-tune retry: complete the licensed cache review and retry6 training/eval
   artifacts under `.spipe/llm-finetune-process/artifacts/`, including
   `llm_backed_app_server_dry_run_retry6/model_manifest.json` and
   `llm_backed_app_server_dry_run_retry6/eval_result.json`, then run
   `scripts/check/check-llm-finetune-acceptance-evidence.shs` and
   `FINETUNE_ACCEPTANCE_EVIDENCE_ENV=build/llm_finetune_acceptance/evidence.env sh scripts/check/check-llm-finetune-guard-evidence.shs --strict-ready`.

Latest local host probe:
`doc/09_report/2026/06/llm_runtime_vllm_host_probe_2026-06-29.md` records a
repeatable `scripts/check/check-llm-runtime-vllm-host-probe.shs` readiness
run through the runtime-owned control CLI. On the current host it returns
`status=unavailable` with
`reason=missing_local_vllm` and
`blocked_gates=local_vllm|python_vllm_module|serve_preflight|endpoint_reachable|models_listed`.
The evidence env records `llm_runtime_vllm_host_probe_required_gates`,
`llm_runtime_vllm_host_probe_blocked_gates`,
`llm_runtime_vllm_host_probe_primary_blocked_gate`,
`llm_runtime_vllm_host_probe_base_model`,
`llm_runtime_vllm_host_probe_endpoint`,
`llm_runtime_vllm_host_probe_endpoint_scheme_status`,
`llm_runtime_vllm_host_probe_endpoint_host_status`,
`llm_runtime_vllm_host_probe_wrapper_path`,
`llm_runtime_vllm_host_probe_wrapper_sha256`,
`llm_runtime_vllm_host_probe_control_cli_path`,
`llm_runtime_vllm_host_probe_control_cli_sha256`,
`llm_runtime_vllm_host_probe_probe_command_sha256`,
`llm_runtime_vllm_host_probe_local_vllm_status`,
`llm_runtime_vllm_host_probe_vllm_command_path`,
`llm_runtime_vllm_host_probe_vllm_version_log_size`,
`llm_runtime_vllm_host_probe_vllm_version_log_sha256`,
`llm_runtime_vllm_host_probe_python_vllm_module_status`,
`llm_runtime_vllm_host_probe_python_vllm_origin`,
`llm_runtime_vllm_host_probe_python_vllm_version`,
`llm_runtime_vllm_host_probe_python_vllm_probe_log_size`,
`llm_runtime_vllm_host_probe_python_vllm_probe_log_sha256`,
`llm_runtime_vllm_host_probe_local_gpu_status`,
`llm_runtime_vllm_host_probe_nvidia_smi_path`,
`llm_runtime_vllm_host_probe_gpu_probe_log_size`,
`llm_runtime_vllm_host_probe_gpu_probe_log_sha256`,
`llm_runtime_vllm_host_probe_readiness_status`,
`llm_runtime_vllm_host_probe_preflight_status`,
`llm_runtime_vllm_host_probe_endpoint_status`, and
`llm_runtime_vllm_host_probe_models_status`, and
`llm_runtime_vllm_host_probe_models_reason`,
`llm_runtime_vllm_host_probe_log_size`,
`llm_runtime_vllm_host_probe_status`,
`llm_runtime_vllm_host_probe_reason`,
`llm_runtime_vllm_host_probe_required_gates`,
`llm_runtime_vllm_host_probe_blocked_gates`,
`llm_runtime_vllm_host_probe_cli_exit`,
`llm_runtime_vllm_host_probe_event`,
`llm_runtime_vllm_host_probe_log_sha256`,
`llm_runtime_vllm_host_probe_serve_readiness_run_event_count`,
`llm_runtime_vllm_host_probe_pass_integrity_status`,
`llm_runtime_vllm_host_probe_pass_integrity_reason`,
`llm_runtime_vllm_host_probe_report_path`,
`llm_runtime_vllm_host_probe_report_size`,
`llm_runtime_vllm_host_probe_report_sha256`, and
`llm_runtime_vllm_host_probe_next_action` so strict aggregate runs can report
the first local serving blocker, full blocker list, pass-log integrity, and
next operator step. The wrapper accepts a PASS only when endpoint setup is
well-formed, wrapper/control CLI/probe command provenance is hashed, report
provenance is present, the runtime event is
`llm_runtime_vllm_serve_readiness_run`, CLI exit is zero, blocked gates are
`none`, the local vLLM executable is available, the Python `vllm` module is
available with a non-missing origin, GPU tooling is available, readiness is
`ready`, endpoint is `configured`, model listing is `ready`, models reason is
`models_endpoint_ready`, and the hashed readiness log contains exactly one
serve-readiness run event. The
models-list classifier treats `models_status=ready` as satisfying
`models_listed`, matching the strict pass condition. Keep
`FR-LLM-RUNTIME-0001` open until a
configured local endpoint reaches `status=ready`, `endpoint=configured`, and
`models_status=ready` after `/v1/models` serves the selected base model.
If a host is missing GPU tooling too, `local_gpu` is added to the blocked-gates
list independently of the collapsed control-CLI reason.
If the executable exists but the Python module cannot be imported,
`python_vllm_module` remains blocked even when the control CLI can still render
skipped or planned evidence.
The local `vllm --version`, Python `vllm` module discovery, and `nvidia-smi`
GPU probes are written as bounded logs with SHA-256 hashes, so missing-host
evidence can be traced to the exact command/module checks that ran.
The wrapper also records a surface manifest count, size, and SHA-256 for the
runtime control/readiness source files, unit specs, agent task plan, LLM runtime
runbook, and dashboard guide that define the local serve-readiness path; the
aggregate forwards those fields in `llm_goal_evidence_vllm_host_detail`. This
prevents strict host evidence from mixing a fresh probe with stale operator
instructions.
Run the wrapper with `--strict` when unavailable or readiness-incomplete hosts must
fail the lane.

Latest svLLM local readiness evidence:
`doc/09_report/2026/06/llm_runtime_svllm_local_readiness_2026-06-29.md`
records `scripts/check/check-llm-runtime-svllm-local-readiness.shs` passing the
pack CLI, manifest, tensor-byte, stream-plan, std_fs local-read, and
streaming-readiness contracts with per-spec timeout handling through
`SVLLM_READINESS_SPEC_TIMEOUT_SECONDS` (default `120`). It also records a
surface manifest count, size, and SHA-256 for the eight checked local readiness
specs plus their produced logs, and the focused env/report include per-log size
and SHA-256 values. The aggregate forwards those local manifest fields in
`llm_goal_evidence_svllm_local_detail`. Keep
`src/app/svllm_pack/main.spl` as a thin entrypoint over
`src/app/svllm_pack/core.spl`; unit specs import `core.run` so app entrypoint
discovery cannot turn passing examples into a file-level failure. The local
readiness wrapper also treats the two svLLM pack specs as pass when their logs
contain `examples, 0 failures` and no failed-example marker, private helper
collision warning, or short-grammar "Common mistake detected" diagnostic; it
keeps the raw nonzero runner exit in the evidence fields so that warning-exit
normalization remains visible.
Keep
`FR-LLM-RUNTIME-0002` open because that wrapper proves only local file-backed
readiness; native NVFS async scheduling, pinned buffer registration, device
staging, and true streaming model loads still need live evidence. Run
`scripts/check/check-llm-runtime-svllm-native-streaming-evidence.shs` to produce
the native evidence env. It records concrete blockers such as
`native_read_range_unavailable` and only passes when native read_range, pinned
buffer registration, and device staging are all ready. Native evidence records
`svllm_native_streaming_local_spec_timeout_seconds` so nested local-readiness
timeouts remain visible when strict aggregate evidence is collected.
It also writes `svllm_native_streaming_blocked_gates`,
`svllm_native_streaming_primary_blocked_gate`, and
`svllm_native_streaming_next_action`; strict local readiness forwards those
fields as `llm_runtime_svllm_local_readiness_native_*` so aggregate reports use
the producer's canonical blocker contract instead of re-deriving it.
The native wrapper also records SHA-256 and size metadata for the nested
local-readiness env, log, and report, making strict native evidence traceable to
the exact local readiness run it consumed.
It also writes `svllm_native_streaming_surface_manifest`,
`svllm_native_streaming_surface_manifest_count`,
`svllm_native_streaming_surface_manifest_size`, and
`svllm_native_streaming_surface_manifest_sha256` for the wrapper, local
readiness wrapper, streaming readiness implementation, stream/transport
helpers, focused specs, and this guide. Strict aggregate detail forwards those
native manifest fields when `--strict-host` collects native svLLM evidence.
Configured native hosts provide those native capability results through
`SVLLM_NATIVE_READ_RANGE_STATUS`, `SVLLM_NATIVE_PINNED_BUFFER_STATUS`, and
`SVLLM_NATIVE_DEVICE_STAGING_STATUS`. Values normalize to `ready`,
`unsupported`, `unavailable`, or `unchecked`; omitted values default to
`unsupported`. When callers do not provide `SVLLM_NATIVE_CAPABILITY_SOURCE` or
`SVLLM_NATIVE_CAPABILITY_EVIDENCE_PATH`, the native streaming wrapper runs
`scripts/check/check-llm-runtime-svllm-native-capability-probe.shs` and consumes
its schema-v1 artifact. That local probe is fail-closed: it records
`unsupported` for read-range, pinned-buffer, and device-staging support with
`svllm_native_capability_source=local_simple_svllm_capability_probe`, so reports
show a probed unsupported state instead of ambiguous missing provenance. The
same probe also executes the StdFs NVFS client spec and records
`svllm_native_capability_local_read_range_bytes_status` plus
`svllm_native_capability_local_read_range_bytes_reason`. A `ready` value there
only proves the bounded local `read_range_bytes` helper through checked-in
specs; it does not satisfy native caller-buffer `read_range`, pinned-buffer
registration, or device staging. The native streaming wrapper forwards those
fields as
`svllm_native_streaming_capability_evidence_local_read_range_bytes_status` and
`svllm_native_streaming_capability_evidence_local_read_range_bytes_reason` so
strict reports can show local file-backed progress without turning the native
streaming gate green. The
native streaming report records
`svllm_native_streaming_capability_source` and
`svllm_native_streaming_capability_provenance_status` so reviewers can
distinguish an explicit host probe from the default fallback. A strict native
PASS requires either `SVLLM_NATIVE_CAPABILITY_SOURCE` to name the probe or
artifact that proved the ready native capabilities, or a non-empty
`SVLLM_NATIVE_CAPABILITY_EVIDENCE_PATH` whose schema-v1 artifact carries
`svllm_native_capability_source`; the wrapper derives the source from that
artifact when the env source is omitted.
It also writes `svllm_native_streaming_pass_integrity_status` and
`svllm_native_streaming_pass_integrity_reason`; PASS integrity requires local
readiness, all three native capability statuses, provenance, and the evidence
artifact to be present together. The artifact is a line-oriented schema-v1 env
file with `svllm_native_capability_source` matching the explicit or
artifact-derived capability source,
`svllm_native_capability_probe_event=svllm_native_capability_probe`,
`svllm_native_capability_probe_status=pass`,
`svllm_native_capability_probe_exit=0`, and reported read-range, pinned-buffer,
and device-staging statuses that match the wrapper inputs. The wrapper records
the artifact SHA-256, size, mtime, source, schema version,
probe event/status/exit, and the artifact-reported read-range, pinned-buffer,
and device-staging statuses. Strict aggregate detail forwards those fields as
`capability_evidence_mtime`,
`capability_evidence_reported_read_range_status`,
`capability_evidence_reported_pinned_buffer_status`, and
`capability_evidence_reported_device_staging_status`, so a top-level report can
prove the artifact matched the claimed native capability inputs without opening
the nested native evidence env. It also forwards
`svllm_native_streaming_capability_probe_report`,
`svllm_native_streaming_capability_probe_report_size`, and
`svllm_native_streaming_capability_probe_report_sha256` when the local
fail-closed probe produced the default artifact.

Latest Torch/CUDA host probe:
`doc/09_report/2026/06/llm_runtime_torch_cuda_host_probe_2026-06-28.md`
records Python Torch `2.9.1+cu130` with CUDA available and visible NVIDIA GPUs,
plus a passing Simple dynamic Torch SFFI readiness spec. Keep
`FR-LLM-RUNTIME-0003` open until Simple/libtorch executes and records a real
CUDA optimizer step.

Latest Simple/libtorch optimizer probe:
`doc/09_report/2026/06/llm_runtime_torch_cuda_optimizer_probe_2026-06-29.md`
records `scripts/check/check-llm-runtime-torch-cuda-optimizer-probe.shs`
classifying the self-hosted Simple runtime as `unavailable` with
`reason=libtorch_unavailable` on this host. The evidence env records
`torch_cuda_optimizer_probe_required_gates`,
`torch_cuda_optimizer_probe_blocked_gate`,
`torch_cuda_optimizer_probe_blocked_gates`,
`torch_cuda_optimizer_probe_primary_blocked_gate`,
`torch_cuda_optimizer_probe_wrapper_path`,
`torch_cuda_optimizer_probe_wrapper_sha256`,
`torch_cuda_optimizer_probe_probe_path`,
`torch_cuda_optimizer_probe_probe_sha256`,
`torch_cuda_optimizer_probe_probe_command`,
`torch_cuda_optimizer_probe_probe_command_sha256`,
`torch_cuda_optimizer_probe_python_torch_module_status`,
`torch_cuda_optimizer_probe_python_torch_version`,
`torch_cuda_optimizer_probe_python_torch_file`,
`torch_cuda_optimizer_probe_python_torch_package_dir`,
`torch_cuda_optimizer_probe_python_torch_cmake_prefix_path`,
`torch_cuda_optimizer_probe_python_torch_library_paths`,
`torch_cuda_optimizer_probe_python_torch_library_count`,
`torch_cuda_optimizer_probe_python_torch_libtorch_status`,
`torch_cuda_optimizer_probe_python_torch_libtorch_cuda_status`,
`torch_cuda_optimizer_probe_python_torch_libc10_status`,
`torch_cuda_optimizer_probe_python_torch_libc10_cuda_status`,
`torch_cuda_optimizer_probe_python_torch_cuda_library_bundle_status`,
`torch_cuda_optimizer_probe_python_torch_cuda_available`,
`torch_cuda_optimizer_probe_python_torch_cuda_device_count`,
`torch_cuda_optimizer_probe_python_torch_env_size`,
`torch_cuda_optimizer_probe_python_torch_env_sha256`,
`torch_cuda_optimizer_probe_system_libtorch_status`,
`torch_cuda_optimizer_probe_system_libtorch_probe_log_size`,
`torch_cuda_optimizer_probe_system_libtorch_probe_log_sha256`,
`torch_cuda_optimizer_probe_surface_manifest_count`,
`torch_cuda_optimizer_probe_surface_manifest_size`,
`torch_cuda_optimizer_probe_surface_manifest_sha256`,
`torch_cuda_optimizer_probe_torch_available_normalized`,
`torch_cuda_optimizer_probe_cuda_available_normalized`,
`torch_cuda_optimizer_probe_parameter_is_cuda_normalized`,
`torch_cuda_optimizer_probe_grad_handle_normalized`, and
`torch_cuda_optimizer_probe_optimizer_step_attempted_normalized`, and
`torch_cuda_optimizer_probe_sum_decreased_status`,
`torch_cuda_optimizer_probe_pass_integrity_status`,
`torch_cuda_optimizer_probe_pass_integrity_reason`, and
`torch_cuda_optimizer_probe_next_action` so strict aggregate runs can report the
compact blocked Torch gate list, the first blocked gate, independent pass-log
integrity, the Python Torch wheel file/package/CMake/library path diagnostics,
explicit Python wheel libtorch/libc10 CUDA library-bundle readiness, the hashed
Python Torch discovery env, the hashed system libtorch probe, the hashed wrapper
and probe source, the hashed probe command, the hashed Torch optimizer
source/spec/doc surface, and the next operator step. A
probe `status=pass` is accepted only
when the wrapper also sees a zero wrapper exit, a non-empty hashed probe log,
exactly one complete proof record for status, required gates, libtorch/CUDA
availability, CUDA parameter placement, gradient handle, optimizer step, and
before/after sums, plus normalized libtorch/CUDA availability, CUDA parameter
placement, a nonzero gradient handle, an attempted optimizer step, and numeric
`after_sum < before_sum`. Use this wrapper as the
canonical evidence path for the real CUDA optimizer-step gate; run it with
`--strict` when unavailable hosts must fail the lane instead of recording a
warning.

`scripts/check/check-llm-runtime-torch-setup-contract.shs` is the focused
diagnostic contract for that wrapper. It does not turn the Torch optimizer
blocker green; it proves the default wrapper continues to expose Python
Torch/CUDA visibility, system libtorch visibility, hashed surface-manifest
provenance, and a concrete `next_action` for unconfigured hosts.

## Focused Checks

Use the aggregate local LLM evidence wrapper when checking the current
context/Ponytail, dashboard, vLLM, svLLM, Torch, fine-tune, and public-absence
lanes together:

```bash
sh scripts/check/check-llm-goal-evidence.shs
```

The aggregate report is written to
`doc/09_report/2026/06/llm_goal_evidence_2026-06-29.md`. It treats live vLLM
and Simple/libtorch CUDA optimizer host gaps as expected WARN lanes on hosts
where those dependencies are not installed, while fine-tune readiness remains a
guard-only pass in default mode. Default mode also generates repo-local
context/Ponytail full-replacement evidence before running the context/Ponytail
lane, so the detail row shows checked-in Simple-owned replacement surfaces
instead of only mimic evidence. That detail includes the checked surface
manifest count, size, SHA-256, execution-spec log size/SHA-256, and mimic env
size/SHA-256 so a passing replacement row is tied to exact repo-local source
and spec artifacts. The aggregate env also records
`llm_goal_evidence_context_ponytail_detail` for mimic/full-replacement state,
`llm_goal_evidence_dashboard_detail` for dashboard live-readiness state,
including the strict dashboard route surface manifest count, size, SHA-256,
dashboard evidence env/log size and SHA-256, live HTTP status, live HTTP
auth source type, response hashes, and the live dashboard next action,
`llm_goal_evidence_vllm_host_detail` for local
vLLM/GPU/preflight/endpoint/model statuses and pass-log integrity, and
`llm_goal_evidence_svllm_local_detail` for native svLLM streaming status,
native blocker reason, local readiness, native `read_range`, pinned-buffer,
device-staging, capability source, capability provenance, capability evidence
artifact status, source, and hash metadata, probe event/status/exit, pass integrity,
local file-backed byte-read states, native blocked gates, primary blocked gate,
and next action.
In default mode, dashboard live HTTP and svLLM native streaming evidence are
collected as non-blocking diagnostic producers. The default dashboard lane still
passes or fails on route/collector evidence, but its detail row forwards live
HTTP blocked gates, auth source, response hashes, surface manifest, and next
action. The default svLLM lane still passes or fails on local file-backed
readiness, but its detail row forwards the native producer's blocked gates,
capability provenance, surface manifest, and next action. Strict host mode
consumes the same live dashboard and native streaming evidence as
release-completion gates. The svLLM blocker table is mode-aware too: default mode
reports the `local_readiness` gate with no lane-blocking native gates, while
strict host mode reports the native producer's `blocked_gates` and
`next_action` contract. It
also records
`llm_goal_evidence_torch_optimizer_detail` for Simple/libtorch CUDA optimizer
status, compact blocked gates, primary blocked gate, Python Torch/CUDA host
visibility, Python Torch wheel path diagnostics, system libtorch visibility,
Simple runtime gates, gradient handle, system libtorch probe-log hash,
optimizer-step attempt, before/after parameter sums, sum-decrease status, and
pass-log integrity. vLLM
and Torch detail rows include the focused
wrapper `next_action` values. It also records
`llm_goal_evidence_finetune_guard_detail` for the fine-tune guard and
acceptance path. In default mode this comes from the freshly-run guard wrapper
and reports guard status, strict-ready mode, guard blocked gates, primary guard
blocker, guard reason, and next action. In strict host mode it reports the
fresh acceptance evidence status, reason, gate exit/status, compact blocked
gates, training/model/eval readiness, license, safety, deployment, app handoff,
decision status, and next action. Those detail fields are diagnostic only; they
do not relax the strict host gates.

Latest fine-tune acceptance evidence:
`doc/09_report/2026/06/llm_finetune_acceptance_2026-06-29.md` records
`scripts/check/check-llm-finetune-acceptance-evidence.shs` failing the retry7
normal acceptance gate with `reason=BLOCKED_RETRY6_NOT_READY`. The evidence env
records `llm_finetune_acceptance_required_gates`,
`llm_finetune_acceptance_blocked_gates`,
`llm_finetune_acceptance_primary_blocked_gate`,
`llm_finetune_acceptance_training_allowed`,
`llm_finetune_acceptance_gate_log_artifact_status`,
`llm_finetune_acceptance_gate_log_sha256`,
`llm_finetune_acceptance_surface_manifest_count`,
`llm_finetune_acceptance_surface_manifest_size`,
`llm_finetune_acceptance_surface_manifest_sha256`,
`llm_finetune_acceptance_upstream_attempt_record`,
`llm_finetune_acceptance_upstream_attempt_record_artifact_status`,
`llm_finetune_acceptance_upstream_attempt_record_sha256`,
`llm_finetune_acceptance_upstream_cache_manifest`,
`llm_finetune_acceptance_upstream_cache_manifest_artifact_status`,
`llm_finetune_acceptance_upstream_cache_manifest_sha256`,
`llm_finetune_acceptance_attempt_record`,
`llm_finetune_acceptance_attempt_record_sha256`,
`llm_finetune_acceptance_attempt_record_size`,
`llm_finetune_acceptance_model_manifest`,
`llm_finetune_acceptance_model_manifest_exists`,
`llm_finetune_acceptance_model_manifest_artifact_status`,
`llm_finetune_acceptance_model_manifest_sha256`,
`llm_finetune_acceptance_model_manifest_size`,
`llm_finetune_acceptance_model_manifest_schema_version`,
`llm_finetune_acceptance_model_manifest_attempt_id`,
`llm_finetune_acceptance_base_model`,
`llm_finetune_acceptance_base_model_revision`,
`llm_finetune_acceptance_model_artifact_status`,
`llm_finetune_acceptance_model_artifact_sha256`,
`llm_finetune_acceptance_model_artifact_size`,
`llm_finetune_acceptance_model_manifest_deployable`,
`llm_finetune_acceptance_eval_result`,
`llm_finetune_acceptance_eval_result_exists`,
`llm_finetune_acceptance_eval_result_artifact_status`,
`llm_finetune_acceptance_eval_result_sha256`,
`llm_finetune_acceptance_eval_result_size`,
`llm_finetune_acceptance_eval_result_schema_version`,
`llm_finetune_acceptance_eval_result_status`,
`llm_finetune_acceptance_eval_metric_name`,
`llm_finetune_acceptance_eval_metric_value`,
`llm_finetune_acceptance_eval_metric_target`,
`llm_finetune_acceptance_eval_dataset_id`,
`llm_finetune_acceptance_eval_dataset_checksum`,
`llm_finetune_acceptance_eval_samples`,
`llm_finetune_acceptance_required_accuracy`,
`llm_finetune_acceptance_retry6_next_action`,
`llm_finetune_acceptance_decision_status`,
`llm_finetune_acceptance_handoff_doc`,
`llm_finetune_acceptance_handoff_doc_artifact_status`,
`llm_finetune_acceptance_handoff_doc_sha256`,
`llm_finetune_acceptance_handoff_doc_size`,
`llm_finetune_acceptance_handoff_usage`,
`llm_finetune_acceptance_pass_integrity_status`, and
`llm_finetune_acceptance_next_action` so strict aggregate runs can report the
first concrete blocker, the exact upstream artifact refs to fill, and the
model/eval/license/safety/deployment/app-handoff blocker list. The gate-log and
upstream retry5 hashes make a blocked acceptance report traceable to the exact
normal-review gate output and cache/attempt artifacts it consumed.
The wrapper passes only when retry7 reports `acceptance_allowed=true` and the
normalized `llm_finetune_acceptance_blocked_gates` value is `none`, and
`llm_finetune_acceptance_pass_integrity_status=pass` after hashing local
attempt, model manifest, model artifact, eval result, and handoff artifacts and
extracting schema/linkage fields. PASS integrity also requires a deployable
model manifest, passing eval result, metric target metadata, dataset checksum,
eval sample count, and deployable handoff usage. A retry7 PASS line cannot
override missing model, eval, license, safety, deployment, handoff, or
artifact-integrity evidence.
The acceptance wrapper also writes a checked surface manifest for the retry6
and retry7 gate scripts/specs, this wrapper, the guard wrapper, the operator
guide, the agent task plan, and the produced retry7 gate log. Aggregate
fine-tune detail forwards the acceptance surface manifest count/size/SHA-256,
so strict review can distinguish stale process scripts from missing model/eval
artifacts.

The local fine-tune guard evidence writes its own current blocker contract to
`build/llm_finetune_guard_evidence/evidence.env`. Default aggregate mode uses
that guard env for fine-tune required gates, blocked gates, blocker reason, and
next action; strict host mode still uses the acceptance env generated during
the strict run. The guard env also records a manifest count, size, and SHA-256
for the fixed-format data file, retry6/retry7 gate scripts, retry6/retry7 SSpec
files, the retry5 cache-manifest checker, and produced guard/spec logs, plus
per-log sizes and SHA-256 values including
`llm_finetune_guard_retry5_cache_log_size` and
`llm_finetune_guard_retry5_cache_log_sha256`. The guard forwards retry5 cache
manifest artifact status, size, and SHA-256 as
`llm_finetune_guard_retry5_cache_manifest_artifact_status`,
`llm_finetune_guard_retry5_cache_manifest_size`, and
`llm_finetune_guard_retry5_cache_manifest_sha256`; strict-ready mode also
emits `llm_finetune_guard_acceptance_attempt` and fails if the consumed
acceptance env is not for the configured retry7 attempt.
Guard-only fine-tune evidence is therefore traceable to exact local process
inputs and outputs.

On a configured host, use strict host mode when the aggregate must be
release-completion evidence for the live gates:

```bash
sh scripts/check/check-llm-goal-evidence.shs --strict-host
```

Strict host mode first runs the live dashboard HTTP producer, then generates
authenticated dashboard route evidence and fine-tune retry7 acceptance evidence,
reuses the same repo-local context/Ponytail full-replacement contract, and
passes the focused strict flags to the context/Ponytail, dashboard, vLLM, svLLM,
Torch optimizer, and fine-tune wrappers. It clears each strict producer's
canonical `evidence.env` before the producer runs so stale results cannot mask a
timeout or early producer failure. When no dashboard URL is configured, strict
dashboard detail reports the live HTTP `base_url` blocker from
`check-llm-dashboard-live-http-evidence.shs` instead of a generic missing-env
failure; if authentication is also absent or invalid, the same no-network path
reports `base_url|auth_configured` so both setup tasks stay visible. The live
HTTP producer always writes
`llm_dashboard_live_http_surface_manifest_count`,
`llm_dashboard_live_http_surface_manifest_size`, and
`llm_dashboard_live_http_surface_manifest_sha256`, even for
`missing_base_url`, so strict dashboard failures are tied to the exact wrapper,
dashboard route source, route specs, and operator docs used by the live proof.
The dashboard detail also forwards per-route live HTTP status and reason fields:
`live_http_dashboard_status`/`live_http_dashboard_reason`,
`live_http_agents_status`/`live_http_agents_reason`,
`live_http_control_status`/`live_http_control_reason`, and
`live_http_unauth_api_status`/`live_http_unauth_api_reason`. The live HTTP
producer also emits non-secret setup diagnostics before network calls:
`llm_dashboard_live_http_base_url_status`,
`llm_dashboard_live_http_base_url_scheme_status`,
`llm_dashboard_live_http_auth_config_status`,
`llm_dashboard_live_http_auth_source`, and
`llm_dashboard_live_http_timeout_seconds`. These fields distinguish missing
dashboard URL, malformed URL, and missing auth configuration without printing
secrets or treating route-contract evidence as live HTTP proof.
Use `scripts/check/check-llm-dashboard-live-http-setup-contract.shs` after
editing the live HTTP wrapper to verify the no-URL/no-auth path keeps the
combined `base_url|auth_configured` blocker and report `next_action`; the main
LLM goal aggregate also runs it as the `dashboard_http_setup_contract` lane.
The aggregate expects all completion lanes to pass, fails for any WARN
or missing strict evidence result, and writes `llm_goal_evidence_failed_gates`,
`llm_goal_evidence_failed_gate_hints`, `llm_goal_evidence_warn_gates`, and
per-lane `llm_goal_evidence_<lane>_hint` and
`llm_goal_evidence_<lane>_producer_exit` and
`llm_goal_evidence_<lane>_producer_log` values to the env file for direct
triage. Producer fields are `n/a` for lanes without a strict producer in the
current mode. It also copies focused blocker details into
`llm_goal_evidence_<lane>_required_gates`,
`llm_goal_evidence_<lane>_blocked_gates`, and
`llm_goal_evidence_<lane>_primary_blocked_gate`, and
`llm_goal_evidence_<lane>_blocker_reason` for strict context/Ponytail
replacement, strict live dashboard, vLLM, svLLM, Torch optimizer, and fine-tune
lanes so operators can triage strict failures from the aggregate report without
opening every focused env first; the Markdown Blocker Details table shows the
same primary blocked gate as a dedicated column. It also writes
`llm_goal_evidence_<lane>_next_action` and a report `Next Actions` table for
all aggregate lanes, including context/Ponytail replacement, live dashboard,
host runtime, fine-tune, and public absence rendering triage. The detail table also includes
context/Ponytail replacement subfields including the replacement primary
blocked gate, live dashboard route and live HTTP subfields including the live
dashboard primary blocked gate and non-secret auth source type, svLLM native streaming subfields, Torch
optimizer subfields, and
fine-tune acceptance subfields needed to distinguish missing replacement
surfaces, dashboard route/auth gaps, missing authenticated live HTTP proof,
missing native streaming support, a missing host runtime, a failed optimizer
step, and a blocked retry/eval gate from a licensing, safety, deployment, or
app-handoff blocker.
Aggregate lane execution unsets the aggregate `BUILD_DIR` before invoking
focused wrappers, so detail rows consume each wrapper's canonical
`build/<lane>/evidence.env` instead of stale env files from older standalone
runs.

Use the focused public-rendering guard after changing runtime manuals,
dashboard JSONL wording, or evidence docs:

```bash
sh scripts/check/check-llm-tooling-public-absence-rendering.shs
```

The public-rendering guard writes
`build/llm_tooling_public_absence_rendering/evidence.env` and
`doc/09_report/2026/06/llm_tooling_public_absence_rendering_<date>.md`.
The env records the required absence-marker gates, blocked gates, failure
count, and a hashed `public_absence_surface_manifest.tsv` covering the public
manuals, generated/manual SPipe docs, dashboard wording, and LLM runtime
evidence surfaces it scanned. The aggregate forwards those values through
`llm_goal_evidence_public_absence_detail`, so a passing public absence lane
must include a reproducible manifest count/size/hash, not only a terminal
`STATUS: PASS` line.

Use the LLM feature database reference guard after changing feature rows,
generated/manual spec locations, fine-tune process paths, dashboard references,
or runtime evidence references:

```bash
sh scripts/check/check-llm-feature-db-reference-integrity.shs
```

The guard writes `build/llm_feature_db_reference_integrity/evidence.env` and
`doc/09_report/2026/06/llm_feature_db_reference_integrity_<date>.md`. It scans
only the LLM, SPipe LLM, and dashboard feature rows in
`doc/08_tracking/feature/feature_db.sdn`, verifies every referenced local
`doc/`, `test/`, `src/`, `scripts/`, `.spipe/`, and `examples/` path exists,
and fails if the known stale svLLM generated-spec paths under
`doc/06_spec/01_unit/lib/gc_async_mut/svllm/...` reappear instead of the real
`doc/06_spec/test/01_unit/...` generated docs. The aggregate forwards this as
`llm_goal_evidence_feature_db_reference_detail`, so a passing aggregate also
proves LLM feature tracking rows do not point at missing local evidence.

Use the focused vLLM host probe after changing vLLM control CLI, live
environment detection, dashboard control JSONL, or host preflight behavior:

```bash
sh scripts/check/check-llm-runtime-vllm-host-probe.shs
```

Use the focused svLLM local readiness gate after changing svLLM pack manifests,
tensor byte loading, stream planning, std_fs local reads, or readiness evidence:

```bash
sh scripts/check/check-llm-runtime-svllm-local-readiness.shs
```

Use strict native mode on hosts or CI lanes that are supposed to prove real
svLLM streaming:

```bash
sh scripts/check/check-llm-runtime-svllm-native-streaming-evidence.shs
SVLLM_NATIVE_EVIDENCE_ENV=build/llm_runtime_svllm_native_streaming/evidence.env \
  sh scripts/check/check-llm-runtime-svllm-local-readiness.shs --strict-native
```

`scripts/check/check-llm-runtime-svllm-setup-contract.shs` is the focused
diagnostic contract for this lane. It runs the default native streaming wrapper
and local readiness wrapper, then verifies local-readiness proof, native
read-range/pinned-buffer/device-staging blocker diagnostics, capability
provenance fields, surface-manifest hashes, and `next_action` fields remain
present. It does not mark native svLLM streaming complete.

The strict native gate requires the evidence env to report
`svllm_native_streaming_status=pass`; local file-backed bytes are recorded as
bring-up evidence but are not enough for native streaming completion. Ready
native capability env values require matching structured evidence; the artifact
must record the same source string as the explicit or artifact-derived source,
and strict aggregate detail forwards that artifact source as
`capability_evidence_source`. Status-only ready claims fail as
`capability_evidence`. Strict local readiness requires
`svllm_native_streaming_status=pass` and
`svllm_native_streaming_pass_integrity_status=pass` plus complete native
provenance fields. It exposes
`llm_runtime_svllm_local_readiness_native_evidence_completeness_status`,
`llm_runtime_svllm_local_readiness_native_capability_provenance_status`,
`llm_runtime_svllm_local_readiness_native_capability_evidence_status`,
`llm_runtime_svllm_local_readiness_native_surface_manifest_count`, and
`llm_runtime_svllm_local_readiness_native_surface_manifest_sha256`, so a
status-only native env cannot satisfy strict completion.
The native evidence env also exposes the strict contract manifest fields
`svllm_native_streaming_surface_manifest_count`,
`svllm_native_streaming_surface_manifest_size`, and
`svllm_native_streaming_surface_manifest_sha256`; use them to confirm a stale
wrapper/spec/doc bundle was not mixed with a newer native capability artifact.

Use the focused Torch optimizer gate after changing Torch SFFI, CUDA placement,
or runtime training behavior:

The wrapper records Python Torch discovery separately from Simple runtime
availability. If `python_torch_libtorch_bundle_status=ready` and
`python_torch_cuda_library_bundle_status=ready` but `torch_available=false`,
the next setup step is to run the Torch SFFI bridge setup wrapper, expose its
reported `SIMPLE_SFFI_PATH` and libtorch directory, and rerun the strict
optimizer probe. That setup evidence is not optimizer completion. If the probe
then reports
`simple_runtime_torch_link_status=missing_after_libtorch_env_exposed`, the
library bundle and bridge are visible but the running Simple binary likely
needs the Torch SFFI auto-discovery loader rebuild, or a temporary
`SIMPLE_TORCH_RUNTIME_PATH` diagnostic override. Strict completion still
requires the probe to show Simple/libtorch availability, CUDA availability,
CUDA parameter placement, gradient production, and a decreasing optimizer step.
If the diagnostic override gets availability to `true` but the probe reports
`blocked_gate=torch_extern_surface`, the loader path is working and the next
implementation task is registering or implementing the named `rt_torch_*`
extern in the interpreter/runtime Torch surface.

```bash
sh scripts/check/check-llm-runtime-torch-cuda-optimizer-probe.shs
```

Before final handoff for runtime-adjacent changes, also run the direct
environment/runtime guards for working and staged content.

Latest strict-completion audit:
`doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`.
Default aggregate evidence passes with host-dependent WARN lanes for vLLM and
Torch. Strict-host completion still fails live dashboard HTTP auth/base URL,
local vLLM serving, native svLLM streaming, Simple-visible libtorch optimizer
execution, and fine-tune retry6/7 acceptance. Context/Ponytail full replacement
is passing.
Track those blockers in
`doc/08_tracking/bug/llm_strict_host_completion_blockers_2026-06-29.md`.
When updating the audit or tracker without collecting live host evidence, run:

```bash
sh scripts/check/check-llm-strict-blocker-tracker.shs
```

The guard checks that the committed tracker, strict audit, and latest default
aggregate evidence still agree on open strict blockers plus the current vLLM,
Torch, and public absence manifest provenance. It does not collect live host
evidence; it fails when the default aggregate no longer matches the
tracker/audit, when public absence failure count is nonzero, or when manifest
counts and hashes drift. It requires the aggregate Markdown report to match
when present, and falls back to
`build/llm_goal_evidence/evidence.env` only while that report is absent during
regeneration. It is a drift check, not strict-host completion evidence.

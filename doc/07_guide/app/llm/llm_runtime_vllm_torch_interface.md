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

Latest local host probe:
`doc/09_report/2026/06/llm_runtime_vllm_host_probe_2026-06-29.md` records a
repeatable `scripts/check/check-llm-runtime-vllm-host-probe.shs` readiness
run through the runtime-owned control CLI. On the current host it returns
`status=unavailable` with
`reason=missing_local_vllm` and
`blocked_gates=local_vllm|serve_preflight|endpoint_reachable|models_listed`.
The evidence env records `llm_runtime_vllm_host_probe_required_gates`,
`llm_runtime_vllm_host_probe_blocked_gates`,
`llm_runtime_vllm_host_probe_primary_blocked_gate`,
`llm_runtime_vllm_host_probe_base_model`,
`llm_runtime_vllm_host_probe_endpoint`,
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
`llm_runtime_vllm_host_probe_log_sha256`,
`llm_runtime_vllm_host_probe_serve_readiness_run_event_count`,
`llm_runtime_vllm_host_probe_pass_integrity_status`,
`llm_runtime_vllm_host_probe_pass_integrity_reason`, and
`llm_runtime_vllm_host_probe_next_action` so strict aggregate runs can report
the first local serving blocker, full blocker list, pass-log integrity, and
next operator step. The wrapper accepts a PASS only when the runtime event is
`llm_runtime_vllm_serve_readiness_run`, CLI exit is zero, blocked gates are
`none`, local vLLM/GPU are available, readiness is `ready`, endpoint is
`configured`, model listing is `ready`, models reason is
`models_endpoint_ready`, and the hashed readiness log contains exactly one
serve-readiness run event. The
models-list classifier treats `models_status=ready` as satisfying
`models_listed`, matching the strict pass condition. Keep
`FR-LLM-RUNTIME-0001` open until a
configured local endpoint reaches `status=ready`, `endpoint=configured`, and
`models_status=ready` after `/v1/models` serves the selected base model.
If a host is missing GPU tooling too, `local_gpu` is added to the blocked-gates
list independently of the collapsed control-CLI reason.
The local `vllm --version`, Python `vllm` module discovery, and `nvidia-smi`
GPU probes are written as bounded logs with SHA-256 hashes, so missing-host
evidence can be traced to the exact command/module checks that ran.
The wrapper also records a surface manifest count, size, and SHA-256 for the
runtime control/readiness source files and unit specs that define the local
serve-readiness path; the aggregate forwards those fields in
`llm_goal_evidence_vllm_host_detail`.
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
Configured native hosts provide those native capability results through
`SVLLM_NATIVE_READ_RANGE_STATUS`, `SVLLM_NATIVE_PINNED_BUFFER_STATUS`, and
`SVLLM_NATIVE_DEVICE_STAGING_STATUS`. Values normalize to `ready`,
`unsupported`, `unavailable`, or `unchecked`; omitted values default to
`unsupported`. The native streaming report records
`svllm_native_streaming_capability_source` and
`svllm_native_streaming_capability_provenance_status` so reviewers can
distinguish an explicit host probe from the default fallback. A strict native
PASS requires `SVLLM_NATIVE_CAPABILITY_SOURCE` to name the probe or artifact
that proved the ready native capabilities and
`SVLLM_NATIVE_CAPABILITY_EVIDENCE_PATH` to point at a non-empty probe artifact.
It also writes `svllm_native_streaming_pass_integrity_status` and
`svllm_native_streaming_pass_integrity_reason`; PASS integrity requires local
readiness, all three native capability statuses, provenance, and the evidence
artifact to be present together. The artifact is a line-oriented schema-v1 env
file with `svllm_native_capability_probe_event=svllm_native_capability_probe`,
`svllm_native_capability_probe_status=pass`,
`svllm_native_capability_probe_exit=0`, and reported read-range, pinned-buffer,
and device-staging statuses that match the wrapper inputs. The wrapper records
the artifact SHA-256, size, mtime, schema version, probe event/status/exit, and
reported native statuses.

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
`torch_cuda_optimizer_probe_python_torch_module_status`,
`torch_cuda_optimizer_probe_python_torch_version`,
`torch_cuda_optimizer_probe_python_torch_cuda_available`,
`torch_cuda_optimizer_probe_python_torch_cuda_device_count`,
`torch_cuda_optimizer_probe_system_libtorch_status`,
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
integrity, the hashed Torch optimizer source/spec surface, and the next
operator step. A probe `status=pass` is accepted only
when the wrapper also sees a zero wrapper exit, a non-empty hashed probe log,
exactly one complete proof record for status, required gates, libtorch/CUDA
availability, CUDA parameter placement, gradient handle, optimizer step, and
before/after sums, plus normalized libtorch/CUDA availability, CUDA parameter
placement, a nonzero gradient handle, an attempted optimizer step, and numeric
`after_sum < before_sum`. Use this wrapper as the
canonical evidence path for the real CUDA optimizer-step gate; run it with
`--strict` when unavailable hosts must fail the lane instead of recording a
warning.

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
response hashes, and the live dashboard next action,
`llm_goal_evidence_vllm_host_detail` for local
vLLM/GPU/preflight/endpoint/model statuses and pass-log integrity, and
`llm_goal_evidence_svllm_local_detail` for native svLLM streaming status,
native blocker reason, local readiness, native `read_range`, pinned-buffer,
device-staging, capability source, capability provenance, capability evidence
artifact status and hash metadata, probe event/status/exit, pass integrity,
local file-backed byte-read states, native blocked gates, primary blocked gate,
and next action.
In default mode, the
dashboard detail keeps a concrete strict-host next action even though live HTTP
evidence is intentionally not collected, and the svLLM native fields report
`not_required` / `not_collected`; strict host mode
generates and consumes the native streaming evidence. The svLLM blocker table
is mode-aware too: default mode reports the `local_readiness` gate with no
blocked native gates, while strict host mode reports the native producer's
`blocked_gates` and `next_action` contract. It
also records
`llm_goal_evidence_torch_optimizer_detail` for Simple/libtorch CUDA optimizer
status, compact blocked gates, primary blocked gate, Python Torch/CUDA host
visibility, system libtorch visibility, Simple runtime gates, gradient handle,
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
`llm_finetune_acceptance_upstream_attempt_record`,
`llm_finetune_acceptance_upstream_attempt_record_artifact_status`,
`llm_finetune_acceptance_upstream_attempt_record_sha256`,
`llm_finetune_acceptance_upstream_cache_manifest`,
`llm_finetune_acceptance_upstream_cache_manifest_artifact_status`,
`llm_finetune_acceptance_upstream_cache_manifest_sha256`,
`llm_finetune_acceptance_attempt_record`,
`llm_finetune_acceptance_model_manifest`,
`llm_finetune_acceptance_model_manifest_exists`,
`llm_finetune_acceptance_model_manifest_artifact_status`,
`llm_finetune_acceptance_model_manifest_sha256`,
`llm_finetune_acceptance_model_manifest_schema_version`,
`llm_finetune_acceptance_model_manifest_attempt_id`,
`llm_finetune_acceptance_base_model`,
`llm_finetune_acceptance_base_model_revision`,
`llm_finetune_acceptance_model_artifact_status`,
`llm_finetune_acceptance_model_manifest_deployable`,
`llm_finetune_acceptance_eval_result`,
`llm_finetune_acceptance_eval_result_exists`,
`llm_finetune_acceptance_eval_result_artifact_status`,
`llm_finetune_acceptance_eval_result_sha256`,
`llm_finetune_acceptance_eval_result_schema_version`,
`llm_finetune_acceptance_eval_result_status`,
`llm_finetune_acceptance_eval_metric_name`,
`llm_finetune_acceptance_eval_metric_value`,
`llm_finetune_acceptance_eval_dataset_id`,
`llm_finetune_acceptance_eval_dataset_checksum`,
`llm_finetune_acceptance_required_accuracy`,
`llm_finetune_acceptance_retry6_next_action`,
`llm_finetune_acceptance_decision_status`,
`llm_finetune_acceptance_handoff_doc`,
`llm_finetune_acceptance_handoff_doc_artifact_status`,
`llm_finetune_acceptance_handoff_doc_sha256`,
`llm_finetune_acceptance_pass_integrity_status`, and
`llm_finetune_acceptance_next_action` so strict aggregate runs can report the
first concrete blocker, the exact upstream artifact refs to fill, and the
model/eval/license/safety/deployment/app-handoff blocker list. The gate-log and
upstream retry5 hashes make a blocked acceptance report traceable to the exact
normal-review gate output and cache/attempt artifacts it consumed.
The wrapper passes only when retry7 reports `acceptance_allowed=true` and the
normalized `llm_finetune_acceptance_blocked_gates` value is `none`, and
`llm_finetune_acceptance_pass_integrity_status=pass` after hashing local
attempt, model manifest, eval result, and handoff artifacts and extracting
schema/linkage fields. A retry7 PASS line cannot override missing model, eval,
license, safety, deployment, handoff, or artifact-integrity evidence.

The local fine-tune guard evidence writes its own current blocker contract to
`build/llm_finetune_guard_evidence/evidence.env`. Default aggregate mode uses
that guard env for fine-tune required gates, blocked gates, blocker reason, and
next action; strict host mode still uses the acceptance env generated during
the strict run. The guard env also records a manifest count, size, and SHA-256
for the fixed-format data file, retry6/retry7 gate scripts, retry6/retry7 SSpec
files, and produced guard/spec logs, plus per-log sizes and SHA-256 values.
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
failure.
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
dashboard primary blocked gate, svLLM native streaming subfields, Torch
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

The strict native gate requires the evidence env to report
`svllm_native_streaming_status=pass`; local file-backed bytes are recorded as
bring-up evidence but are not enough for native streaming completion. Ready
native capability env values without a non-default
`SVLLM_NATIVE_CAPABILITY_SOURCE` fail as `capability_provenance`, and ready
values without a non-empty `SVLLM_NATIVE_CAPABILITY_EVIDENCE_PATH` fail as
`capability_evidence`. Strict local readiness requires both
`svllm_native_streaming_status=pass` and
`svllm_native_streaming_pass_integrity_status=pass`, so a status-only native env
cannot satisfy strict completion.

Use the focused Torch optimizer gate after changing Torch SFFI, CUDA placement,
or runtime training behavior:

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
aggregate evidence still agree on open strict blockers and the hardened
vLLM/Torch manifest hashes. It reads the aggregate Markdown report when present
and falls back to `build/llm_goal_evidence/evidence.env` while that report is
being regenerated. It is a drift check, not strict-host completion evidence.

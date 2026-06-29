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
`llm_runtime_vllm_host_probe_local_vllm_status`,
`llm_runtime_vllm_host_probe_local_gpu_status`,
`llm_runtime_vllm_host_probe_readiness_status`,
`llm_runtime_vllm_host_probe_preflight_status`,
`llm_runtime_vllm_host_probe_endpoint_status`, and
`llm_runtime_vllm_host_probe_models_status` so strict aggregate runs can report
the exact local serving blocker. Keep `FR-LLM-RUNTIME-0001` open until a
configured local endpoint reaches `status=ready`, `endpoint=configured`, and
`models_status=ready` after `/v1/models` serves the selected base model.
If a host is missing GPU tooling too, `local_gpu` is added to the blocked-gates
list independently of the collapsed control-CLI reason.
Run the wrapper with `--strict` when unavailable or readiness-incomplete hosts must
fail the lane.

Latest svLLM local readiness evidence:
`doc/09_report/2026/06/llm_runtime_svllm_local_readiness_2026-06-29.md`
records `scripts/check/check-llm-runtime-svllm-local-readiness.shs` passing the
pack CLI, manifest, tensor-byte, stream-plan, std_fs local-read, and
streaming-readiness contracts with per-spec timeout handling through
`SVLLM_READINESS_SPEC_TIMEOUT_SECONDS` (default `120`). Keep
`FR-LLM-RUNTIME-0002` open because that wrapper proves only local file-backed
readiness; native NVFS async scheduling, pinned buffer registration, device
staging, and true streaming model loads still need live evidence. Run
`scripts/check/check-llm-runtime-svllm-native-streaming-evidence.shs` to produce
the native evidence env. It records concrete blockers such as
`native_read_range_unavailable` and only passes when native read_range, pinned
buffer registration, and device staging are all ready. Native evidence records
`svllm_native_streaming_local_spec_timeout_seconds` so nested local-readiness
timeouts remain visible when strict aggregate evidence is collected.

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
`torch_cuda_optimizer_probe_torch_available_normalized`,
`torch_cuda_optimizer_probe_cuda_available_normalized`,
`torch_cuda_optimizer_probe_parameter_is_cuda_normalized`,
`torch_cuda_optimizer_probe_grad_handle_normalized`, and
`torch_cuda_optimizer_probe_optimizer_step_attempted_normalized` so strict
aggregate runs can report the exact blocked Torch gate. Use this wrapper as the
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
guard-only pass in default mode. The aggregate env also records
`llm_goal_evidence_context_ponytail_detail` for mimic/full-replacement state,
`llm_goal_evidence_dashboard_detail` for dashboard live-readiness state,
`llm_goal_evidence_vllm_host_detail` for local
vLLM/GPU/preflight/endpoint/model statuses, and
`llm_goal_evidence_svllm_local_detail` for native svLLM streaming status,
native blocker reason, local readiness, native `read_range`, pinned-buffer,
device-staging, and local file-backed byte-read states. In default mode, the
native fields report `not_required` / `not_collected`; strict host mode
generates and consumes the native streaming evidence. The svLLM blocker table
is mode-aware too: default mode reports the `local_readiness` gate with no
blocked native gates, while strict host mode reports
`native_read_range,pinned_buffer,device_staging` and their exact blockers. It
also records
`llm_goal_evidence_torch_optimizer_detail` for Simple/libtorch CUDA optimizer
status, host/runtime gates, gradient handle, optimizer-step attempt, and
before/after parameter sums. It also records
`llm_goal_evidence_finetune_guard_detail` for acceptance status, reason, gate
exit/status, compact blocked gates, training/model/eval readiness, license,
safety, deployment, app handoff, decision status, and next action. Those detail
fields are diagnostic only; they do not relax the strict host gates.

Latest fine-tune acceptance evidence:
`doc/09_report/2026/06/llm_finetune_acceptance_2026-06-29.md` records
`scripts/check/check-llm-finetune-acceptance-evidence.shs` failing the retry7
normal acceptance gate with `reason=BLOCKED_RETRY6_NOT_READY`. The evidence env
records `llm_finetune_acceptance_required_gates`,
`llm_finetune_acceptance_blocked_gates`,
`llm_finetune_acceptance_training_allowed`,
`llm_finetune_acceptance_model_manifest_exists`,
`llm_finetune_acceptance_eval_result_exists`,
`llm_finetune_acceptance_decision_status`,
`llm_finetune_acceptance_handoff_doc`, and
`llm_finetune_acceptance_next_action` so strict aggregate runs can report the
exact model/eval/license/safety/deployment/app-handoff blockers.

On a configured host, use strict host mode when the aggregate must be
release-completion evidence for the live gates:

```bash
sh scripts/check/check-llm-goal-evidence.shs --strict-host
```

Strict host mode first generates repo-local context/Ponytail full-replacement
evidence, authenticated dashboard route evidence, and fine-tune retry7
acceptance evidence, then passes the focused strict flags to the
context/Ponytail, dashboard, vLLM, svLLM, Torch optimizer, and fine-tune
wrappers. It clears each strict producer's canonical `evidence.env` before the
producer runs so stale results cannot mask a timeout or early producer failure.
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
`llm_goal_evidence_<lane>_blocker_reason` for the vLLM, svLLM, Torch optimizer,
and fine-tune lanes so operators can triage strict failures from the aggregate
report without opening every focused env first. The detail table also includes
svLLM native streaming subfields, Torch optimizer subfields, and fine-tune
acceptance subfields needed to distinguish missing native streaming support, a
missing host runtime, a failed optimizer step, and a blocked retry/eval gate
from a licensing, safety, deployment, or app-handoff blocker.

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
bring-up evidence but are not enough for native streaming completion.

Use the focused Torch optimizer gate after changing Torch SFFI, CUDA placement,
or runtime training behavior:

```bash
sh scripts/check/check-llm-runtime-torch-cuda-optimizer-probe.shs
```

Before final handoff for runtime-adjacent changes, also run the direct
environment/runtime guards for working and staged content.

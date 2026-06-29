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
`doc/09_report/2026/06/llm_runtime_vllm_host_probe_2026-06-28.md` records a
repeatable `scripts/check/check-llm-runtime-vllm-host-probe.shs` preflight. On
the current host it returns `status=unavailable` with
`reason=missing_local_vllm`. Keep `FR-LLM-RUNTIME-0001` open until a configured
local endpoint proves `/v1/models` serves the selected base model. Run the
wrapper with `--strict` when unavailable or preflight-only hosts must fail the
lane.

Latest svLLM local readiness evidence:
`doc/09_report/2026/06/llm_runtime_svllm_local_readiness_2026-06-28.md`
records `scripts/check/check-llm-runtime-svllm-local-readiness.shs` passing the
pack CLI, manifest, tensor-byte, stream-plan, std_fs local-read, and
streaming-readiness contracts. Keep `FR-LLM-RUNTIME-0002` open because that
wrapper proves only local file-backed readiness; native NVFS async scheduling,
pinned buffer registration, device staging, and true streaming model loads
still need live evidence. Run
`scripts/check/check-llm-runtime-svllm-native-streaming-evidence.shs` to produce
the native evidence env. It records concrete blockers such as
`native_read_range_unavailable` and only passes when native read_range, pinned
buffer registration, and device staging are all ready.

Latest Torch/CUDA host probe:
`doc/09_report/2026/06/llm_runtime_torch_cuda_host_probe_2026-06-28.md`
records Python Torch `2.9.1+cu130` with CUDA available and visible NVIDIA GPUs,
plus a passing Simple dynamic Torch SFFI readiness spec. Keep
`FR-LLM-RUNTIME-0003` open until Simple/libtorch executes and records a real
CUDA optimizer step.

Latest Simple/libtorch optimizer probe:
`doc/09_report/2026/06/llm_runtime_torch_cuda_optimizer_probe_2026-06-28.md`
records `scripts/check/check-llm-runtime-torch-cuda-optimizer-probe.shs`
classifying the self-hosted Simple runtime as `unavailable` with
`reason=libtorch_unavailable`. Use this wrapper as the canonical evidence path
for the real CUDA optimizer-step gate; run it with `--strict` when unavailable
hosts must fail the lane instead of recording a warning.

## Focused Checks

Use the aggregate local LLM evidence wrapper when checking the current
context/Ponytail, dashboard, vLLM, svLLM, Torch, fine-tune, and public-absence
lanes together:

```bash
sh scripts/check/check-llm-goal-evidence.shs
```

The aggregate report is written to
`doc/09_report/2026/06/llm_goal_evidence_2026-06-28.md`. It treats live vLLM
and Simple/libtorch CUDA optimizer host gaps as expected WARN lanes on hosts
where those dependencies are not installed.

On a configured host, use strict host mode when the aggregate must be
release-completion evidence for the live gates:

```bash
sh scripts/check/check-llm-goal-evidence.shs --strict-host
```

Strict host mode first generates repo-local context/Ponytail full-replacement
evidence, authenticated dashboard route evidence, and fine-tune retry7
acceptance evidence, then passes the focused strict flags to the
context/Ponytail, dashboard, vLLM, svLLM, Torch optimizer, and fine-tune
wrappers. The aggregate expects all completion lanes to pass, fails for any WARN
or missing strict evidence result, and writes `llm_goal_evidence_failed_gates`,
`llm_goal_evidence_failed_gate_hints`, `llm_goal_evidence_warn_gates`, and
per-lane `llm_goal_evidence_<lane>_hint` values to the env file for direct
triage.

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

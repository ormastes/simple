# LLM Strict Host Completion Blockers

Status: OPEN

## Summary

Default LLM evidence is reproducible, but strict-host completion still fails on
five live/runtime/model gates. This tracker is the durable owner for the
remaining blockers recorded in
`doc/09_report/2026/06/llm_goal_strict_completion_audit_2026-06-29.md`.

## Evidence

Default aggregate:

- `STATUS: PASS llm-goal-evidence warn_count=2`
- `warn_gates=vllm_host|torch_optimizer`
- local provenance hardening: context/Ponytail replacement, dashboard route,
  vLLM host, svLLM local readiness, Torch optimizer, and fine-tune guard
  evidence now include checked surface/input manifests with size/SHA-256
  metadata and focused log hashes.

Strict-host aggregate:

- `STATUS: FAIL llm-goal-evidence warn_count=0 fail_count=5`
- `failed_gates=dashboard|vllm_host|svllm_local|torch_optimizer|finetune_guard`

## Blockers

### Dashboard Live HTTP

- primary blocker: `live_http_authenticated_request`
- concrete reason: `missing_base_url`
- local proof already hardened: dashboard route/source/spec evidence has a
  manifest and nested dashboard env/log hashes
- required evidence: `llm_dashboard_live_http_status=pass`
- next action: set `LLM_DASHBOARD_LIVE_BASE_URL` plus dashboard authentication
  env and rerun `scripts/check/check-llm-dashboard-live-http-evidence.shs`.

### vLLM Host

- primary blocker: `local_vllm`
- current evidence: `vllm_command_path=missing`,
  `python_vllm_module_status=missing`, `local_gpu_status=available`
- local proof already hardened: vLLM host evidence has a checked runtime
  control/readiness source/spec manifest with
  `surface_manifest_count=10` and
  `surface_manifest_sha256=83abdc5c0a155eb8bc2cd2c20e3a9349d0e5b43cacf1073c5d59706b5fe9500b`
- required evidence: local `vllm` executable, serve preflight, reachable
  endpoint, and `/v1/models` listing the selected base model
- next action: install or expose local vLLM, then rerun
  `scripts/check/check-llm-runtime-vllm-host-probe.shs --strict`.

### svLLM Native Streaming

- primary blocker: `native_read_range`
- current evidence: local readiness passes, local file-backed byte reads are
  ready, but native `read_range`, pinned-buffer registration, and device
  staging are `unsupported`
- local proof already hardened: svLLM local readiness has a checked spec/log
  manifest and per-log hashes
- required evidence: `svllm_native_streaming_status=pass`
- next action: implement native streaming capability evidence and rerun
  `scripts/check/check-llm-runtime-svllm-native-streaming-evidence.shs` with
  `SVLLM_NATIVE_CAPABILITY_SOURCE` and a non-empty
  schema-v1 `SVLLM_NATIVE_CAPABILITY_EVIDENCE_PATH` from the native probe
  artifact; the artifact must report probe event/status/exit and native
  capability statuses matching the wrapper inputs.

### Torch Optimizer

- primary blocker: `libtorch`
- current evidence: Python Torch `2.9.1+cu130` has CUDA available with 2
  devices; system/Simple-visible libtorch is missing
- local proof already hardened: Torch optimizer evidence has a checked live
  probe/source/spec manifest with `surface_manifest_count=14` and
  `surface_manifest_sha256=852a1c814199286c0cf686f2bc68ffc8fb946a85691426a4c7440cf69aa7165c`
- required evidence: Simple/libtorch CUDA optimizer probe with parameter on
  CUDA, gradient handle, optimizer step attempted, and parameter sum decrease
- next action: build or install Simple-visible libtorch and rerun
  `scripts/check/check-llm-runtime-torch-cuda-optimizer-probe.shs --strict`.

### Fine-Tune Acceptance

- primary blocker: `retry6_training_eval`
- current evidence: retry7 acceptance is blocked; retry5 licensed cache review,
  retry6 model manifest, eval result, target eval, license, safety,
  deployment, app handoff, and accepted decision are not ready
- local proof already hardened: fine-tune guard evidence has a checked
  process/input/log manifest and per-log hashes
- required evidence: `llm_finetune_acceptance_status=pass`
- next action: complete retry5 licensed cache/checksum review, run retry6
  training/eval to target, then record retry7 normal acceptance evidence with
  `llm_finetune_acceptance_pass_integrity_status=pass` from local attempt,
  model manifest, eval result, and handoff artifact hashing plus schema/linkage
  extraction.

## Done Criteria

This tracker can close only when:

- `sh scripts/check/check-llm-goal-evidence.shs --strict-host` reports
  `STATUS: PASS`
- strict `failed_gates` is empty
- the strict report shows context/Ponytail replacement, dashboard, vLLM, svLLM,
  Torch optimizer, and fine-tune lanes all passing

# Architecture: LLM Runtime vLLM/Torch Interface

Date: 2026-06-25

## Pattern

Use an external-runtime boundary. Simple owns manifests, probes, evidence, and
dashboard rendering. vLLM owns model serving. PyTorch/Torch SFFI owns tensor and
training primitives only when a later lane explicitly enters training.

## Layers

1. Manifest layer:
   - base model id
   - serving endpoint
   - optional chat template path
   - optional LoRA adapter list
   - dynamic LoRA trust mode
2. Probe layer:
   - file/static validation
   - endpoint readiness summaries from planned or observed transport evidence
   - Torch/SFFI readiness as a separate capability check
3. Serve-plan layer:
   - sanitized vLLM command metadata
   - static LoRA adapter counts without paths
   - invalid endpoint and malformed adapter-entry reporting
4. Evidence layer:
   - SPipe JSONL events
   - internal-marker-free status/reason fields
   - dashboard diagnostics consumption
5. Runtime control layer:
   - live request planning for `/v1/models` and `/v1/chat/completions`
   - HTTP transport through owner facades after planning succeeds
   - serve lifecycle and readiness orchestration through process/HTTP owner
     facades
6. UI/tool layer:
   - existing web dashboard diagnostics panel
   - dashboard vLLM control-intent panel for preflight/start/poll/probe/stop
   - runtime-owned `/api/vllm/control` execution JSONL for authenticated
     side-effect requests, with skipped/blocked evidence when local resources
     are missing

## Boundaries

- App/dashboard code must not add raw runtime shortcuts. Torch owner modules may
  add or standardize owner ABI externs when they are the SFFI boundary.
- Do not shell out from hot request handlers.
- Normal serving uses static vLLM startup LoRA only:
  `--enable-lora --lora-modules name=path`.
- Do not enable runtime LoRA loading by default; allow it only in an explicitly
  isolated trusted mode.
- Do not print secrets in generated commands or dashboard output.
- Sanitized command previews must use `--lora-modules` terminology and replace
  adapter paths with counts/redaction markers.
- Static serve plans are metadata only; they must not start vLLM, shell out, or
  probe HTTP. Live requests and process actions must pass through
  `src/app/llm_runtime` planner/executor facades before any transport or
  lifecycle side effect.
- Dashboard rendering may expose intent and owner-produced execution JSONL, but
  it must not import process or HTTP backends directly or treat planned controls
  as live endpoint proof.
- Absence is represented as option-like text such as `none`, `missing`, or an
  omitted field, never the runtime's internal marker.

## MDSOC Ownership

- `src/app/llm_runtime` should own manifests and probes if implemented.
- Dashboard modules should render collected evidence and control intent. They
  must not import live HTTP/process backends for ordinary page rendering; live
  execution remains behind `src/app/llm_runtime` owner facades.
- SPipe specs should assert behavior through public probe/evidence outputs.
- Torch/SFFI owner modules must provide ABI/loader readiness; app probes should
  consume that evidence instead of reaching around owner boundaries.

## 2026-07-01 Continuation MDSOC Notes

<!-- codex-design -->

- CLI provider capsule: `src/app/llm_caret` owns Claude/OpenCode style
  argument construction, response classification, and pid kill evidence. It may
  use `app.io.mod` process facades, but must not add local raw
  `rt_process_*` externs.
- Runtime serving capsule: `src/app/llm_runtime` owns backend-neutral manifest
  fields and sanitized serve-plan JSONL. vLLM remains the default backend;
  SGLang support starts as backend metadata and command-preview planning only.
- Cross-cutting kill behavior: pid validation and process kill evidence belongs
  at the provider/runtime owner boundary. Dashboard or UI layers can render the
  evidence, but must not kill by process name or shell command.
- SGLang-derived knobs (`backend`, tensor/data parallel sizing, memory fraction)
  are feature-transform metadata over the existing serve plan, not a separate
  serving subsystem.

## Deferred

- PEFT/TRL training orchestration.
- End-to-end proof against an installed local vLLM server and GPU-backed
  endpoint.
- Host-proven dashboard start/probe/stop execution against a real local vLLM
  process. The runtime-owned execution boundary exists, but live availability
  evidence remains host-dependent.
- Dynamic adapter resolver plugins.
- GPU memory accounting beyond optional readback.
- Full svLLM native streaming through NVFS scheduling, pinned-buffer
  registration, and device staging.

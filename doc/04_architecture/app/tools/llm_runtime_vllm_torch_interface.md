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
   - endpoint readiness when available
   - Torch/SFFI readiness as a separate capability check
3. Serve-plan layer:
   - sanitized vLLM command metadata
   - static LoRA adapter counts without paths
   - invalid endpoint and malformed adapter-entry reporting
4. Evidence layer:
   - SPipe JSONL events
   - nil-free status/reason fields
   - dashboard diagnostics consumption
5. UI/tool layer:
   - existing web dashboard diagnostics panel
   - future MCP/tool exposure

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
  probe HTTP.
- Absence is represented as option-like text such as `none`, `missing`, or an
  omitted field, never literal `nil`.

## MDSOC Ownership

- `src/app/llm_runtime` should own manifests and probes if implemented.
- Dashboard modules should only render collected evidence.
- SPipe specs should assert behavior through public probe/evidence outputs.
- Torch/SFFI owner modules must provide ABI/loader readiness; app probes should
  consume that evidence instead of reaching around owner boundaries.

## Deferred

- PEFT/TRL training orchestration.
- vLLM process supervisor.
- Dynamic adapter resolver plugins.
- GPU memory accounting beyond optional readback.
- Custom serving engine work in this lane; keep svLLM product work separate
  unless explicitly selected.

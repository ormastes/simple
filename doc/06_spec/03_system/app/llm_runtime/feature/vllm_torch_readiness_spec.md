# Spec: vLLM Torch Readiness Bridge

Source: `test/03_system/app/llm_runtime/feature/vllm_torch_readiness_spec.spl`

## Behavior

- A local Option A manifest can produce absence-safe vLLM readiness JSONL without
  requiring vLLM, PyTorch, CUDA, or a GPU.
- The JSONL event is consumable by the existing LLM dashboard diagnostics
  collector.
- The public probe is conservative while Torch/svLLM readiness is still a known
  placeholder: it reports `blocked`, never `ready`.
- Missing optional chat template state renders as `none`.
- Dynamic LoRA requests that are not explicitly trusted are blocked.
- Path-like local model identifiers are redacted from evidence.
- The local probe/readback path is checked under the 2 second Option A NFR.
- A static vLLM serve-plan event can be generated without starting vLLM or
  probing HTTP; its command preview redacts model path-like labels and
  credentials, and unit coverage proves LoRA adapter paths are omitted.
- Malformed adapter entries and invalid endpoint strings are surfaced as
  explicit option-like reasons, not hidden as successful partial metadata.

## Covered Requirements

- System coverage: REQ-003, REQ-004, REQ-005, REQ-006, REQ-007, NFR-001,
  NFR-002, NFR-003, NFR-004, NFR-005, and NFR-006.
- Unit coverage in `test/01_unit/app/llm_runtime/vllm_readiness_spec.spl` and
  `test/unit/app/llm_runtime/vllm_readiness_spec.spl` also covers REQ-001 and
  REQ-002 manifest/static validation details.

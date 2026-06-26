# Requirements: LLM Runtime vLLM/Torch Interface

Date: 2026-06-25

Selected option: Option A, vLLM Readiness Bridge.

Selection source: user requested the first implementation option.

## Final Requirements

- REQ-001: The runtime lane shall provide a local manifest shape for a vLLM
  serving target with base model, endpoint, optional chat template, optional
  static LoRA adapters, and dynamic LoRA trust mode.
- REQ-002: The readiness probe shall validate required manifest fields without
  starting or supervising a vLLM process.
- REQ-003: Optional absence shall render as option-like text such as `none`,
  `missing`, `blocked`, or `unchecked`, never literal `nil`.
- REQ-004: Dynamic LoRA loading shall be reported as `blocked` unless the
  manifest explicitly marks the mode as `trusted`.
- REQ-005: The probe shall emit one structured JSONL evidence event consumable
  by SPipe/dashboard diagnostics.
- REQ-006: Evidence shall not expose prompts, tool payloads, credentials, API
  keys, or secret file paths.
- REQ-007: Known Torch/SFFI or svLLM placeholder readiness shall be represented
  as `blocked`, not normalized into `ready`.

## Deferred

- Starting or supervising a vLLM server.
- Live `/v1/models` or `/v1/chat/completions` probing.
- Dynamic LoRA adapter resolver plugins.
- PEFT/TRL fine-tuning orchestration.

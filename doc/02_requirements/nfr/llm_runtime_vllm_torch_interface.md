# NFR Requirements: LLM Runtime vLLM/Torch Interface

Date: 2026-06-25

Selected option: Option A, Local Evidence NFRs.

Selection source: user requested the first implementation option.

## Final Targets

- NFR-001: Public manifest/probe/evidence output shall not contain literal
  `nil`.
- NFR-002: Static readiness checks and mocked local evidence generation shall
  complete in under 2 seconds.
- NFR-003: Dynamic LoRA loading shall be disabled or blocked by default.
- NFR-004: Each probe shall emit one structured JSONL event with status, reason,
  and option-like missing fields.
- NFR-005: Evidence shall redact or omit prompts, tool payloads, API keys,
  credentials, and secret paths by default.
- NFR-006: The first slice shall compile and run without GPU, PyTorch, vLLM, or
  CUDA availability.

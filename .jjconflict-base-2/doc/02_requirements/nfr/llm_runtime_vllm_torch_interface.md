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
- NFR-007: Live request planning, response parsing, dashboard control preflight,
  and skipped-resource evidence shall be deterministic under unit/system tests
  and shall not require a local vLLM server, GPU, PyTorch, or CUDA.
- NFR-008: Dashboard vLLM control output shall label intent-only,
  executor-required, skipped, blocked, and not-live-evidence states explicitly so
  operators cannot confuse planned controls with live endpoint proof.
- NFR-009: Process, HTTP, environment, and time access used by the vLLM control
  lane shall route through existing owner facades; new raw `rt_*` shortcuts are
  not acceptable for app/dashboard code.
- NFR-010: Torch/svLLM placeholder hardening shall fail closed with explicit
  unavailable or unsupported status strings and remain usable in clean
  workspaces that lack libtorch, CUDA, vLLM, and NVFS native streaming support.
- NFR-011: CLI-provider kill support shall use pid-scoped owner process facades,
  not shell `kill`, process-name matching, or raw `rt_process_*` shortcuts in
  app provider modules.
- NFR-012: SGLang-derived serve metadata shall be plan/evidence only until a
  focused host proof verifies a live SGLang endpoint.

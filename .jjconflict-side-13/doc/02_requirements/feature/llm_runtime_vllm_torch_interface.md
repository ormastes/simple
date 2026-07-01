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
- REQ-008: Live vLLM request planning shall sanitize `/v1/models` and
  `/v1/chat/completions` metadata before any transport call, reject invalid
  endpoints, and block unsupported chat parameters at the planner boundary.
- REQ-009: Live vLLM response parsing shall distinguish ready, auth rejection,
  malformed response, wrong-model, empty-choice, and missing-assistant-content
  states without exposing generated content or private model paths.
- REQ-010: vLLM serve lifecycle and dashboard control evidence shall keep
  process and HTTP side effects behind `app.llm_runtime` owner facades. Dashboard
  rendering may expose intent, preflight, skipped, blocked, and executor-required
  JSONL, but shall not treat planned controls as live serving proof.
- REQ-011: Local vLLM/GPU resource detection shall be bounded and optional.
  Missing resources must produce explicit `skipped` or `blocked` evidence before
  spawn/fetch behavior is attempted.
- REQ-012: Torch/svLLM owner-module readiness shall expose explicit unavailable
  or unsupported statuses for placeholder or host-missing capabilities, including
  dynamic Torch SFFI tensor operations and svLLM streaming readiness.
- REQ-013: The LLM Caret provider surface shall support an OpenCode CLI backend
  shaped like the Claude CLI wrapper: deterministic argument construction,
  JSON/raw response classification, provider registration, and no subprocess
  calls in unit-only helper tests.
- REQ-014: Claude-like CLI providers that can spawn long-running agent work
  shall expose pid-based kill evidence through the owner process facade, with
  invalid pids rejected before any signal is attempted.
- REQ-015: The runtime serve manifest and serve-plan evidence shall keep vLLM as
  the default backend while allowing SGLang-derived backend metadata for
  `sglang`, tensor/data parallel sizing, and static memory-fraction intent.

## Deferred

- End-to-end proof against an installed local vLLM server and GPU.
- Live dashboard control execution that proves a real local vLLM process starts,
  serves `/v1/models`, serves `/v1/chat/completions`, and stops cleanly on this
  host.
- Dynamic LoRA adapter resolver plugins.
- PEFT/TRL fine-tuning orchestration.
- Full svLLM streaming through native NVFS scheduling, pinned-buffer
  registration, and device staging.
- Live CUDA optimizer execution against a local libtorch/CUDA installation.
- Full OpenCode server attach/session management beyond non-interactive
  `opencode run` and pid kill evidence.
- Host-proven SGLang serving and OpenAI-compatible endpoint parity.

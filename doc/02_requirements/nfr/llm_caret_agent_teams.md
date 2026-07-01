# LLM Caret Agent Teams - NFR Requirements

Date: 2026-07-01

- NFR-001: Default verification must run as unit-level pure tests only.
- NFR-002: Generated prompts must be deterministic for the same inputs.
- NFR-003: The planner must not read environment variables, shell out, scan the filesystem, or import raw `rt_*` intrinsics.
- NFR-004: The public surface must remain small enough to review in one module.

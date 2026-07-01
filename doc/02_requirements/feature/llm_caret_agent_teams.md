# LLM Caret Agent Teams - Feature Requirements

Date: 2026-07-01

- REQ-001: Provide a pure single-agent launch planner from provider, agent markdown path, skill path, task description, model, session id, and extra args.
- REQ-002: Provide a pure team launch planner that combines multiple single-agent launch requests and records an interaction mode.
- REQ-003: Provide a pure low-agent review planner that includes tracked changed files, including per-agent change sets and review guidance.
- REQ-004: Provide pure Claude advisor and Codex goal planners that encode the requested advisor/goal text without live subprocess execution.
- REQ-005: Keep the API testable without Claude, Codex, OpenCode, network, or a live process registry.

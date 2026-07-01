# LLM Caret Agent Teams - Feature Requirements

Date: 2026-07-01

- REQ-001: Provide a pure single-agent launch planner from provider, agent markdown path, skill path, task description, model, session id, and extra args.
- REQ-002: Provide a pure team launch planner that combines multiple single-agent launch requests and records an interaction mode.
- REQ-003: Provide a pure low-agent review planner that includes tracked changed files, including per-agent change sets and review guidance.
- REQ-004: Provide pure Claude advisor and Codex goal planners that encode the requested advisor/goal text without live subprocess execution.
- REQ-005: Keep the API testable without Claude, Codex, OpenCode, network, or a live process registry.
- REQ-006: Provide explicit agent, skill, MCP server, and plugin capability lists so plans can mirror SPipe-style agent/skill/tool handoffs.
- REQ-007: Provide a deterministic team interaction transcript planner with explicit `btw` and `side` message channels.
- REQ-008: Provide a small filesystem snapshot helper that records existing file hashes per agent through the app I/O facade.

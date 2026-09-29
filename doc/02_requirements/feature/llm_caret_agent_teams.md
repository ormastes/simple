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
- REQ-009: Provide a minimal team launcher that starts a list of single-agent requests and returns per-agent process records without persisting a supervisor.
- REQ-010: Provide a VCS changed-file discovery helper that defaults to `jj diff --name-only` and returns per-agent changed-file records.
- REQ-011: Provide simple MCP/plugin manifest parsers and plugin install argument planning so agent handoffs can be populated consistently with SPipe without performing live installs.
- REQ-012: Provide a pure team mailbox for `btw` and `side` messages with per-agent inbox and channel filtering.
- REQ-013: Provide a TUI-readable handoff surface and executable SSpec system test for agent, skill, MCP, plugin, and team-message visibility.

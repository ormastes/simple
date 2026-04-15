# MCP Performance Regression Skill Update Plan

Date: 2026-03-30

## Purpose

Align Codex, Claude, and Gemini so design, implementation, and verification all catch MCP and LSP performance regressions early.

## Shared Rule Vocabulary

- startup-path review
- hot request path review
- cache or index strategy
- invalidation strategy
- realistic fixture
- warm startup time
- representative request latency
- max RSS evidence

## File Targets

### Shared Docs

- `AGENTS.md`
- `CLAUDE.md`
- `GEMINI.md`

### Codex

- `.codex/skills/design/SKILL.md`
- `.codex/skills/impl/SKILL.md`
- `.codex/skills/verify/SKILL.md`

### Claude

- `.claude/skills/design.md`
- `.claude/skills/impl.md`
- `.claude/skills/verify.md`

### Gemini

- `.gemini/commands/design.toml`
- `.gemini/commands/impl.toml`
- `.gemini/commands/verify.toml`

## Rule Split By Stage

### Design

- review wrapper startup path
- identify scans, rereads, subprocesses, and retry loops in hot paths
- require cache/index and invalidation design when repeated scans are likely
- require startup, latency, and RSS budgets for performance-sensitive tooling

### Implementation

- wrappers use cached compiled artifacts for normal execution
- avoid repeated full-tree scans and per-request subprocesses in hot handlers
- add invalidation on writes for cached or indexed read paths
- run perf smoke checks before closing perf-sensitive work

### Verify

- fail source-entrypoint launchers in production wrappers
- audit repeated scans, rereads, subprocesses, and missing invalidation
- require timing and RSS evidence on realistic fixtures

## Review Checklist

- shared docs and skills use consistent terms
- no CLI stack is missing design, impl, or verify performance rules
- shared docs do not contradict launcher behavior or current MCP config

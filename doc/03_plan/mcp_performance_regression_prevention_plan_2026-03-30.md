# MCP Performance Regression Prevention Plan

Date: 2026-03-30
Scope: `simple-mcp`, `t32-mcp`, `t32-lsp-mcp`, `obsidian-search`, `obsidian-lsp-mcp`

## Goal

Prevent startup, CPU, memory, and request-latency regressions in MCP and LSP-MCP servers by adding design rules, implementation constraints, runtime observability, lint checks, and verification gates.

## Problem Summary

- MCP wrappers can accidentally launch source entrypoints in production paths instead of cached compiled artifacts.
- Request handlers can accidentally perform full vault or workspace scans repeatedly.
- Hot request paths can shell out per request, multiplying latency and memory churn.
- Cache introduction without invalidation creates correctness drift.
- Existing verify rules focus on completeness and stubs, but not enough on hot-path performance hazards.

## Design Workstream

### Design Rules

- Production MCP wrappers must execute cached compiled artifacts, not source entrypoints.
- Request handlers must not perform full-tree scans unless the operation is explicitly a reindex, maintenance, or admin tool.
- Expensive derived data must live behind a cache or index with an explicit invalidation strategy.
- Per-request subprocess execution in hot paths must be avoided when an in-process alternative exists.
- Performance-sensitive features must define startup and request-latency budgets before implementation.

### Required Design Artifacts

- Architecture note for wrapper execution strategy and cache lifecycle.
- Detail design for scan cache, invalidation triggers, perf instrumentation, and lint coverage.
- Verification traceability from performance requirements to tests and checks.

## Program Workstream

### Phase 1: Wrapper Safety

- Standardize wrapper pattern for MCP/LSP-MCP launchers.
- Compile to cached `.smf` or equivalent artifact before execution.
- Add a shared launcher helper or documented launcher template.

### Phase 2: Hot-Path Caching

- Add core cache layers for repeated scan/read operations.
- Route high-frequency analytics and completion flows through the cache or index.
- Invalidate caches on write, move, delete, template application, rename, and bulk replace.

### Phase 3: Runtime Observability

- Add debug-only counters and timing for:
  - directory walks
  - file reads
  - subprocess count
  - request elapsed time
- Emit warnings when thresholds are exceeded.

### Phase 4: Static Prevention

- Add lint or analysis rules for:
  - source entrypoint execution in production wrappers
  - `scan_vault` or `rt_dir_walk` in request handlers
  - `rt_process_run("/bin/sh", ["-c", ...])` in hot paths
  - cache introduction without invalidation hooks in write flows

### Phase 5: Perf Test Coverage

- Add startup smoke tests for all MCP wrappers:
  - cold start
  - warm start
  - RSS ceiling
- Add request smoke tests for representative high-cost tools:
  - initialize
  - tools/list
  - completion
  - diagnostics
  - vault stats or equivalent analytics

## Verify Workstream

### Verification Gates

- Fail if a production wrapper launches a source entrypoint directly.
- Fail if a hot request path performs repeated full scans without caching or indexing.
- Warn or fail if a hot request path shells out per request without documented justification.
- Fail if cacheable derived data has no invalidation path after writes.
- Fail if performance-critical features have no perf smoke tests or budgets.

### Evidence Required

- Startup measurements captured for affected servers.
- Request-latency measurements for representative tools.
- Static scan output for hot-path rules.
- Design doc references for cache and invalidation strategy.

## Skill Rule Update Plan

### Codex

- Update `.codex/skills/design/SKILL.md`
- Update `.codex/skills/impl/SKILL.md`
- Update `.codex/skills/verify/SKILL.md`

### Claude

- Update `.claude/skills/design.md`
- Update `.claude/skills/impl.md`
- Update `.claude/skills/verify.md`

### Gemini

- Update `.gemini/commands/design.toml`
- Update `.gemini/commands/impl.toml`
- Update `.gemini/commands/verify.toml`

## Rule Additions by Skill Type

### Design

- Require explicit startup-path and hot-path review.
- Require cache/index/invalidation design for repeated scans.
- Require performance budgets and observability plan for performance-sensitive tools.

### Implementation

- Require cached compiled launcher pattern for production wrappers.
- Forbid full-tree scans in request handlers unless explicitly designed and documented.
- Require invalidation hooks when writes affect cached or indexed data.
- Require perf smoke tests for startup and representative requests.

### Verify

- Add wrapper-launch pattern audit.
- Add repeated-scan and per-request-subprocess audit.
- Add cache invalidation audit.
- Add perf smoke/budget audit.

## Deliverables

- Updated cross-LLM skill rules.
- Static prevention checks in code or linting.
- Perf smoke tests for startup and hot requests.
- Design and verification docs updated to treat performance regressions as release blockers where applicable.

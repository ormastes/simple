<!-- codex-research -->
# UI Access Protocol — NFR Options

**Date:** 2026-04-15
**Feature:** `ui_access_protocol`

## Option A — Balanced Internal Tooling Baseline

### Targets

- additive only over existing test/MCP surfaces
- bounded recent-event history in memory
- representative snapshot and find paths stay interactive for local use
- old widget/test routes remain compatible

### Pros

- realistic for current codebase
- enforces compatibility and low overhead

### Cons

- does not set aggressive perf targets for very large trees

### Effort

- **M**

## Option B — Performance-First Hard Targets

### Targets

- strict startup, latency, and RSS budgets for all access routes
- cache/invalidation metrics from day one
- broad benchmark coverage

### Pros

- stronger perf discipline

### Cons

- heavy verification overhead for a v1 internal-only feature

### Effort

- **L**

## Option C — Reliability and Audit Heavy

### Targets

- persisted history
- formal redaction policy
- stronger observability and audit logs

### Pros

- better enterprise-style traceability

### Cons

- overbuilds the first release

### Effort

- **L**

## Selected Option

**Chosen:** Option A, with explicit compatibility and bounded-history rules.

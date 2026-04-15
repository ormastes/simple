<!-- codex-design -->
# System Test Plan: KAIROS-Like Simple MCP + LLM Dashboard

Date: 2026-04-15

## Scope

Validate standalone `simple mcp`, standalone dashboard replay/import mode, and combined live mode for assistant sessions, ticks, signals, child tasks, digests, notifications, and degraded behavior.

## Test Groups

### Group 1: Standalone `simple mcp`

- create/list/pause/resume assistant sessions
- emit brief output
- process periodic ticks
- process pushed signals
- spawn and complete child tasks

### Group 2: Standalone Dashboard Replay/Import

- load persisted assistant snapshot
- render session overview
- render timeline and task tree
- render digests and notifications
- show disabled live controls

### Group 3: Combined Live Mode

- attach dashboard to live assistant state
- reflect delta updates
- route operator control actions through MCP
- preserve source-of-truth separation

### Group 4: Failure and Recovery

- child-task crash
- bridge disconnect
- notification route failure
- session restart after crash
- bursty signal backpressure/coalescing

## Traceability

- REQ-KAIROS-001 through REQ-KAIROS-012
- NFR-KAIROS-001 through NFR-KAIROS-015

## Exit Criteria

1. Every REQ has at least one system-level scenario.
2. Standalone and combined modes are separately validated.
3. Degraded-mode behavior is proven rather than implied.
4. Failure evidence remains visible after restart or disconnect.

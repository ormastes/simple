<!-- codex-research -->
# NFR Requirements: KAIROS-Like Simple MCP + LLM Dashboard

**Date:** 2026-04-15
**Selected Option:** 3 - Strong Multi-Session Operations Gate

## Performance Targets

### NFR-KAIROS-001 Warm MCP Control Latency

Warm `simple mcp` assistant session list/detail/brief operations shall complete in under 250 ms on representative local state.

### NFR-KAIROS-002 Tick Dispatch Latency

Tick dispatch shall classify wake reason, load session state, and reach an action/no-action decision in under 150 ms before any delegated work begins.

### NFR-KAIROS-003 Signal Persistence Latency

Signal ingestion to durable timeline/event state shall complete in under 100 ms for representative local payloads.

### NFR-KAIROS-004 Dashboard Live Refresh

Dashboard live refresh or delta application shall complete in under 500 ms for representative single-session updates and under 1 s for 10-session overview updates.

## Capacity and Retention

### NFR-KAIROS-005 Concurrent Session Support

The system shall support at least 10 concurrent assistant sessions in degraded but usable mode with bounded retention and readable multi-session dashboards.

### NFR-KAIROS-006 Retention Boundaries

The system shall define bounded retention and digest-compaction rules for transcripts, timelines, signals, and child-task records so storage growth is controlled.

### NFR-KAIROS-007 Burst Handling

The system shall define event coalescing and backpressure behavior for bursty external signal input and shall preserve dropped/coalesced evidence in structured counters or summaries.

## Reliability and Safety

### NFR-KAIROS-008 Worker Resource Policy

All proactive/background workers and child-agent tasks shall run with explicit timeout and memory policy, and those policies shall be visible in diagnostics.

### NFR-KAIROS-009 Recovery Evidence

Crash, timeout, disconnect, and restart paths shall preserve structured failure records sufficient to diagnose what failed, when, and under which session/task IDs.

### NFR-KAIROS-010 Degraded-Mode Operation

The system shall continue operating in documented degraded mode when:

- the dashboard bridge is absent
- the dashboard is disconnected
- a child-agent fails
- notification delivery fails

## Architecture and Hot-Path Constraints

### NFR-KAIROS-011 No Hidden Full-Store Hot Paths

Hot live-update paths shall not rely on repeated full-store rereads, repeated full-tree scans, or per-request subprocess spawning unless explicitly justified and measured.

### NFR-KAIROS-012 Source-of-Truth Separation

The dashboard shall not become the source of truth for assistant state; authoritative session control and persistence remain in the assistant core/control plane.

### NFR-KAIROS-013 Observability

The implementation shall expose timings, counters, and diagnostic state for:

- session operations
- tick decisions
- signal intake
- child-agent lifecycle
- bridge freshness/staleness
- notification delivery

## Verification Targets

### NFR-KAIROS-014 Startup and RSS Reporting

The implementation shall report startup and max RSS targets for the assistant core, live bridge, and representative child-agent workloads on realistic fixtures.

### NFR-KAIROS-015 Multi-Mode Test Coverage

Verification shall cover standalone `simple mcp`, standalone dashboard replay/import mode, and combined live mode, including degraded/failure paths.

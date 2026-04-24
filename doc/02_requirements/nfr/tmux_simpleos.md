<!-- codex-research -->
# NFR Requirements — `tmux_simpleos`

Date: 2026-04-24
Selected option: `2`
Additional constraint: preserve API-compatibility direction for a later backend
swap.

## Non-Functional Requirements

### NFR-001 Startup

On hosted/dev lanes, cold start of the multiplexer service or primary app path
 shall complete in under 200 ms.

### NFR-002 Interactive Latency

On hosted/dev lanes, pane input-to-visible-output latency shall achieve p95
under 20 ms in representative local smoke scenarios.

### NFR-003 Concurrency Capacity

The design shall support at least 16 concurrent panes across multiple sessions
without architectural rework.

### NFR-004 State Persistence Across Detach

Detach/reattach shall preserve:

- session topology
- pane buffers needed for recapture
- shell state owned by the pane process/runtime

### NFR-005 Hot-Path Discipline

Hot paths shall avoid:

- full-tree scans
- per-keystroke subprocess spawning
- repeated file rereads
- polling loops without explicit design justification

### NFR-006 Error Containment

Failures in one pane or session shall not crash unrelated sessions or the
top-level service.

### NFR-007 Observability

The implementation shall include observable timing or counters for:

- startup time
- attach/detach operations
- pane creation/split
- input-to-output path

### NFR-008 API Stability Direction

The control API shall remain stable enough that current or future callers can
map to session/window/pane control without coupling to a specific backend.

### NFR-009 Backend Isolation

Backend-specific execution details shall be isolated so a later stock-`tmux`
backend experiment can be added without changing external callers.

### NFR-010 Verification

Verification shall include:

- requirement-traceable system tests
- failure-path coverage for invalid targets and missing shell/runtime cases
- representative interactive smoke checks


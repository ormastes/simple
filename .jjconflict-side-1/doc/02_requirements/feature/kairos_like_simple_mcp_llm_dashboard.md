<!-- codex-research -->
# Feature Requirements: KAIROS-Like Simple MCP + LLM Dashboard

**Date:** 2026-04-15
**Selected Option:** 3 - Full Autonomous Assistant Platform

## Goal

Implement a Simple-native KAIROS-like assistant architecture that supports persistent sessions, proactive wakeups, event-driven signals, delegated child-agent work, durable digests/memory summaries, notifications, and operator visibility across `simple mcp` and `llm dashboard`.

## Scope

In scope:

- assistant session lifecycle in `simple mcp`
- periodic tick and external signal wakeups
- bounded child-agent spawn/delegate orchestration
- durable transcripts, timelines, and digest checkpoints
- dashboard views for sessions, events, tasks, blockers, and notifications
- combined live mode when both `simple mcp` and `llm dashboard` are present

Out of scope for the first release:

- opaque unconstrained long-term memory
- autonomous code mutation without explicit session policy
- cross-repo federation as a mandatory baseline

## Functional Requirements

### REQ-KAIROS-001 Session Identity and Lifecycle

The system shall provide first-class assistant sessions with stable IDs, lifecycle states, policy mode, current objective, last wake reason, and resumable persisted state.

### REQ-KAIROS-002 Proactive Tick Scheduler

The system shall support periodic proactive wakeups with explicit schedule metadata, rate limits, pause/resume controls, and wake-reason recording.

### REQ-KAIROS-003 Event and Signal Intake

The system shall support event-driven wakeups through a signal inbox that records source, type, payload summary, enqueue time, and processing outcome.

### REQ-KAIROS-004 Child-Agent Delegation

The system shall support spawned child-agent tasks with parent linkage, scoped objective, status, resource policy, final summary, and bounded result merge-back into the parent session.

### REQ-KAIROS-005 Brief and Digest Generation

The system shall generate compact session briefs and periodic digest checkpoints summarizing recent observations, actions, blockers, and retained follow-up items.

### REQ-KAIROS-006 Notification Routing

The system shall record notification-worthy events and expose notification routing decisions, delivery status, and suppression reasons.

### REQ-KAIROS-007 Standalone `simple mcp` Operation

`simple mcp` shall remain useful without the dashboard by exposing assistant control and inspection through MCP tools/resources/prompts and CLI-accessible status/brief views.

### REQ-KAIROS-008 Standalone `llm dashboard` Operation

`llm dashboard` shall remain useful without a live MCP source by supporting replay/import inspection of assistant timelines, digests, tasks, and notifications from persisted records or snapshots.

### REQ-KAIROS-009 Combined Live Mode

When both products are present, the dashboard shall attach to live assistant state without becoming the source of truth and shall route documented operator actions back through the MCP control plane.

### REQ-KAIROS-010 Operator Visibility

The system shall provide operator-visible session status, task tree, recent events, blockers, failures, and pending approvals rather than hiding background work behind opaque logs.

### REQ-KAIROS-011 Failure Recovery and Evidence

The system shall preserve structured crash, timeout, disconnect, and restart evidence across assistant sessions, child tasks, and bridge failures.

### REQ-KAIROS-012 Retention and Backpressure

The system shall apply bounded retention, digest compaction, and event coalescing/backpressure rules so long-running sessions do not grow unbounded timelines or saturate live views.

## Acceptance Criteria

1. A parent assistant session can start, pause, resume, and emit a brief without the dashboard.
2. A signal can wake a session and produce a persisted timeline entry.
3. A child-agent task can be spawned, tracked, and summarized with parent linkage.
4. The dashboard can inspect persisted assistant records without a live MCP connection.
5. Combined mode can show live session state and route documented control actions back to the assistant core.
6. Crash/restart and stale-bridge cases preserve structured evidence for diagnosis.

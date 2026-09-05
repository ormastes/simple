# LLM Caret Messaging — Non-Functional Requirements

Date: 2026-08-02
Selection: NFR Option N1

- NFR-LLM-MSG-001: Once a canonical write transaction commits, restart recovery loses no accepted message or task event.
- NFR-LLM-MSG-002: Repeating an inbound external event or idempotent write creates no duplicate canonical message or task.
- NFR-LLM-MSG-003: Every context item passes room ACL and redaction policy checks; private-room contents never cross room boundaries.
- NFR-LLM-MSG-004: Hook files contain no transport credentials; local hook tokens are narrowly scoped and external webhook signatures are verified.
- NFR-LLM-MSG-005: Context, queues, payloads, retries, handoffs, and room-agent turns are bounded; permanent failures dead-letter and produce exactly one visible failure update.
- NFR-LLM-MSG-006: Production wrappers execute cached compiled artifacts; hot request paths perform no full-tree scans, unbounded rereads, or synchronous external delivery.
- NFR-LLM-MSG-007: Baseline the primitive server with 10,000 messages, 32 clients, and three agent bindings, then gate warm startup, p95 local request latency, and max RSS at no more than 125% of the accepted baseline.
- NFR-LLM-MSG-008: Unit and integration branch coverage reaches at least 80% for owned domain/application code; every feature requirement has real modern SSpec coverage and generated manual evidence.
- NFR-LLM-MSG-009: Live platform gates retain credential, server/version, command, timestamps, and evidence class; unavailable gates remain blocked/unsupported rather than passing through simulation.
- NFR-LLM-MSG-010: Installation/uninstallation is reversible: merge rather than overwrite, back up changed settings, record before/after hashes and ownership, and never delete user-owned entries.

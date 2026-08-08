# LLM Caret Primitive Messaging PureDatabase

> Production pure-Simple SQL scenarios for canonical primitive rooms. Current
> retained result: **FAIL — 1/10 passed**.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 10 | 10 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Status | Active, failing production evidence |
| Requirements | `doc/02_requirements/feature/llm_caret_messaging.md` |
| Plan | `doc/03_plan/sys_test/llm_caret_messaging.md` |
| Design | `doc/05_design/app/tools/llm_caret_messaging.md` |
| Research | `doc/01_research/app/llm_caret/messaging_platforms.md` |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl` |
| Updated | 2026-08-02 |

## Overview

The executable spec opens real temporary database files through
`PureSqlMessagingStore.open(path)`. It never substitutes an in-memory fixture.
Messages enter with sequence zero because the store owns per-room monotonic
sequence assignment. Every restart scenario closes and reopens the same file.

## Scenarios

### Durable ordered rooms and history

- Create a canonical room, append two messages, and require sequences 1 and 2.
- Close/reopen and require chronological history plus durable audit evidence.
- Page strictly after a supplied sequence with a bounded limit.
- Reject append to a missing room with `room_not_found` and no stored history.

### Idempotency, cursors, and inbound deduplication

- Submit two message IDs with one stable idempotency key and require the
  original canonical ID/sequence with only one stored message.
- Advance one identity's local cursor, reopen, and require independent cursors.
- Accept one `(binding_id, external_event_id)`, reject its duplicate, and allow
  the same external ID for another binding.

### Direct-room isolation

- Persist distinct public and direct-room bodies.
- Close/reopen and query each canonical room separately.
- Require public history never to contain the direct-room body.

### Transactional outbox and dead letters

- Enqueue delivery and retain queued state after a recoverable attempt.
- Close/reopen and require queued delivery recovery.
- Exhaust an attempt ceiling, require `dead_letter`, one durable dead-letter
  row, and one explicit failure audit event.

## Recorded execution evidence

The final permitted 2026-08-02 verify/fix cycle produced 10 examples with 9
failures. Missing-room rejection passed. The earliest durable/history and
direct-room failures reported `array index out of bounds: index is 0 but length
is 0` after queries returned empty history. Idempotency, cursor, inbound dedup,
retry, restart recovery, and dead-letter scenarios also failed. No fourth run
was made because the feature iteration cap had been reached.

## Evidence boundary

These scenarios exercise only the production `PureDatabase` store. Even after
they pass, they do not prove email enrollment, REST/SSE, scoped authentication,
agent hooks, MCP discovery, or any credential-backed external platform.

## Executable source

The complete canonical SSpec remains in
`test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl`.
It uses `step(...)` and only built-in canonical matchers; it contains no TODO,
stub, dummy, or unconditional placeholder pass.

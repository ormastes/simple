# Concurrency Design (Incremental)

## Goals
- Actor-based concurrency with mailbox semantics; eventual work-stealing scheduler per `concurrency.md`.
- Support fire-and-forget `spawn`, message passing (`send`/`recv`/`reply`), and `join` on actor handles.
- Keep ABI narrow so compiler depends on `runtime::concurrency` only.

## Current Implementation
- `runtime::concurrency` provides `ActorHandle` (channels, id, join handle) and `spawn_actor`.
- Compiler maps `spawn`/`send`/`recv`/`reply`/`join` to these runtime APIs; messages are string payloads for now.
- Driver has system test for send/recv/join roundtrip.

## Near-Term Plan
- Message typing: allow structured payloads (enum or serialized bytes) instead of string formatting.
- Timeouts: extend `recv` with optional timeout; return `nil`/error on timeout.
- Error handling: propagate actor panics to callers (join result) and surface as semantic error.
- Move channel bridging out of compiler; keep all mailbox logic in `runtime::concurrency`.

## Scheduler/Mailbox Future
- Replace per-actor threads with a runtime scheduler:
  - Worker threads with work-stealing deques for actor tasks.
  - Mailboxes as MPMC queues; scheduler polls and dispatches messages.
  - Stackless actors (async) run-to-completion; stackful actors support suspension.
- Expose scheduler hooks in `common` for compiler codegen to target (`spawn_task`, `send_msg`, `recv_msg` with timeout).
- Add supervision semantics (restart/stop) and linking between actors.

## Testing
- System tests for send/recv/reply/join; add timeout/guarded cases.
- Stress tests once scheduler arrives (many actors/messages).

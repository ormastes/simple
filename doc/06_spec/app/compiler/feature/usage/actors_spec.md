# Actor Model Concurrency

The actor model provides a message-passing concurrency primitive where isolated actors communicate exclusively through asynchronous messages. Each actor encapsulates its own state and processes messages sequentially from a mailbox, eliminating shared-state races. This spec validates the actor creation, message dispatch, and concurrent execution semantics of Simple's actor system.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RUNTIME-010 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/feature/usage/actors_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Overview

The actor model provides a message-passing concurrency primitive where isolated actors
communicate exclusively through asynchronous messages. Each actor encapsulates its own
state and processes messages sequentially from a mailbox, eliminating shared-state races.
This spec validates the actor creation, message dispatch, and concurrent execution
semantics of Simple's actor system.

## Syntax

```simple
val counter = spawn CounterActor(initial: 0)
counter.send(Increment(by: 1))
val result = counter.ask(GetCount())
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Actor | An isolated concurrent entity with private state and a mailbox |
| Message Passing | Communication via asynchronous send/ask rather than shared memory |
| Mailbox | A queue of incoming messages processed sequentially by the actor |
| Spawn | Creating a new actor instance that runs concurrently |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/actors/result.json` |

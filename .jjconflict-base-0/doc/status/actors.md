# Feature #30: Actors

**Status**: Implemented
**Difficulty**: 3 (was 5)
**Importance**: 4

## Summary

Actor-based concurrency with message passing. spawn, send, recv, reply, and join all working with timeout-based deadlock prevention.

## Current Implementation

- [x] `actor` keyword in parser
- [x] Actor definition with fields and methods
- [x] `spawn` expression
- [x] Fire-and-forget thread spawning
- [x] Basic handle return
- [x] AST: `ActorDef`, `Expr::Spawn`
- [x] Interpreter: thread spawn via `std::thread::spawn`
- [x] Runtime: Thread-local `ACTOR_INBOX`/`ACTOR_OUTBOX`

## Working Syntax

```simple
# Actor definition (parsed)
actor Counter:
    count: i64 = 0

    fn increment(self):
        self.count += 1

# Spawn works
fn work():
    return 42

let handle = spawn work()
main = 0  # Works - spawn is fire-and-forget
```

## Remaining Work

- [x] Working `send()` / `recv()` - implemented with timeout (5s)
- [x] `join()` for waiting on actors
- [x] `reply()` for responses
- [x] Mailbox/message queue system (using mpsc channels)
- [ ] Actor supervision (future enhancement)

## Why Difficulty Reduced (5→3)

- Parser, AST, and basic spawn all work
- Thread spawning infrastructure exists
- Deadlock is a runtime issue, not architectural
- Fix requires replacing blocking channels with async/crossbeam
- Most actor semantics already implemented

## Tests

### Working
- `runner_handles_spawn_expression` - Spawn fire-and-forget works
- `runner_handles_actor_send_recv_join` - Full actor roundtrip (spawn, send, recv, reply, join)

## Files

- `src/parser/src/parser.rs` - actor/spawn parsing
- `src/parser/src/ast.rs` - ActorDef, Expr::Spawn
- `src/compiler/src/lib.rs` - spawn evaluation
- `src/runtime/src/concurrency/` - actor runtime

## Related

- #31 Concurrency Primitives (partial)
- #32 Async Effects (not implemented)
- #33 Stackless Coroutines (not implemented)

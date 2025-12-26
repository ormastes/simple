# Feature #31: Concurrency Primitives

**Status**: Implemented
**Difficulty**: 3 (was 5)
**Importance**: 4

## Summary

Core concurrency primitives: spawn, send, receive for actor communication. All working with timeout-based deadlock prevention.

## Current Implementation

- [x] `spawn` expression (creates thread)
- [x] Basic join support
- [x] Thread-local inbox/outbox infrastructure
- [x] Message type defined

## Working Syntax

```simple
# Spawn is implemented
let handle = spawn some_function()
main = 0  # Fire-and-forget works
```

## Remaining Work

- [x] `send()` with working message passing
- [x] `recv()` with blocking/non-blocking modes (timeout-based)
- [ ] Channel creation syntax (future enhancement)
- [ ] Select/multiplex on channels (future enhancement)

## Why Difficulty Reduced (5→3)

- spawn already works with std::thread::spawn
- Infrastructure exists (ACTOR_INBOX/OUTBOX)
- Deadlock is a specific bug, not missing architecture
- Fix is replacing blocking channels with proper async ones
- Well-understood problem with known solutions (crossbeam, tokio)

## Tests

- `runner_handles_spawn_expression` - Works
- `runner_handles_actor_send_recv_join` - Works (send/recv/reply/join roundtrip)

## Implementation Notes

- Uses `recv_timeout(5 seconds)` to prevent deadlocks
- `try_recv()` available for non-blocking receives
- Standard library `mpsc` channels with timeout work reliably

## Files

- `src/runtime/src/concurrency/mod.rs` - Actor runtime
- `src/compiler/src/lib.rs` - spawn/send/recv evaluation

## Related

- #30 Actors (partial)
- #32 Async Effects
- #33 Stackless Coroutines

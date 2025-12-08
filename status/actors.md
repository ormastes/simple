# Feature: Actors / Spawn (Concurrency)

- **Importance**: 4/5
- **Difficulty**: 5/5
- **Status**: IN_PROGRESS

## Current Work
- Parser supports `actor` definitions and `spawn` expressions.
- Compiler/runtime handle `spawn` as fire-and-forget threads in the interpreter/evaluator; returns a deterministic handle (`0`) until the full scheduler/actor runtime is implemented.

## Next Steps
- Add real actor runtime (mailboxes, send/receive) per `concurrency.md` (work-stealing scheduler, waitless actors).
- Wire spawn return handles and join/cancel semantics; expose message APIs in `common` for compiler/runtime boundary.
- System tests: spawn, send/receive, await timeouts, actor supervision.

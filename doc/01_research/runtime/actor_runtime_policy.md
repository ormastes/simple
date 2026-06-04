# Actor Runtime Policy: Erlang-Style vs Rust-Style

## Context
The current actor plan (docs/plans/18_actor_runtime_scheduler.md) assumes a thread-per-actor scheduler with simple mailboxes. Future evolution needs a clear policy for failure handling, supervision, and message semantics. This note compares Erlang-style actor philosophy with more conventional Rust-style concurrency and proposes a direction.

## Comparison
- **Failure model**
  - Erlang: “Let it crash.” Actors isolate failure; supervisors decide restart/stop; crashing is expected, not exceptional.
  - Rust (typical async/thread): Failures bubble as `Result`/panics; callers often join/await and must handle errors explicitly; restarts are opt-in plumbing.
- **Supervision**
  - Erlang: Supervision trees define restart strategy (one-for-one, one-for-all, rest-for-one), max restarts, backoff, escalation.
  - Rust: Libraries provide task spawning (`tokio::spawn`, threads) without built-in supervision; users layer their own retry/backoff.
- **Message semantics**
  - Erlang: Mailboxes are unbounded by default, selective receive, pattern matching, ordering preserved per-sender.
  - Rust: Channels are typically bounded/unbounded with strict FIFO; no selective receive/pattern matching built in.
- **Isolation**
  - Erlang: Process heap isolation, message copy; no shared memory; GC per process.
  - Rust: Shared-state is possible but discouraged via ownership; channels move values; copying/cloning is explicit.
- **Lifecycle**
  - Erlang: Linking/monitoring ties actor lifetimes; exits propagate per policy.
  - Rust: Joins/handles are manual; no link/monitor concept unless built by the user.
- **Observability**
  - Erlang: Standardized signals for exits, monitors, timeouts; introspection tooling baked in.
  - Rust: Varies by runtime/logging; no standardized actor signals.

## Direction for Simple
- **Default philosophy**: Prefer Erlang-like resilience (“let it crash”) over Rust-style manual error plumbing. Keep handles/joins for interop, but do not require the caller to catch every failure.
- **Supervision**: Introduce supervisor handles and restart policies (one-for-one first). Model as runtime structs plus codegen-visible FFI for spawning under a supervisor.
- **Failure propagation**: On panic/abort inside an actor, notify supervisor and downstream monitors; do not unwind into message loops.
- **Mailboxes**: Keep ordered FIFO per actor; add capacity configuration later. No selective receive yet; pattern matching can compile to filtered recv in the future.
- **Isolation**: Continue pass-by-value for messages (deep copy or shared-arc with refcounts). Avoid shared mutable state in message payloads.
- **Lifecycle links**: Add lightweight monitor/link APIs so other actors can observe exits without joining.
- **Timeouts**: Standardize recv timeouts with a default (current 5s placeholder) and allow configurable duration.
- **Interop with Rust style**: Preserve `ActorHandle::join` for callers that want synchronous waiting; keep `send/recv` usable from non-actor threads for tests and embedding.

## Next Steps
1) Specify supervisor API (spawn under supervisor, restart strategy enum, backoff).  
2) Define error payload for actor exits (panic string, fatal code).  
3) Add monitor/link hooks to the runtime and expose via FFI.  
4) Make mailbox capacity configurable; decide default (probably unbounded for now).  
5) Replace fixed recv timeout with argument + non-blocking try_recv.  
6) Align codegen traps 33-35 with the runtime API once supervision hooks are stable.

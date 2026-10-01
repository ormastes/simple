# Bootstrap distributed builder architecture

Status: implementation in progress, native and remote qualification pending.
Requirements: [retained scope](../02_requirements/feature/bootstrap_distributed_builder.md).

## Owners and boundaries

`src/lib/common/build_manager/contracts.spl` owns domain-specific immutable task,
host and result records. `codec.spl` owns their bounded canonical wire encoding.
These consume frozen copied/encoded payload semantics from the common parallel
ownership model; they introduce no alternate pointer, lease or mutation protocol.

`src/app/bootstrap_builder/manager.spl` owns the dependency state machine and
retry admission. The native app orchestrator owns process handles, durable
journal writes and output admission. `worker.spl` receives a frozen request and
creates an attempt-owned result. `transport.spl` owns local or configured SSH
execution and staging. Only the parent mutates canonical result/publication state.
App `contracts.spl` and `codec.spl` are compatibility facades; only the latter
adds app file persistence. The compiler imports the pure common layer.

Each cross-process boundary carries versioned encoded files, not live objects.
Worker output is child-created data. Parent checks task/attempt/host identity,
declared output set and fresh file hashes before admitting it. A worker cannot
authorize shared cache publication by returning exit zero alone.

## Scheduling and restart

Ready requires every dependency to have admitted successful output. A
topological ordering alone is insufficient. Failure produces terminal rows for
dependents; independent tasks continue under keep-going. Fail-fast stops new
dispatch while retaining accurate rows and reaping owned work. Retries are
bounded and begin only after the previous owned worker is confirmed reaped.
Attempt identity is part of the result key; late output is rejected.

Journal recovery requires exact run identities and current output hashes.
Recorded RUNNING state is not proof of a live process; PID plus creation-time
authority is required before adopting or killing anything. A journal may fail
closed when it cannot safely recover ownership. No process is restarted merely
because observation timed out.

Mutable cache namespaces include phase, producer, task and worker. Keep roots
stable for an unchanged task; isolate attempt publication. Preserve completed
outputs and surviving workers. Compiler cache manifest writes remain with the
compiler parent. Task-result reuse and internal compiler cache reuse are distinct.

## Compiler integration and bootstrapping

Scripts advance existing cached bootstrap immediately. The latest user-selected
ordering uses the permitted genuine Phase 1 seed to compile the standalone
native manager and exercise sanity, then retains that manager through Phase 4.
Adopt it once the required compiler and manager artifacts are qualified; it must
never require itself or the compiler it is currently building as its producer.
Record producer, frozen source, manager and per-host worker digests. The worker
may be a separate Windows executable; transport checks its configured digest
instead of assuming it equals the manager image.

LLVM codegen can use immutable `.ll` files as the first module-task boundary.
MIR capsules and storage snapshots remain in the compiler parent; final object
collection rechecks their original identities before publishing. Provider
backends without an admitted process boundary retain their honest serial path.
This does not certify frontend/HIR/MIR isolation. Full module/SCC integration
remains a requirement with distinct execution evidence.

Remote execution uses only explicitly configured hosts and compiled workers.
Declared inputs are staged and checked, worker executes there, parent fetches
outputs and checks them again. Unconfigured hosts are rejected. Missing remote
execution evidence remains pending, even when transport encoding tests pass.
Current priority is grouped isolated local workers; distributed transport is
later work, with its remaining evidence stated explicitly.

## Performance and evidence

Manager startup imports the small common protocol and app facades, not compiler
frontend/backend modules. Requests use the admitted manifest, with no source-tree
discovery in a worker hot path. Validate bounds once at admission; record warm
startup/request latency/RSS and real cache counters. No speedup is claimed from
slot configuration alone. See [NFRs](../02_requirements/nfr/bootstrap_distributed_builder.md).

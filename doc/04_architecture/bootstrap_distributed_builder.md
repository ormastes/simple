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

The canonical post-Stage-2 route uses the exact admitted Phase 2 compiler to
build and pin manager, worker, index-builder and source-authority images before
the manager is ready. Source, tool and runtime SHA receipts are reread around
each image build. Once ready, every Phase 3 and Phase 4 compile is a manager
task; neither phase depends on the other's result. Each owns distinct mutable
state, output roots and terminal receipts. Host capacity can schedule these
independent children serially without changing their producer graph.

The Phase 2 authority image copies the complete admitted source bytes and
symlink identities into a private read-only snapshot. The compiler's SCV
inventory must select logical `.spl` modules from that authority and bind the
package-ownership policy. A full V2 index task for each phase and backend
must produce typed HIR/MIR receipts for the exact selected module count.
The Phase 3 and Phase 4 LLVM routes each finish before their own Cranelift
routes. Grouped processes share one frontend load per SCC group, receive
immutable warm index and dependency identities, and return per-module results.
Only the parent can promote a qualified SMF, and completion requires a compiled
verifier to match every selected module to a terminal SMF output. An emitted
`.o` by itself remains diagnostic, not completion.

The current source implementation and shell fixtures are static evidence.
An admitted self-hosted Phase 2 image, full-inventory runtime index, and both
backend terminal ledgers have not yet been demonstrated. The Stage 2 byte
snapshot also requires an explicit fixture-role policy so intentional test
sources are accounted for without being compiled as production modules.

Remote execution uses only explicitly configured hosts and compiled workers.
Declared inputs are staged and checked, worker executes there, parent fetches
outputs and checks them again. Unconfigured hosts are rejected. Missing remote
execution evidence remains pending, even when transport encoding tests pass.
Current priority is grouped isolated local workers; distributed transport is
later work, with its remaining evidence stated explicitly.

## Performance and evidence

Capacity admission requires a canonical `capacity.request.sdn` sidecar bound to
the exact task identity and host. Its `owned-platform-boundary-v1` policy
authorizes a fresh platform boundary; it does not alter task/cache identity.
The Linux SOSIX owner walks the cgroup2 mount without following symlinks,
requires memory already delegated at the mount root, and exclusively creates
an empty `simple-parent-<identity>` child. Only that fresh parent's memory
subtree controller is enabled. Its descriptor, device and inode remain pinned
through capacity measurement, capped `clone3`, complete tree reap and removal.
No inherited inhabited cgroup or ambient host root is adopted as the task parent.
The worker writes `capacity.receipt` before launch and `capacity.released`
only after removing its empty parent. Cleanup failures remain errors.
Windows consumes the same authority sidecar, measures the minimum of physical
and commit headroom, and reads back the owned JobObject limit before process
creation. These runtime checks remain separate from scheduler estimates.

Native Linux adapter integration passed on 2026-10-02 (fresh parent, identity
rejection, parent capacity cap, atomic child entry, child memory cap, reap,
cleanup and unchanged global controllers). Rebuilt manager/worker compiler-task
qualification on both hosts remains pending; the native probe is not that proof.

Manager startup imports the small common protocol and app facades, not compiler
frontend/backend modules. The compiled source authority and full index are
explicit pre-group work; a group worker reads its admitted manifest and warm
index rather than rediscovering the whole tree for every member. Process trees
have hard memory limits, physical/commit headroom and disk checks near spawn;
the parent commits results in manifest order and retries only failed or
unattempted groups. Real overlap, full-index peak memory, portable parse-CAS
reuse and native output parity still require measured evidence. No speedup is
claimed from slot or thread settings alone. See [NFRs](../02_requirements/nfr/bootstrap_distributed_builder.md).

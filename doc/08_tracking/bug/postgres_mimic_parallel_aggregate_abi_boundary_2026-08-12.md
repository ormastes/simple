# PostgreSQL mimic parallel worker aggregate ABI boundary

## Status

Open / blocked.  The scalar descriptor is not yet a safe parallel worker
implementation.  The hosted `--inline` profile remains the only truthful
native execution path until the runtime exposes scalar-only owner handles.

## Exact audit

`src/lib/nogc_async_mut/database/postgres_mimic/worker_descriptor.spl` has the
right shape: its native calls carry only six `i64` fields and a generation
tagged descriptor token.  However, the current parallel server does not stop
at that boundary:

| Source boundary | Current payload | Why it is rejected |
| --- | --- | --- |
| `rt_pg_parallel_control_registry_new/get` | `PgParallelControl` | class contains mutex and atomic handles; aggregate ABI is compiler/runtime-layout dependent |
| `rt_pg_dispatch_gate_registry_new/get` | `PgDispatchGate` | nested mutable queue/state crosses SFFI as an aggregate |
| `rt_pg_wire_limits_registry_new/get` | `PgWireLinuxLimits` | aggregate return is decoded in Simple, not a scalar snapshot |
| `rt_pg_wire_server_config_registry_new/get` | `PgWireServerConfig` | contains text and an enum; neither is a scalar ABI |
| `rt_pg_parallel_worker_handoff_new/get` | `PgParallelWorker` | contains listener, text, class state, mutex/atomic handles, and dispatch state |
| `thread_spawn_with_args` callback | `Any` closure carrier | dynamic closure representation is not an ownership/ABI contract |

The comments in the server call this a scalar boundary, but only the worker
slot is scalar.  The four typed registries return the original RuntimeValue,
and the worker handoff still publishes the whole aggregate.  Therefore this
path must not be admitted as parallel or performance evidence.

## Required replacement contract

The parent remains the owner of mutable database/dispatch state.  A worker
may receive only copied scalars and opaque, typed runtime handles:

```text
worker_descriptor_new(worker_id, listener_fd,
    control_handle, dispatch_handle, limits_handle, config_handle) -> token:i64
worker_descriptor_get(token, field) -> i64
worker_descriptor_release(token) -> status:i64       # parent, after join
```

Each `*_handle` API must expose operations as scalar calls (for example,
`control_admit(handle, max_connections) -> connection_id:i64`), rather than
returning a Simple class/struct.  Immutable limits/config must be copied into
bounded scalar fields or read through scalar getters.  No API in the worker
path may accept or return `Any`, text, an enum, a struct, class, raw pointer, or
a borrowed object.  The parent must join every worker before releasing the
descriptor or any referenced handle; failed spawn closes only unspawned
listeners.

## Deterministic reproducer / admission rule

The current source is rejected by this structural predicate:

```text
parallel_linux_server.spl contains
  extern fn rt_pg_*_registry_new(value: Pg...)
  extern fn rt_pg_*_registry_get(token: i64) -> Pg...?
  or rt_pg_parallel_worker_handoff_new(worker: PgParallelWorker)
```

An artifact built while that predicate is true is not a valid parallel
artifact, even if workers print `ready`, because the aggregate can be decoded
with a different layout or outlive its transient graph.  The pre-bind/native
crash evidence is tracked in
`postgres_mimic_native_daemon_invalid_field_receiver_2026-08-12.md`.

## Resume condition

Resume this lane only after a runtime/API change supplies scalar operation
entrypoints and a focused cross-thread test proves: wrong-handle rejection,
bounded slots, stale-generation rejection, concurrent reads, join-before-
release, and no aggregate/`Any` crossing.  Until then, use `--inline` and keep
the parallel claim RED.

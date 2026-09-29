<!-- codex-design -->
# Async identity-owned process lease — detail design

## API contract

The Simple facade exposes these public operations and no token accessors:

```simple
pub fn process_owned_start(command: text, args: [text], policy: OwnedProcessPolicy) -> Result<OwnedProcessLease, OwnedProcessStartError>
pub fn process_owned_poll(me lease: OwnedProcessLease, stdout_capacity: i64, stderr_capacity: i64) -> OwnedProcessPoll
pub fn process_owned_wait(me lease: OwnedProcessLease, wait_ms: i64, stdout_capacity: i64, stderr_capacity: i64) -> OwnedProcessPoll
pub fn process_owned_cancel(me lease: OwnedProcessLease) -> OwnedProcessCancelReceiptV2
pub fn process_owned_result(me lease: OwnedProcessLease) -> Result<OwnedProcessResultV2, OwnedProcessPending>
pub fn process_owned_collect(me lease: OwnedProcessLease) -> Result<OwnedProcessResultV2, OwnedProcessCollectError>
```

`OwnedProcessLease` contains a private capability-registry handle, not public
token words. `OwnedProcessPolicy` validates timeout `1..3_600_000 ms`, TERM
grace `0..30_000 ms`, post-reap drain `0..10_000 ms`, combined retained output
`0..16 MiB`, and per-poll drain `1..256 KiB`. Empty commands, embedded NUL,
invalid arrays, or excessive values fail before reservation.

`OwnedProcessPoll` reports state, bounded stdout/stderr deltas, cumulative seen
and kept counts, truncation, deadline/cancel flags, and runtime error. It does
not report authority fields. `OwnedProcessResultV2` reports evidence fields
including PID, PGID, start identity, exit/signal status, TERM/KILL/reap facts,
output totals, and terminal reason.

## C ABI v2

Add to `src/runtime/runtime.h`:

- `RtOwnedProcessTokenV2 { uint64_t high; uint64_t low; }`;
- versioned `RtOwnedProcessPolicyV2`, `RtOwnedProcessPollReceiptV2`,
  `RtOwnedProcessCancelReceiptV2`, and `RtOwnedProcessResultV2`;
- `rt_process_owned_start_v2(...)`;
- `rt_process_owned_poll_v2(token, wait_ms, out, out_cap, err, err_cap, ...)`;
- `rt_process_owned_cancel_v2(token, ...)`;
- `rt_process_owned_result_v2(token, ...)`;
- `rt_process_owned_collect_v2(token, ...)`.

The language bridge uses opaque runtime values, not an integer array containing
token words:

- `rt_process_owned_start_value_v2(command, args, policy_fields) -> opaque`;
- `rt_process_owned_poll_value_v2(opaque, wait_ms, caps) -> tuple`;
- `rt_process_owned_cancel_value_v2(opaque) -> fields`;
- `rt_process_owned_result_value_v2(opaque) -> tuple`;
- `rt_process_owned_collect_value_v2(opaque) -> tuple`.

The opaque value is registered with a dedicated runtime type tag and finalizer.
The finalizer requests cancellation and drives bounded synchronous cleanup; it
may not silently detach a live child. Explicit `collect` remains required for a
successful application flow.

## Runtime slot layout

Extend `RtOwnedSlot` with state, token, retired flag, deadline, grace/drain
deadlines, stdout/stderr fds, bounded ring/capture buffers, cumulative counters,
wait status, terminal reason, signal flags, and collection state. Store argv
only until `exec` completes. Zero command and token buffers on release.

All public operations lock, resolve token, validate state, and perform one
bounded transition. Blocking wait is repeated bounded poll inside the owner;
it never holds `rt_owned_lock` during OS `poll`, `waitid`, or pipe reads. It
pins the slot with an internal operation reference, releases the lock, performs
the syscall, then reacquires and commits only if generation and token still
match.

Cancellation merely records the request under lock. The poll/wait transition
owner sends signals. If cancellation must make progress without a waiter,
`cancel_v2` itself drives the same transition loop through reap, bounded by the
policy grace and drain deadlines. No second cancellation worker exists.

## Files changed during implementation

Primary owner changes:

- `src/runtime/runtime_process_owned.c`: split reserve/spawn/drive/drain/reap/
  collect helpers; implement token generation and v2 state machine; rewrite v1
  run as a v2 composition.
- `src/runtime/runtime.h`: v2 structs and ABI declarations.
- `src/lib/nogc_sync_mut/io/process_ops.spl`: opaque Simple types and facade.
- `src/lib/nogc_sync_mut/io/__init__.spl`: explicit exports.

ABI registration changes:

- `src/compiler_rust/common/src/runtime_symbols.rs`;
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`;
- `src/compiler/70.backend/backend/stage4_symbol_closure.spl`;
- `src/compiler/70.backend/backend/runtime_compiler.spl` only if the source list
  changes (it should not);
- interpreter registration must return `UnsupportedPlatform`, never fabricate a
  lease.

Compatibility surfaces:

- `src/app/io/mod.spl` and `src/app/io/__init__.spl` re-export only;
- `src/os/_QemuRunner/vm_adapter.spl` consumes the new facade in its own change.

## Error model

Start errors distinguish invalid input, capacity exhausted, entropy failure,
pipe/fork/group/pidfd/identity failures, and unsupported platform. Poll errors
distinguish stale/forged/revoked token, concurrent operation, OS failure, and
invalid bounds. A runtime failure after spawn enters cleanup; it never returns
a live orphan. Collect-before-terminal returns `Pending`; repeated collect
returns `AlreadyCollected` without revealing whether a later slot exists.

## Tests and falsification

Extend `src/runtime/test/runtime_process_owned_selfcheck.c` with live-start
return-before-exit, poll deltas, wait timeout without cancellation, explicit
cancel TERM/grace/KILL/reap, descendant containment, concurrent cancel/poll,
single reap/collect, output flood bounds, inherited pipe deadline, slot
exhaustion, token forgery, stale token after 64+ turnovers, entropy failure,
generation retirement, and injected syscall failures.

Extend `runtime_process_owned_adapter_selfcheck.c` for opaque-value allocation,
finalizer cleanup, malformed policy/strings, every allocation failure, and no
token leakage in returned arrays. Extend `runtime_process_owned_nonunix_selfcheck.c`
to prove start returns `ENOTSUP` and spawns nothing.

Extend `test/01_unit/app/io/process_owned_facade_contract_spec.spl` to require
the v2 symbols, opaque lease, absence of public token fields/getters, explicit
exports, interpreter refusal, and v1 compatibility. Add
`test/02_integration/os/sosix/qemu_owned_process_lease_spec.spl` for a fake QEMU
that stays live while QMP readiness is polled, then exits or is cancelled.

The implementation is not accepted until the existing MCI process-safety gate
retains its v1 evidence and adds v2 selfcheck receipts. Tests must sabotage
token comparison, group kill, reap, and non-Unix refusal independently.

## Migration sequence

1. Add v2 ABI and tests without changing v1 behavior.
2. Implement v1 as v2 start/wait/collect and compare receipts in selfchecks.
3. Export the Simple lease and migrate only `QemuRunner` first.
4. Migrate other long-lived process owners individually.
5. Audit compiled references to tuple cancellation; deprecate it.
6. Remove v1 cancellation authority only in a declared compatibility release.

## Performance and observability

Start adds one CSPRNG read and pidfd open. Poll performs bounded pipe work and
at most one lifecycle transition. Receipts expose live slot count, exhausted
starts, cancellations, TERM/KILL counts, reaps, truncations, stale-token
rejects, and cleanup failures through test/debug diagnostics; no registry
enumeration API is public.


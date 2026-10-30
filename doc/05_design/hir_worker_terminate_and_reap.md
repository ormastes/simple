# HIR worker terminate-and-reap contract

**Status:** proposed; API names and runtime adapters require implementation review.

## Context

A HIR worker runs under a queue owner and can publish claims, terminal rows, and
cache data. When its deadline expires, the coordinator must stop the exact owned
worker before sealing its remaining rows or releasing the queue to other work.
The existing `process_kill(pid) -> bool` has provider-specific completion
semantics, while `process_wait` may consume or invalidate the provider's handle.
A kill followed by a second wait therefore cannot prove ownership quiescence.

The attempt-15 evidence and cache-preservation facts are recorded in
`doc/08_tracking/bug/hir_shard_timeout_double_wait_blocks_ledger_2026-10-30.md`.

## Proposed contract

Keep the existing `process_kill` semantics for its other callers. Add a distinct
operation, provisionally `process_terminate_owned_v1`, that consumes an
ownership-qualified child lease and returns a durable result rather than a
boolean. The operation must bind a PID/token to its process generation so a
reused PID or stale handle cannot authorize ledger mutation.

Provisional result shapes:

```text
WorkerTerminationResultV1 =
    Quiescent { owner_identity, leader_exit_status, scope_receipt }
  | TimedOut { owner_identity, ownership_retained }
  | Failed { owner_identity?, reason, ownership_retained }
```

The request carries the owned lease, a monotonic deadline, and a graceful-stop
grace interval. Platform adapters may escalate from graceful termination to
forced termination within that finite budget. A `Quiescent` result proves the
leader was reaped and every child in the requested ownership scope can no longer
write to the queue. If the platform cannot establish descendant/group quiescence,
it must return `TimedOut` or `Failed` with ownership retained; leader exit alone
is insufficient when descendants may still mutate the ledger.

The receipt is the canonical authority for later `wait`, collection, and queue
sealing. Repeated collection returns the same terminal receipt. Unknown handles,
PID-generation mismatch, wait failure, an expired deadline, or incomplete group
proof never become `Quiescent`. Do not substitute a liveness boolean for the
receipt.

## Provider implications

The adapters must normalize their current differences without changing the
legacy `process_kill` contract:

- Rust hosted process registry currently kills and waits while removing the
  child entry; the new operation must retain or publish the resulting terminal
  receipt so a second collector can retrieve it.
- Pure Simple `core_process.spl` performs signal/escalation and `waitpid`, but
  currently does not validate every allocation/wait result as an explicit
  receipt.
- POSIX C paths differ: some signal and return without waiting; others wait only
  on escalation and treat `ECHILD` as success. They need an owned-child result,
  EINTR-safe wait, bounded escalation, and a proof scoped to the owned child.
- Windows paths differ between `TerminateProcess`/handle close and redirected
  process tokens that maintain completion state. A terminal receipt must be
  published only after a confirmed wait result and retained for collection.

The attempt-15 producer used the hosted Rust runtime library identified in the
bug record. The cross-provider requirements prevent this fix from making a
portable claim based on that single provider.

## HIR coordinator behavior

Preserve the original timeout as the worker's nonzero failure. Once the owned
termination operation returns `Quiescent`, the coordinator may seal only that
owner's uncompleted claims as blocked/failed and continue independent queued
work when the existing policy allows. It must not report aggregate success. If
termination remains uncertain, keep the ledger globally blocked and retain the
owner lease/receipt for recovery. Completed `PASS/CACHE_STORED` rows remain immutable retained candidates under
their source, producer, runtime, target, and cache identities. A later run must
still perform its ordinary identity, header, and dependency checks before reuse.

## Acceptance cases

1. Graceful stop of a live owned child produces one retained quiescence receipt.
2. A child requiring forced termination is terminated and reaped within the
   monotonic deadline; timeout remains a failed worker result.
3. A child that already exited but remains registered can be collected once, and
   duplicate collection returns the same receipt.
4. Unknown, stale, or PID-reused ownership returns `Failed`; it cannot seal a
   queue row.
5. Wait failure, deadline exhaustion, or unsupported descendant/group ownership
   retains the lease and leaves the HIR ledger fail-closed.
6. Nested child processes are covered by the requested ownership scope; a reaped
   leader with a live descendant does not yield `Quiescent`.
7. The coordinator does not call `process_wait` again after a provider has
   consumed the underlying handle; no path converts the timeout to PASS.
8. Regression against attempt 15's terminal shape proves the 2,778 existing
   `PASS/CACHE_STORED` rows remain retained candidates while the unfinished
   claimed work is explicitly failed/blocked and the overall build remains
   nonzero; cache admission still runs normal identity/header/dependency checks.

## Evidence status

The attempt-15 log and cache inventory support the timeout/double-wait diagnosis.
These acceptance cases are design requirements, not executed tests. No code
change, API unification, HIR retry, or full-CLI retry has been performed for
this proposal.

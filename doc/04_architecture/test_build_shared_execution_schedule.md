# Shared build/test execution state

Status: candidate implementation and specs authored; execution evidence pending.

## Decision

Extract provenance-free execution scheduling state from the existing
common.task_runner.scheduler into common.task_runner.execution_schedule.
The build adapter continues validating BuildRun/BuildTask identities, dependency
admission, output digests and bounded retry policy. Ordinary tests adapt their
real file inventory without manufacturing build provenance.

The common state owns readiness and slot lifecycle. A dispatch reserves its
host slot before spawn; RUNNING and REAPED both retain the reservation. Only
parent acceptance after collection permits terminal publication or retry.
The build wrapper may project its existing serialized status/host fields into
this value API; it must not retain a second independently mutable state owner.

Both adapters already reach nogc_sync_mut.io.process_ops: app.io.process_ops
is a compatibility reexport. Preserve that async owner and domain-specific
capture/receipt adapters; do not add a second thread pool or process backend.

## Ownership boundaries

- Scheduling state, result slots and admission decisions: one parent.
- Child requests: immutable encoded values or existing owned process handles;
  never share the parent's mutable map/arrays with a worker.
- Completion: bounded capture plus process/reap evidence returned to parent.
- Commit: domain validation, then deterministic input-order result publication.
- No lockless map: there are no concurrent scheduling-map writers.

The CPU fiber scheduler is not a drop-in process scheduler: its progress-rule
memory over-admission must not weaken test worker limits. Test session/QEMU/
cache/gated routing stays above the ordinary runnable-file scheduling adapter.

## Verification obligations

Exercise capacity reservation, out-of-order completions, reap-before-release,
spawn denial, stale/duplicate completion, retry, cancellation, hard resource
denial, independent failure continuation and manifest-order reporting. Preserve
the existing build DAG/receipt and runner process/evidence regression suites.

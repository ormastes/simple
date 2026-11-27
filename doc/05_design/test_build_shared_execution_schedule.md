# Shared execution scheduling detail design

Status: source adapters and focused specs authored; execution unverified.

Common owner: std.common.task_runner.execution_schedule.
Public state: TaskExecutionScheduleV1 (statuses, host_ids, next_pending,
host_active, error), containing
no source, compiler, output or build receipt fields.
host_active is an ordinary parent-owned Dict<text, i64>, never shared with
workers. It avoids rescanning every task on each process admission.
TaskExecutionSelectionV1 contains indices and error for checked readiness.

Shared API names:
- task_execution_schedule_v1: checked value projection from existing state.
- task_execution_ready_v1: bounded stable-order selection from next_pending,
  using a manifest-sized eligibility bitmap; return TaskExecutionSelectionV1.
- task_execution_host_active_v1: RUNNING/REAPED host charge.
- task_execution_dispatch_v1: PENDING -> RUNNING with reservation.
- task_execution_reap_v1: RUNNING -> REAPED, preserving charge.
- task_execution_finish_v1: REAPED -> terminal status after domain validation.
- task_execution_retry_v1: REAPED -> PENDING only after domain retry admission.

Do not duplicate build provenance validation in this core. Build wrappers
retain exact error contracts and serialization. Test wrappers retain global
process-slot and RSS/CPU admission, bounded capture, child collection and BDD
evidence parsing; shared state controls the runnable-file lifecycle.

Dispatch advances next_pending past nonpending entries. Retry moves it back
to the retried index when necessary. The ordinary independent test queue
therefore advances incrementally. Build adapters retain derived cursor and
host counts, rebuilding them once for legacy state or journal decode rather
than rescanning all tasks on every transition. Wire fields remain unchanged.
This removes explicit full-array rescan work; value-copy costs are unmeasured.
RUNNING and REAPED charge a host; terminal acceptance or admitted retry releases
the charge. Do not expose this mutable map to workers.

Manual scenario helper names reserved: step("Reserve capacity before spawn"),
step("Collect the child before releasing capacity"), and
step("Publish results in manifest order"). No passing placeholder helpers.

## Interpreter child receipts

For assert-ran interpreter children, append --test-result-file with a unique
path derived from the PID/timestamp/sequence capture name. The CLI configures
SIMPLE_TEST_RESULT_FILE inside that child; never mutate the parent's env.
Refuse existing receipt, expectations or trace paths before spawning. Keep
native `test` child arguments and its evidence protocol unchanged.

Store the evidence path in AsyncTestRun. After timeout, capture and cleanup
checks, use the canonical structured BDD parser, which owns valid trace-sidecar
cleanup and retains malformed trace diagnostics. Delete receipt/expectations
only after reaping is proven; unresolved cleanup retains evidence and capacity.
Green output cannot replace missing/zero evidence or override deadline expiry.

async_structured_evidence_spec.spl covers receipt authority, red/missing/zero
evidence, deadlines, independent reverse-order collection and cleanup using
temporary files. It does not prove actual child transport, scheduling order
or compiler behavior. All new specs remain UNRUN. Real parallel green/red/empty
fixtures under the exact qualified Phase2 descendant CLI remain mandatory.

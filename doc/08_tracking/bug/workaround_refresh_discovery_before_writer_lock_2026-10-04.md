# Workaround refresh discovers sources before acquiring its writer lock

Status: repair draft; native execution and paired performance measurements pending.

## Observed boundary

The Windows Cranelift Phase3 log at
`runtime/windows-restart-20261004/diagnostic-phase3-restart-80/cranelift/phase3/build.log`
begins with `workarounds: refresh failed: workaround Git failed (-1):` followed by
`TIMEOUT`. The NUL regression LLVM log at
`runtime/windows-restart-20261004/p2-nul-cranelift/validation-retry-80/llvm/build.log`
reports `workaround writer lock unavailable`. Its Cranelift sibling and inventory
Hello logs report incomplete coverage. These are distinct outcomes; incomplete
coverage is not evidence that there are no applicable workarounds.

`run_native_build_worker` already refreshes only when
`SIMPLE_NATIVE_BUILD_WORKER != 1`. No per-shard refresh defect is established.
However, `refresh_workarounds_at` ran both HEAD discovery and Git status (including
all untracked paths) before acquiring the writer lock. Concurrent coordinators
therefore each paid the discovery cost even when they could not become writers.
Status decoding also used `paths.contains` for each candidate, giving quadratic
membership work on a large status result.

## Repair

Acquire the existing five-second writer lock before Git discovery. A private
helper owns the fallible discovery calls; its Result returns to the lock owner,
which always releases the lock before returning. Keep the 30-second Git command
deadline, output bounds, final HEAD comparison, linked-source rereads, canonical
bug database checks, atomic publication, and coverage rules unchanged. Contended
requests still return an error and never claim a clean or complete index.

Replace status-path linear membership with a Dict while preserving first-encounter
order and both sides of rename/copy records. This is the same narrow algorithm
previously drafted in the frozen `simple-native-coalesce-array-20261004` checkout;
that checkout remains untouched. Existing tracked-path and refresh-batch owners
already use this membership structure.

## Validation and limits

`bug_workaround_store_spec.spl` adds exact rename/copy order/dedup assertions and
a held-lock test in an unborn Git repository. The latter requires the contention
error before the invalid-HEAD error, then checks discovery failure releases the
lock and publishes no index. Existing tests retain changed HEAD, malformed links,
unknown bugs, pending WAL, reverted annotations, and incomplete-coverage checks.

Whitespace validation passed. Tests and compiler execution have not run because
the active bootstrap lanes own the native build resources. No elapsed-time or RSS
improvement is claimed. Paired native timing/RSS cohorts and the actual product
retry remain required. In particular, an uncontended Git process timeout remains
an independent issue; this change does not remove all refresh work or justify
skipping source/coverage validation.

# Generic SDK failed-readiness behavior

SOURCE_ONLY / NOT_RUN. The public signature stays
`daemon_ensure_responsive(config, start_fn, ping_fn) -> bool`.

The client first invokes the existing `daemon_ensure_running` once. Its false
result returns false immediately. Its true result permits exactly one
`ping_fn()` invocation, whose result is returned. The client performs no signal,
second startup attempt, recovery sleep or lock mutation after readiness failure.
The existing startup wait and request polling remain unchanged.

The old PID-kill branch was not backed by an exact process owner. It is removed,
along with imports used only by that branch and its unused kill extern. The
async client is already a direct re-export of this sync backend, so no second
implementation or facade change is needed. Config/callback inputs remain data
and policy hooks, not exact-instance recovery authority.

Adjacent boundaries were inspected: daemon lock helpers are PID metadata and
are not upgraded to native owners by this patch; `daemon_stop` sends explicit
IPC; service `daemon_base_stop_owned` releases its PID-file state and does not
magically own the corresponding process. The existing `OwnedProcessLease`
supports only processes obtained through an actual owned launch and is reused
for test fixture cleanup. No versioned recovery API is needed for this narrow
fail-closed fix. A later recovery feature must compose real owned service/process
recovery rather than reconstructing ownership from the lock.

The app-specific test-daemon readiness wrapper is independent: it checks an
already-running daemon and pings through its own protocol. The current test
runner calls that wrapper. It is not changed or accused of using the SDK's
unsafe branch. The stale design line claiming automatic app restart is corrected
using that actual call-chain evidence.

Tests call both production exports. Six callback scenarios cover one startup
refusal, failed-ping disappearance and existing success through both facades.
They never leave a test-process PID available to the failed-probe branch.
Six owned-sentinel scenarios cover existing failed probe, startup-then-failed
probe, and false startup that nevertheless publishes its owned child's PID.
Only the known fixture child is a failed-probe target; liveness guards turn
uncertainty into a successful callback result to avoid the old kill branch.
The test then fails after attempting owned cleanup. No unrelated or pre-existing
process is targeted.

The native fixture launches one bounded shell that prints its own PID and execs
sleep with that same PID. `OwnedProcessLease` retains actual native ownership;
the printed PID is only reproduction metadata. Cleanup polls/cancels/collects
through that lease and clears it only after positive reaping. Unknown cleanup
keeps the owner and private directory. Cases are serial because their callback
state is module-local. Native provider admission, shell availability, deadline,
signal and collection behavior remain NOT_RUN, not proven safety evidence.

The bounded fixture-review correction publishes the actual post-`collect()`
lease before classifying its result. Reaped results other than errors 11/16
positively consume that lease even when a terminal error is nonzero; those keep
the first diagnostic and root metadata but cannot be polled again. A not-reaped
or 11/16 result retains the updated live lease. Unknown collection keeps that
lease quarantined without native retry. The next case checks all retained
owner/root/lock/diagnostic state before allocating or overwriting any new path.
Only clean native consumption and successful directory removal clear fixture
metadata. These fault paths are source-reviewed, not dynamically executed.

The isolated snapshot uses exact current release preimages and preserves all
unreleased local prior artifacts. No app/Container/Host files, runtime exports,
active workspace files, build campaigns or Git state are changed by authoring.

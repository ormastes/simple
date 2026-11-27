# DAE-02: generic SDK readiness kills a PID-file target after uncertainty

Status: SOURCE_FIX_AUTHORED / NOT_RUN. This report does not mark full DAE-02,
native ownership, explicit recovery or daemon qualification complete.

Actual release inspected: `26fb9715a47384057df6c70c6567b8591bbafad6` as identified
by root; isolated correction preimages are from current release/1.0.0 commit
`671d5545201c5c5bc73ea0ddaf0db0f143218d44`. The actual SDK source is unchanged
between the relevant inspected behavior and that current preimage.

`src/lib/nogc_sync_mut/daemon_sdk/client.spl:42–53` tries readiness, then reads
the PID file, calls `rt_process_kill` on a positive/live PID, sleeps, and tries
startup/readiness again. Its inputs are only config and two callbacks. It has
no exact native process owner authorizing that signal or replacement. A failed
ping or failed startup is uncertainty, not evidence that the recorded process
can be killed. A PID file may describe a live non-daemon process or a replaced
incarnation; the SDK must not adopt it as an owner.

The sync backend is re-exported by the async facade and both module entrypoints.
The repository's app-specific `src/app/test_daemon/client.spl:35–36` is already
non-destructive and does not call this helper. Its actual test-runner callers
use the app wrapper and may fall back to direct tests. This defect report must
not mislabel that separate readiness path as unsafe. One older resource-governor
design line saying the app restarts a lock owner is corrected accordingly.

The narrow fix reuses the existing pending proposal in
`/tmp/orchestrator-daemon-responsive-next.patch`: call `daemon_ensure_running`
once; return false immediately on failure; otherwise return the one ping result.
Remove the unused PID-reading/liveness imports and kill extern from this client.
No signature, facade, startup implementation, lock lifecycle or stop protocol is
changed. Existing `daemon_stop` remains an explicit IPC request, not PID killing.

The discovered local `responsive_spec.spl`, its manual, and
`orchestrator_shared_daemon_operations.md` are unreleased WIP absent from the
current release commit. They express intended safety but do not prove a landed
source fix; they are preserved untouched. The earlier seven-file ownership
review explicitly excluded full responsiveness. The prior same-feature cycle
count cannot be reconstructed from those artifacts, so no fresh six-cycle
allowance or invented remaining budget is claimed. This lane performs one narrow
initial correction and review under root's source-only instruction.

Reproduction/prevention specifications call the actual production SDK through
both facades. Callback cases safely reproduce duplicate startup without a live
failed-probe target. Native cases use an actual `OwnedProcessLease` sentinel;
only its own child PID is written to a private fixture lock. Failed readiness
must return false with unchanged lock bytes, one eligible ping, no replacement,
and a still-live sentinel. Startup-refusal-with-published-PID is also covered.
Fixture cancellation/collection uses the existing exact owner, never the PID
file or a raw signal. Uncertain cleanup retains its actual lease and directory.

No runtime/build/native campaign or unrelated-process experiment was executed.
All twelve authored scenarios are NOT_RUN; native liveness/reap assertions are
not claimed as observed results. PID-reuse safety of every lock operation and a
versioned exact-owner recovery service remain outside this correction.

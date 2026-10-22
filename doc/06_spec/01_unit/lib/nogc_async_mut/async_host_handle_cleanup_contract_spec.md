# Actual runtime cancellation cleanup

**Execution: UNRUN.** C3 adds the chained-cleanup counterexample while preserving all prior scenarios. Existing compiled runner only.

Executable: `test/01_unit/lib/nogc_async_mut/async_host_handle_cleanup_contract_spec.spl`.

<details>
<summary>Shared actual-owner helpers and setup</summary>

```simple
# codex-system-test
# @req REQ-MC-006
# Actual single-carrier owner/handle cleanup. Physical multicarrier/unwind UNRUN/open.
use std.spec.*
use std.spec.step
use std.async_core.{Poll, Priority, TaskState}
use std.async.cancellation.{CancellationToken, cancellation_registry_live_count}
use std.async.sync.{AsyncMutex, AsyncMutexLease}
use std.async_host.scheduler.{HostScheduler, HostTaskContext, HostTaskSignals}
use std.thread_sffi.{thread_current_id}
use std.nogc_sync_mut.concurrent.thread.{thread_spawn_with_i64_args_id, thread_join_by_id}
use std.async_host.handle.{HostTaskHandle}

var cleanup_scheduler = HostScheduler.new(1)
var cleanup_mutex = AsyncMutex.hosted(0)
var cleanup_holder: usize = 0
var cleanup_waiter: usize = 0
var cleanup_successor: usize = 0
var cleanup_visits: [i64] = []
var cleanup_saved_lease: Option<AsyncMutexLease> = nil
var cleanup_runs: i64 = 0
var cleanup_running_ready: bool = false

fn cleanup_handle(id: usize) -> HostTaskHandle<()>:
    val context_result = cleanup_scheduler.task_context(id)
    val context = context_result.unwrap()
    HostTaskHandle(task_id: id, state: TaskState.Pending, result: nil,
        error: nil, cancel_token: context.lifetime, wakers: [], context: Some(context))

fn cleanup_holder_poll() -> Poll<()>:
    val context_result = cleanup_scheduler.task_context(cleanup_holder)
    val context = context_result.unwrap()
    match cleanup_mutex.poll_acquire(context):
        case Poll.Ready(Ok(lease)):
            cleanup_saved_lease = Some(lease)
            cleanup_visits = cleanup_visits.push(10)
        case _: fail("holder must acquire the actual mutex")
    Poll.Pending

fn cleanup_waiter_poll() -> Poll<()>:
    val context_result = cleanup_scheduler.task_context(cleanup_waiter)
    val context = context_result.unwrap()
    match cleanup_mutex.poll_acquire(context):
        case Poll.Pending:
            cleanup_visits = cleanup_visits.push(20)
            Poll.Pending
        case Poll.Ready(Ok(lease)):
            cleanup_visits = cleanup_visits.push(21)
            expect(cleanup_mutex.release(lease)).to_equal(true)
            Poll.Ready(())
        case _: fail("waiter unexpectedly refused")

fn cleanup_successor_poll() -> Poll<()>:
    val context_result = cleanup_scheduler.task_context(cleanup_successor)
    val context = context_result.unwrap()
    match cleanup_mutex.poll_acquire(context):
        case Poll.Pending:
            cleanup_visits = cleanup_visits.push(30)
            Poll.Pending
        case Poll.Ready(Ok(lease)):
            cleanup_visits = cleanup_visits.push(31)
            expect(cleanup_mutex.release(lease)).to_equal(true)
            Poll.Ready(())
        case _: fail("successor unexpectedly refused")

fn cleanup_setup():
    cleanup_scheduler = HostScheduler.new(1)
    cleanup_mutex = AsyncMutex.hosted(2)
    cleanup_visits = []
    cleanup_saved_lease = nil
    cleanup_holder = cleanup_scheduler.schedule(Priority.Normal, cleanup_holder_poll)
    cleanup_waiter = cleanup_scheduler.schedule(Priority.Normal, cleanup_waiter_poll)
    cleanup_successor = cleanup_scheduler.schedule(Priority.Normal, cleanup_successor_poll)
    expect(cleanup_scheduler.run_one()).to_equal(true)
    expect(cleanup_scheduler.run_one()).to_equal(true)
    expect(cleanup_scheduler.run_one()).to_equal(true)
    expect(cleanup_visits).to_equal([10, 20, 30])
    expect(cleanup_mutex.pending_count()).to_equal(2)
    expect(cleanup_scheduler.tasks[cleanup_waiter].state).to_equal(TaskState.Suspended)

fn cleanup_teardown():
    for id in [cleanup_holder, cleanup_waiter, cleanup_successor]:
        expect(cleanup_scheduler.reap_task(id)).to_equal(true)
    expect(cleanup_mutex.close()).to_equal(true)

fn cleanup_once():
    cleanup_runs = cleanup_runs + 1

fn cleanup_running_poll() -> Poll<()>:
    val context_result = cleanup_scheduler.task_context(cleanup_holder)
    val context = context_result.unwrap()
    expect(context.register_cleanup(900, cleanup_once)).to_equal(true)
    expect(context.request_cancel()).to_equal(true)
    # Drain while Running; cleanup must wait for this callback to return.
    cleanup_scheduler.has_runnable()
    expect(cleanup_runs).to_equal(0)
    if cleanup_running_ready:
        Poll.Ready(())
    else:
        Poll.Pending

fn cleanup_running_case(ready: bool):
    val baseline = cancellation_registry_live_count()
    cleanup_scheduler = HostScheduler.new(1)
    cleanup_runs = 0
    cleanup_running_ready = ready
    cleanup_holder = cleanup_scheduler.schedule(Priority.Normal, cleanup_running_poll)
    val handle = cleanup_handle(cleanup_holder)
    expect(cleanup_scheduler.run_one()).to_equal(true)
    expect(cleanup_scheduler.tasks[cleanup_holder].state).to_equal(TaskState.Cancelled)
    expect(cleanup_runs).to_equal(1)
    expect(handle.is_cancelled()).to_equal(true)
    cleanup_scheduler.run()
    expect(cleanup_runs).to_equal(1)
    expect(cleanup_scheduler.reap_task(cleanup_holder)).to_equal(true)
    expect(cancellation_registry_live_count()).to_equal(baseline)

fn cleanup_independent_poll() -> Poll<()>:
    cleanup_visits = cleanup_visits.push(99)
    Poll.Ready(())

# Only immutable scalar IDs cross this boundary. The child constructs and owns
# all context/queue state; no live parent task authority or cleanup crosses.
fn cleanup_foreign_carrier_probe(parent_carrier: i64, sentinel: i64) -> i64:
    val child_carrier = thread_current_id()
    if child_carrier <= 0 or child_carrier == parent_carrier:
        return 0
    val signals = HostTaskSignals(ready: [], cancelled: [], owner_thread: parent_carrier)
    var context = HostTaskContext(task_id: sentinel as usize,
        lifetime: CancellationToken(token_id: -1, parent_id: -1),
        signals: signals, wake_pending: false, cleanup_ids: [],
        cleanup_actions: [], closed: false)
    if context.on_owner_thread() or context.request_cancel():
        return 0
    if context.cancellation_requested or context.cancel_pending or context.closed:
        return 0
    if signals.ready.len() != 0 or signals.cancelled.len() != 0:
        return 0
    73

var cleanup_chain_a_count: i64 = 0
var cleanup_chain_b_count: i64 = 0
var cleanup_chain_b_context: Option<HostTaskContext> = nil

fn cleanup_chain_a_action():
    cleanup_chain_a_count = cleanup_chain_a_count + 1
    val context = cleanup_chain_b_context.unwrap()
    expect(context.request_cancel()).to_equal(true)

fn cleanup_chain_b_action():
    cleanup_chain_b_count = cleanup_chain_b_count + 1

fn cleanup_chain_a_poll() -> Poll<()>:
    val result = cleanup_scheduler.task_context(cleanup_holder)
    val context = result.unwrap()
    expect(context.register_cleanup(901, cleanup_chain_a_action)).to_equal(true)
    cleanup_visits = cleanup_visits.push(40)
    Poll.Pending

fn cleanup_chain_b_poll() -> Poll<()>:
    val result = cleanup_scheduler.task_context(cleanup_waiter)
    val context = result.unwrap()
    expect(context.register_cleanup(902, cleanup_chain_b_action)).to_equal(true)
    cleanup_visits = cleanup_visits.push(50)
    Poll.Pending
```

</details>

## unlinks a parked waiter and releases a holder exactly once

1. Park actual mutex waiters behind an actual owner
2. Cancel the queued waiter twice through its production handle
3. Cancel the holder and require its successor to acquire without manual release
4. Drain again and reclaim terminal resources without resurrection

Expected: all actual dispatch/state/refusal/resource assertions in the executable scenario hold.

<details>
<summary>Executable SSpec</summary>

```simple
    it "unlinks a parked waiter and releases a holder exactly once":
        step("Park actual mutex waiters behind an actual owner")
        val baseline = cancellation_registry_live_count()
        cleanup_setup()
        var waiter = cleanup_handle(cleanup_waiter)
        var holder = cleanup_handle(cleanup_holder)
        step("Cancel the queued waiter twice through its production handle")
        waiter.cancel()
        waiter.cancel()
        expect(cleanup_scheduler.has_runnable()).to_equal(false)
        expect(cleanup_mutex.pending_count()).to_equal(1)
        expect(cleanup_scheduler.tasks[cleanup_waiter].state).to_equal(TaskState.Cancelled)
        step("Cancel the holder and require its successor to acquire without manual release")
        holder.cancel()
        cleanup_scheduler.run()
        expect(cleanup_visits).to_equal([10, 20, 30, 31])
        expect(cleanup_mutex.pending_count()).to_equal(0)
        expect(cleanup_scheduler.tasks[cleanup_holder].state).to_equal(TaskState.Cancelled)
        expect(cleanup_scheduler.tasks[cleanup_successor].state).to_equal(TaskState.Completed)
        val stale_lease = cleanup_saved_lease.unwrap()
        expect(cleanup_mutex.release(stale_lease)).to_equal(false)
        step("Drain again and reclaim terminal resources without resurrection")
        cleanup_scheduler.run()
        expect(cleanup_visits).to_equal([10, 20, 30, 31])
        cleanup_teardown()
        expect(cancellation_registry_live_count()).to_equal(baseline)
```

</details>

## cancels a granted waiter before its next poll and hands to its successor

1. Park two waiters and cancel the current holder
2. Cancel the handoff recipient before dispatch

Expected: all actual dispatch/state/refusal/resource assertions in the executable scenario hold.

<details>
<summary>Executable SSpec</summary>

```simple
    it "cancels a granted waiter before its next poll and hands to its successor":
        step("Park two waiters and cancel the current holder")
        val baseline = cancellation_registry_live_count()
        cleanup_setup()
        var holder = cleanup_handle(cleanup_holder)
        var waiter = cleanup_handle(cleanup_waiter)
        holder.cancel()
        expect(cleanup_scheduler.has_runnable()).to_equal(true)
        step("Cancel the handoff recipient before dispatch")
        waiter.cancel()
        cleanup_scheduler.run()
        expect(cleanup_visits).to_equal([10, 20, 30, 31])
        expect(cleanup_scheduler.tasks[cleanup_waiter].state).to_equal(TaskState.Cancelled)
        expect(cleanup_mutex.pending_count()).to_equal(0)
        cleanup_teardown()
        expect(cancellation_registry_live_count()).to_equal(baseline)
```

</details>

## defers Running cancellation cleanup when a poll returns Pending

1. Request and drain cancellation inside an actual running poll

Expected: all actual dispatch/state/refusal/resource assertions in the executable scenario hold.

<details>
<summary>Executable SSpec</summary>

```simple
    it "defers Running cancellation cleanup when a poll returns Pending":
        step("Request and drain cancellation inside an actual running poll")
        cleanup_running_case(false)
```

</details>

## lets cancellation win over a Running poll Ready result

1. Return Ready after requesting cancellation inside the actual callback

Expected: all actual dispatch/state/refusal/resource assertions in the executable scenario hold.

<details>
<summary>Executable SSpec</summary>

```simple
    it "lets cancellation win over a Running poll Ready result":
        step("Return Ready after requesting cancellation inside the actual callback")
        cleanup_running_case(true)
```

</details>

## cannot use a reaped cancelled handle to cancel a replacement lifetime

1. Cancel a real task during its poll and reap its terminal record
2. Admit a replacement lifetime and retry the retained cancelled handle
3. Require replacement progress and unchanged old cleanup count

Expected: all actual dispatch/state/refusal/resource assertions in the executable scenario hold.

<details>
<summary>Executable SSpec</summary>

```simple
    it "cannot use a reaped cancelled handle to cancel a replacement lifetime":
        step("Cancel a real task during its poll and reap its terminal record")
        val baseline = cancellation_registry_live_count()
        cleanup_scheduler = HostScheduler.new(1)
        cleanup_runs = 0
        cleanup_running_ready = false
        cleanup_visits = []
        cleanup_holder = cleanup_scheduler.schedule(Priority.Normal, cleanup_running_poll)
        var stale = cleanup_handle(cleanup_holder)
        val old_context = stale.context.unwrap()
        expect(cleanup_scheduler.run_one()).to_equal(true)
        expect(cleanup_scheduler.reap_task(cleanup_holder)).to_equal(true)
        step("Admit a replacement lifetime and retry the retained cancelled handle")
        val replacement = cleanup_scheduler.schedule(Priority.Normal, cleanup_independent_poll)
        val live = cleanup_handle(replacement)
        val new_context = live.context.unwrap()
        expect(new_context.lifetime.token_id == old_context.lifetime.token_id).to_equal(false)
        stale.cancel()
        expect(cleanup_scheduler.signals.cancelled.len()).to_equal(0)
        expect(new_context.is_live()).to_equal(true)
        step("Require replacement progress and unchanged old cleanup count")
        cleanup_scheduler.run()
        expect(cleanup_visits).to_equal([99])
        expect(cleanup_runs).to_equal(1)
        expect(live.is_cancelled()).to_equal(false)
        expect(stale.is_cancelled()).to_equal(true)
        expect(cleanup_scheduler.reap_task(replacement)).to_equal(true)
        expect(cancellation_registry_live_count()).to_equal(baseline)
```

</details>

## rejects cancellation of a normally completed closed context without a false cancellation fact

1. Complete a real task and retain its bound handle
2. Require explicit refusal without queue or cancellation mutation

Expected: all actual dispatch/state/refusal/resource assertions in the executable scenario hold.

<details>
<summary>Executable SSpec</summary>

```simple
    it "rejects cancellation of a normally completed closed context without a false cancellation fact":
        step("Complete a real task and retain its bound handle")
        val baseline = cancellation_registry_live_count()
        cleanup_scheduler = HostScheduler.new(1)
        cleanup_visits = []
        val id = cleanup_scheduler.schedule(Priority.Normal, cleanup_independent_poll)
        var handle = cleanup_handle(id)
        val context = handle.context.unwrap()
        cleanup_scheduler.run()
        expect(cleanup_visits).to_equal([99])
        expect(context.lifetime.is_valid()).to_equal(false)
        expect(context.request_cancel()).to_equal(false)
        step("Require explicit refusal without queue or cancellation mutation")
        handle.cancel()
        expect(handle.error.is_some()).to_equal(true)
        expect(handle.is_cancelled()).to_equal(false)
        expect(cleanup_scheduler.signals.cancelled.len()).to_equal(0)
        expect(cleanup_scheduler.reap_task(id)).to_equal(true)
        expect(cancellation_registry_live_count()).to_equal(baseline)
```

</details>

## rejects a foreign carrier without transporting parent task authority

1. Keep the live admitted parent context on its owner carrier
2. Pass only scalar carrier identity to a real isolated child thread
3. Require distinct-carrier refusal and a successful scalar join result
4. Dispatch the untouched parent task exactly once and reap its lifetime

Expected: all actual dispatch/state/refusal/resource assertions in the executable scenario hold.

<details>
<summary>Executable SSpec</summary>

```simple
    it "rejects a foreign carrier without transporting parent task authority":
        step("Keep the live admitted parent context on its owner carrier")
        val baseline = cancellation_registry_live_count()
        cleanup_scheduler = HostScheduler.new(1)
        cleanup_visits = []
        val id = cleanup_scheduler.schedule(Priority.Normal, cleanup_independent_poll)
        val handle = cleanup_handle(id)
        val context = handle.context.unwrap()
        step("Pass only scalar carrier identity to a real isolated child thread")
        val worker = thread_spawn_with_i64_args_id(thread_current_id(), 17, cleanup_foreign_carrier_probe)
        expect(worker).to_be_greater_than(0)
        val result = thread_join_by_id(worker)
        step("Require distinct-carrier refusal and a successful scalar join result")
        expect(result).to_equal(Some(73))
        expect(cleanup_scheduler.signals.cancelled.len()).to_equal(0)
        expect(context.is_live()).to_equal(true)
        step("Dispatch the untouched parent task exactly once and reap its lifetime")
        cleanup_scheduler.run()
        cleanup_scheduler.run()
        expect(cleanup_visits).to_equal([99])
        expect(handle.is_cancelled()).to_equal(false)
        expect(cleanup_scheduler.reap_task(id)).to_equal(true)
        expect(cancellation_registry_live_count()).to_equal(baseline)
```

</details>

## drains cancellation published by another parked task cleanup in one run

1. Park two actual tasks with independent registered cleanup actions
2. Cancel A and let its real cleanup publish cancellation of parked B
3. Require both cleanups and token releases in that single scheduler run
4. Repeat requests and run again without cleanup duplication or task revival

Expected: all actual dispatch/state/refusal/resource assertions in the executable scenario hold.

<details>
<summary>Executable SSpec</summary>

```simple
    it "drains cancellation published by another parked task cleanup in one run":
        step("Park two actual tasks with independent registered cleanup actions")
        val baseline = cancellation_registry_live_count()
        cleanup_scheduler = HostScheduler.new(1)
        cleanup_visits = []
        cleanup_chain_a_count = 0
        cleanup_chain_b_count = 0
        cleanup_holder = cleanup_scheduler.schedule(Priority.Normal, cleanup_chain_a_poll)
        cleanup_waiter = cleanup_scheduler.schedule(Priority.Normal, cleanup_chain_b_poll)
        var a = cleanup_handle(cleanup_holder)
        var b = cleanup_handle(cleanup_waiter)
        val a_context = a.context.unwrap()
        val b_context = b.context.unwrap()
        cleanup_chain_b_context = Some(b_context)
        expect(cleanup_scheduler.run_one()).to_equal(true)
        expect(cleanup_scheduler.run_one()).to_equal(true)
        expect(cleanup_visits).to_equal([40, 50])
        expect(cleanup_scheduler.tasks[cleanup_holder].state).to_equal(TaskState.Suspended)
        expect(cleanup_scheduler.tasks[cleanup_waiter].state).to_equal(TaskState.Suspended)
        step("Cancel A and let its real cleanup publish cancellation of parked B")
        a.cancel()
        expect(cleanup_scheduler.signals.cancelled.len()).to_equal(1)
        cleanup_scheduler.run()
        step("Require both cleanups and token releases in that single scheduler run")
        expect(cleanup_chain_a_count).to_equal(1)
        expect(cleanup_chain_b_count).to_equal(1)
        expect(cleanup_scheduler.tasks[cleanup_holder].state).to_equal(TaskState.Cancelled)
        expect(cleanup_scheduler.tasks[cleanup_waiter].state).to_equal(TaskState.Cancelled)
        expect(cleanup_scheduler.signals.cancelled.len()).to_equal(0)
        expect(a_context.cancel_pending).to_equal(false)
        expect(b_context.cancel_pending).to_equal(false)
        expect(a_context.lifetime.is_valid()).to_equal(false)
        expect(b_context.lifetime.is_valid()).to_equal(false)
        expect(cancellation_registry_live_count()).to_equal(baseline)
        step("Repeat requests and run again without cleanup duplication or task revival")
        a.cancel()
        b.cancel()
        cleanup_scheduler.run()
        expect(cleanup_chain_a_count).to_equal(1)
        expect(cleanup_chain_b_count).to_equal(1)
        expect(cleanup_visits).to_equal([40, 50])
        expect(cleanup_scheduler.signals.cancelled.len()).to_equal(0)
        expect(cleanup_scheduler.reap_task(cleanup_holder)).to_equal(true)
        expect(cleanup_scheduler.reap_task(cleanup_waiter)).to_equal(true)
        expect(cancellation_registry_live_count()).to_equal(baseline)
        cleanup_chain_b_context = nil
```

</details>

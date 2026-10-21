# async host handle cancellation contract spec

Authored manual. **All scenarios UNRUN.** Existing compiled SSpec runner only. Scalar-only child carrier refusal is separate from physical scheduler worker execution.

Executable: `test/01_unit/lib/nogc_async_mut/async_host_handle_cancellation_contract_spec.spl`.

<details>
<summary>Shared actual-owner helpers and setup</summary>

```simple
# codex-system-test
# @req REQ-MC-006
# Expected-red HostTaskHandle -> HostRuntime cancellation linkage. UNRUN.
# Single owner test; no shared mutation across OS carriers.
use std.spec.*
use std.spec.step
use std.async_host.runtime.{HostRuntime}
use std.async_core.{Priority}
use std.async.cancellation.{CancellationToken, cancellation_registry_capacity, cancellation_registry_live_count}

var cancelled_callback_visits: i64 = 0
var independent_callback_visits: i64 = 0

fn cancelled_runtime_callback() -> i64:
    cancelled_callback_visits = cancelled_callback_visits + 1
    37

fn independent_runtime_callback() -> i64:
    independent_callback_visits = independent_callback_visits + 1
    41
```

</details>

## does not invoke a callback cancelled before the runtime dispatches

1. Submit real work without dispatching its runtime
2. Cancel through the returned production task handle
3. Run the production scheduler and inspect callback side effects
4. Run again and reject duplicate work or cancelled-task resurrection

Expected: actual owner dispatch, state, refusal and cleanup satisfy the folded assertions.

<details>
<summary>Executable SSpec</summary>

```simple
    it "does not invoke a callback cancelled before the runtime dispatches":
        step("Submit real work without dispatching its runtime")
        cancelled_callback_visits = 0
        independent_callback_visits = 0
        var runtime = HostRuntime.new()
        var handle = runtime.run_task(cancelled_runtime_callback)
        val independent = runtime.run_task(independent_runtime_callback)
        step("Cancel through the returned production task handle")
        handle.cancel()
        expect(handle.is_cancelled()).to_equal(true)
        step("Run the production scheduler and inspect callback side effects")
        runtime.run()
        expect(cancelled_callback_visits).to_equal(0)
        expect(independent_callback_visits).to_equal(1)
        expect(independent.is_cancelled()).to_equal(false)
        step("Run again and reject duplicate work or cancelled-task resurrection")
        runtime.run()
        expect(cancelled_callback_visits).to_equal(0)
        expect(independent_callback_visits).to_equal(1)
        expect(independent.is_cancelled()).to_equal(false)
```

</details>

## fails admission before callback and recovers after real token release

1. Fill the actual bounded cancellation registry
2. Require failed terminal admission without a callback or user cancellation fact
3. Release capacity and prove the same runtime dispatches accepted work

Expected: actual owner dispatch, state, refusal and cleanup satisfy the folded assertions.

<details>
<summary>Executable SSpec</summary>

```simple
    it "fails admission before callback and recovers after real token release":
        step("Fill the actual bounded cancellation registry")
        val baseline = cancellation_registry_live_count()
        var held: [CancellationToken] = []
        for index in 0..cancellation_registry_capacity():
            val token = CancellationToken.new()
            if token.is_valid():
                held = held.push(token)
        cancelled_callback_visits = 0
        independent_callback_visits = 0
        var runtime = HostRuntime.new()
        step("Require failed terminal admission without a callback or user cancellation fact")
        var refused = runtime.run_task(cancelled_runtime_callback)
        expect(refused.is_finished()).to_equal(true)
        expect(refused.error.is_some()).to_equal(true)
        expect(refused.is_cancelled()).to_equal(false)
        refused.cancel()
        runtime.run()
        expect(cancelled_callback_visits).to_equal(0)
        step("Release capacity and prove the same runtime dispatches accepted work")
        for token in held:
            token.release()
        val accepted = runtime.run_task_with_priority(independent_runtime_callback, Priority.High)
        runtime.run()
        expect(independent_callback_visits).to_equal(1)
        expect(accepted.is_cancelled()).to_equal(false)
        expect(runtime.scheduler.reap_task(accepted.id())).to_equal(true)
        expect(cancellation_registry_live_count()).to_equal(baseline)
```

</details>

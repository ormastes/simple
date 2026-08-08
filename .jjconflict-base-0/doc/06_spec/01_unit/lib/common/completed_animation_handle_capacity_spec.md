# JavaScript Completed Animation Handle Capacity

> JS runtime regression scenario for completed Node-compatible timer handles.

| Field | Value |
|---|---|
| Status | Static-ready; runtime execution held pending a source-admitted pure-Simple CLI |
| Executable source | `test/01_unit/lib/common/completed_animation_handle_capacity_spec.spl` |
| Canonical owner | `JsInterpreter._native_timer_refresh` |
| Unsupported claims | No browser, requirement, pixel, Draw IR, RSS, or native/GPU evidence claim |

## Purpose

Prove that reusing a completed Node-compatible `requestAnimationFrame` handle
cannot bypass the shared 4,096-entry JavaScript timer and animation task bound.
This is JS runtime conformance, not production browser behavior. Draw IR is not
applicable because rejection occurs before a frame is queued.

## Operator flow

1. Complete one animation-frame callback and require its pending task and handle
   lookup to retire.
2. Fill the shared timer and animation task queue to exactly 4,096 entries.
3. Refresh the completed animation handle and require the queue and both
   parallel handle-lookup arrays to remain at 4,096.
4. Require one completed frame and unchanged retired-handle state:
   `1:false:false:true`.

## Failure handling

- A queue or handle count above 4,096 fails the executable SSpec.
- A refreshed, active, or incomplete animation handle fails the lifecycle
  receipt.
- Do not substitute the Rust seed or bootstrap solely to run this scenario.

<details>
<summary>Complete executable SSpec</summary>

```simple
"""Completed animation handles must not bypass the shared JS task bound."""

use std.spec.*

use std.js.engine.runtime.{JsRuntime}
use std.js.engine.js_error.{Logger, LogLevel}
use std.js.types.js_types.{JsValue}

describe "JavaScript completed animation handle capacity":
    # @manual: show
    # @capture(text)
    it "should reject completed animation refresh when the task queue is full":
        step("Complete one requestAnimationFrame handle")
        var runtime = JsRuntime.new(
            Logger.new("completed-animation-capacity", LogLevel.Error)
        )
        expect(runtime.eval(
            "var frames = 0; var completedFrame = " +
            "requestAnimationFrame(function() { frames = frames + 1; });"
        ).is_ok()).to_equal(true)
        expect(runtime.drain_due_timers(16)).to_equal(1)
        expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(0)
        expect(runtime.interpreter.timer_handle_ids.len()).to_equal(0)
        expect(runtime.interpreter.timer_handle_object_ids.len()).to_equal(0)

        step("Fill the canonical timer and animation task queue")
        match runtime.eval(
            "var denied = 0; for (var i = 0; i < 4096; i = i + 1) {" +
            " if (setTimeout(function() {}, 1000) === undefined) {" +
            " denied = denied + 1; } } denied"
        ):
            Ok(JsValue.Number(denied)):
                expect(denied).to_equal(0.0)
            _:
                fail("Expected the canonical task queue to reach capacity")
        expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(4096)
        expect(runtime.interpreter.timer_handle_ids.len()).to_equal(4096)
        expect(
            runtime.interpreter.timer_handle_object_ids.len()
        ).to_equal(4096)

        step("Refresh the completed animation handle without exceeding capacity")
        expect(runtime.eval(
            "completedFrame.refresh() === completedFrame"
        ).is_ok()).to_equal(true)
        expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(4096)
        expect(runtime.interpreter.timer_handle_ids.len()).to_equal(4096)
        expect(
            runtime.interpreter.timer_handle_object_ids.len()
        ).to_equal(4096)
        match runtime.eval(
            "frames + ':' + completedFrame.refreshed + ':' +" +
            " completedFrame.active + ':' + completedFrame.completed"
        ):
            Ok(JsValue.String(state)):
                expect(state).to_equal("1:false:false:true")
            _:
                fail("Expected the completed animation handle to remain retired")
```

</details>

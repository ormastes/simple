# Js Timer Drain Limit Specification

> Tests covering JavaScript timer drain limit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Timer Drain Limit Specification

## Scenarios

### JavaScript timer drain limit

#### mutates the active timer queues without replacement arrays

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- mutates the active timer queues without replacement arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mutates the active timer queues without replacement arrays")
val interpreter_source = rt_file_read_text(
    "src/lib/nogc_sync_mut/js/engine/interpreter.spl"
) ?? ""
val async_source = rt_file_read_text(
    "src/lib/nogc_sync_mut/js/engine/interpreter_async.spl"
) ?? ""
val native_source = rt_file_read_text(
    "src/lib/nogc_sync_mut/js/engine/interpreter_native.spl"
) ?? ""
expect(async_source.contains(
    "var rest: [PendingTimerTask]"
)).to_be(false)
expect(native_source.contains(
    "var rest: [PendingTimerTask]"
)).to_be(false)
expect(async_source).to_contain(
    "val task = self.pending_timer_tasks[0]"
)
expect(interpreter_source).to_contain(
    "me _timer_heap_remove_at(index: i64)"
)
expect(interpreter_source).to_contain(
    "val _ = self.pending_timer_tasks.pop()"
)
expect(async_source).to_contain(
    "self._timer_heap_remove_at(0)"
)
expect(async_source.contains(
    "while i < self.pending_timer_tasks.len()"
)).to_be(false)
expect(async_source.contains("better_due_task")).to_be(false)
expect(native_source.contains("better_due_task")).to_be(false)
```

</details>

#### does not allocate Node timer handles in browser mode

- does not allocate Node timer handles in browser mode
   - Expected: runtime.eval("function noop() {}").is_ok() is true
   - Expected: runtime.drain_due_timers(now) equals `1`
   - Expected: runtime.interpreter.object_store.next_id equals `baseline`
   - Expected: runtime.interpreter.timer_handle_ids.len() equals `0`
   - Expected: runtime.interpreter.timer_handle_object_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not allocate Node timer handles in browser mode")
var runtime = JsRuntime.new_browser(
    Logger.new("browser-timer-heap", LogLevel.Error)
)
expect(runtime.eval("function noop() {}").is_ok()).to_equal(true)
val baseline = runtime.interpreter.object_store.next_id
var now = 0
while now < 128:
    match runtime.eval("setTimeout(noop, 0)"):
        Ok(JsValue.Number(_)): pass_dn
        _:
            fail("Expected browser setTimeout to return a numeric id")
    expect(runtime.drain_due_timers(now)).to_equal(1)
    now = now + 1
expect(runtime.interpreter.object_store.next_id).to_equal(baseline)
expect(runtime.interpreter.timer_handle_ids.len()).to_equal(0)
expect(runtime.interpreter.timer_handle_object_ids.len()).to_equal(0)
```

</details>

#### coalesces an overdue interval to one callback per clock advance

- coalesces an overdue interval to one callback per clock advance
   - Expected: scheduled.is_ok() is true
   - Expected: runtime.drain_due_timers(1000000000) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("coalesces an overdue interval to one callback per clock advance")
var runtime = JsRuntime.new(Logger.new("timer-limit", LogLevel.Error))
val scheduled = runtime.eval(
    "var ticks = 0; setInterval(function() { ticks = ticks + 1; }, 1);"
)
expect(scheduled.is_ok()).to_equal(true)

expect(runtime.drain_due_timers(1000000000)).to_equal(1)
```

</details>

#### yields after one thousand nested zero-delay callbacks

- yields after one thousand nested zero-delay callbacks
   - Expected: scheduled.is_ok() is true
   - Expected: runtime.drain_due_timers(0) equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yields after one thousand nested zero-delay callbacks")
var runtime = JsRuntime.new(Logger.new("timer-limit", LogLevel.Error))
val scheduled = runtime.eval(
    "var ticks = 0; function again() { ticks = ticks + 1; setTimeout(again, 0); } setTimeout(again, 0);"
)
expect(scheduled.is_ok()).to_equal(true)

expect(runtime.drain_due_timers(0)).to_equal(1000)
```

</details>

#### drains a full due queue in deadline and creation order

- drains a full due queue in deadline and creation order
   - Expected: scheduled.is_ok() is true
   - Expected: runtime.interpreter.pending_timer_tasks.len() equals `4096`
   - Expected: runtime.drain_due_timers(4095) equals `1000`
   - Expected: runtime.drain_due_timers(4095) equals `1000`
   - Expected: runtime.drain_due_timers(4095) equals `1000`
   - Expected: runtime.drain_due_timers(4095) equals `1000`
   - Expected: runtime.drain_due_timers(4095) equals `96`
   - Expected: runtime.interpreter.pending_timer_tasks.len() equals `0`
   - Expected: result equals `4096:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drains a full due queue in deadline and creation order")
var runtime = JsRuntime.new_browser(
    Logger.new("timer-bulk-order", LogLevel.Error)
)
val scheduled = runtime.eval(
    "var fired = 0; var mismatches = 0; function record(expected) { if (expected !== 4095 - fired) { mismatches = mismatches + 1; } fired = fired + 1; } for (var i = 0; i < 4096; i = i + 1) { setTimeout(record, 4095 - i, i); }"
)
expect(scheduled.is_ok()).to_equal(true)
expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(4096)

expect(runtime.drain_due_timers(4095)).to_equal(1000)
expect(runtime.drain_due_timers(4095)).to_equal(1000)
expect(runtime.drain_due_timers(4095)).to_equal(1000)
expect(runtime.drain_due_timers(4095)).to_equal(1000)
expect(runtime.drain_due_timers(4095)).to_equal(96)
expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(0)
match runtime.eval("fired + ':' + mismatches"):
    Ok(JsValue.String(result)):
        expect(result).to_equal("4096:0")
    _:
        fail("Expected full ordered timer drain result")
```

</details>

#### lets an interval cancel its queued continuation

- lets an interval cancel its queued continuation
   - Expected: scheduled.is_ok() is true
   - Expected: runtime.drain_due_timers(100) equals `1`
   - Expected: runtime.drain_due_timers(200) equals `0`
   - Expected: ticks equals `1.0`
   - Expected: metadata equals `1:true:false`
   - Expected: runtime.interpreter.timer_handle_ids.len() equals `0`
   - Expected: runtime.interpreter.timer_handle_object_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets an interval cancel its queued continuation")
var runtime = JsRuntime.new(Logger.new("timer-limit", LogLevel.Error))
val scheduled = runtime.eval(
    "var ticks = 0; var timer = setInterval(function() { ticks = ticks + 1; clearInterval(timer); }, 1);"
)
expect(scheduled.is_ok()).to_equal(true)

expect(runtime.drain_due_timers(100)).to_equal(1)
expect(runtime.drain_due_timers(200)).to_equal(0)
match runtime.eval("ticks"):
    Ok(JsValue.Number(ticks)):
        expect(ticks).to_equal(1.0)
    _:
        fail("Expected one self-canceled interval callback")
match runtime.eval(
    "timer.fireCount + ':' + timer.closed + ':' + timer.active"
):
    Ok(JsValue.String(metadata)):
        expect(metadata).to_equal("1:true:false")
    _:
        fail("Expected final self-canceled interval metadata")
expect(runtime.interpreter.timer_handle_ids.len()).to_equal(0)
expect(runtime.interpreter.timer_handle_object_ids.len()).to_equal(0)
```

</details>

#### keeps an interval in its original same-deadline queue slot

- keeps an interval in its original same-deadline queue slot
   - Expected: runtime.drain_due_timers(10) equals `1`
   - Expected: runtime.drain_due_timers(20) equals `2`
   - Expected: order equals `AAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps an interval in its original same-deadline queue slot")
var runtime = JsRuntime.new(Logger.new("timer-order", LogLevel.Error))
expect(runtime.eval(
    "var order = ''; var interval = setInterval(function() { order = order + 'A'; if (order === 'AA') { clearInterval(interval); } }, 10); setTimeout(function() { order = order + 'B'; }, 20);"
).is_ok()).to_equal(true)
expect(runtime.drain_due_timers(10)).to_equal(1)
expect(runtime.drain_due_timers(20)).to_equal(2)
match runtime.eval("order"):
    Ok(JsValue.String(order)):
        expect(order).to_equal("AAB")
    _:
        fail("Expected interval ordering to remain stable")
```

</details>

#### runs due timers by deadline instead of insertion order

- runs due timers by deadline instead of insertion order
   - Expected: runtime.drain_due_timers(20) equals `2`
   - Expected: order equals `EL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs due timers by deadline instead of insertion order")
var runtime = JsRuntime.new_browser(
    Logger.new("timer-deadline-order", LogLevel.Error)
)
expect(runtime.eval(
    "var order = ''; setTimeout(function() { order = order + 'L'; }, 20); setTimeout(function() { order = order + 'E'; }, 10);"
).is_ok()).to_equal(true)

expect(runtime.drain_due_timers(20)).to_equal(2)
match runtime.eval("order"):
    Ok(JsValue.String(order)):
        expect(order).to_equal("EL")
    _:
        fail("Expected earliest timer deadline first")
```

</details>

#### runs a Promise microtask checkpoint between timer callbacks

- runs a Promise microtask checkpoint between timer callbacks
   - Expected: runtime.drain_due_timers(0) equals `2`
   - Expected: order equals `AMB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs a Promise microtask checkpoint between timer callbacks")
var runtime = JsRuntime.new_browser(
    Logger.new("timer-microtask-order", LogLevel.Error)
)
expect(runtime.eval(
    "var order = ''; setTimeout(function() { order = order + 'A'; Promise.resolve(1).then(function() { order = order + 'M'; }); }, 0); setTimeout(function() { order = order + 'B'; }, 0);"
).is_ok()).to_equal(true)

expect(runtime.drain_due_timers(0)).to_equal(2)
match runtime.eval("order"):
    Ok(JsValue.String(order)):
        expect(order).to_equal("AMB")
    _:
        fail("Expected a microtask checkpoint between timers")
```

</details>

#### runs Node nextTick FIFO before Promise microtasks and the next timer

- runs Node nextTick FIFO before Promise microtasks and the next timer
   - Expected: runtime.drain_due_timers(0) equals `3`
   - Expected: order equals `ANMB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs Node nextTick FIFO before Promise microtasks and the next timer")
var runtime = JsRuntime.new(
    Logger.new("timer-next-tick-order", LogLevel.Error)
)
expect(runtime.eval(
    "var order = ''; setTimeout(function() { order = order + 'A'; Promise.resolve(1).then(function() { order = order + 'M'; }); process.nextTick(function() { order = order + 'N'; }); }, 0); setTimeout(function() { order = order + 'B'; }, 0);"
).is_ok()).to_equal(true)

expect(runtime.drain_due_timers(0)).to_equal(3)
match runtime.eval("order"):
    Ok(JsValue.String(order)):
        expect(order).to_equal("ANMB")
    _:
        fail("Expected nextTick then microtask before the next timer")
```

</details>

#### yields before the next timer when a microtask checkpoint hits its cap

- yields before the next timer when a microtask checkpoint hits its cap
   - Expected: runtime.drain_due_timers(0) equals `1`
   - Expected: state equals `1000:false`
   - Expected: runtime.drain_due_timers(0) equals `1`
   - Expected: state equals `1001:true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yields before the next timer when a microtask checkpoint hits its cap")
var runtime = JsRuntime.new_browser(
    Logger.new("timer-microtask-cap", LogLevel.Error)
)
expect(runtime.eval(
    "var hits = 0; var second = false; setTimeout(function() { for (var i = 0; i < 1001; i = i + 1) { Promise.resolve(i).then(function() { hits = hits + 1; }); } }, 0); setTimeout(function() { second = true; }, 0);"
).is_ok()).to_equal(true)

expect(runtime.drain_due_timers(0)).to_equal(1)
match runtime.eval("hits + ':' + second"):
    Ok(JsValue.String(state)):
        expect(state).to_equal("1000:false")
    _:
        fail("Expected the next timer to remain queued at the cap")
expect(runtime.drain_pending_microtasks()).to_be(true)
expect(runtime.drain_due_timers(0)).to_equal(1)
match runtime.eval("hits + ':' + second"):
    Ok(JsValue.String(state)):
        expect(state).to_equal("1001:true")
    _:
        fail("Expected the yielded checkpoint before the next timer")
```

</details>

#### bounds pending timer tasks per document

- bounds pending timer tasks per document
   - Expected: denied equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds pending timer tasks per document")
var runtime = JsRuntime.new(Logger.new("timer-limit", LogLevel.Error))
val result = runtime.eval(
    "var denied = 0; for (var i = 0; i < 4100; i = i + 1) { if (setTimeout(function() {}, 1000) === undefined) { denied = denied + 1; } } denied"
)
match result:
    Ok(JsValue.Number(denied)):
        expect(denied).to_equal(4.0)
    _:
        fail("Expected numeric timer-limit result")
```

</details>

#### keeps a single requestAnimationFrame chain alive past handle history

- keeps a single requestAnimationFrame chain alive past handle history
   - Expected: scheduled.is_ok() is true
   - Expected: frames equals `4097.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a single requestAnimationFrame chain alive past handle history")
var runtime = JsRuntime.new(Logger.new("timer-limit", LogLevel.Error))
val scheduled = runtime.eval(
    "var frames = 0; function frame() { frames = frames + 1; requestAnimationFrame(frame); } requestAnimationFrame(frame);"
)
expect(scheduled.is_ok()).to_equal(true)

var frame_time = 16
while frame_time <= 4097 * 16:
    val _ = runtime.drain_due_timers(frame_time)
    frame_time = frame_time + 16
match runtime.eval("frames"):
    Ok(JsValue.Number(frames)):
        expect(frames).to_equal(4097.0)
    _:
        fail("Expected requestAnimationFrame chain past 4096 handles")
```

</details>

#### fires chained animation frames once and retires completed lookups

- fires chained animation frames once and retires completed lookups
   - Expected: scheduled.is_ok() is true
   - Expected: runtime.drain_due_timers(16) equals `1`
   - Expected: runtime.drain_due_timers(32) equals `1`
   - Expected: runtime.drain_due_timers(48) equals `1`
   - Expected: runtime.interpreter.pending_timer_tasks.len() equals `0`
   - Expected: runtime.interpreter.timer_handle_ids.len() equals `0`
   - Expected: runtime.interpreter.timer_handle_object_ids.len() equals `0`
   - Expected: runtime.interpreter.pending_timer_tasks.len() equals `0`
   - Expected: runtime.interpreter.timer_handle_ids.len() equals `0`
   - Expected: runtime.interpreter.timer_handle_object_ids.len() equals `0`
   - Expected: frames equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fires chained animation frames once and retires completed lookups")
var runtime = JsRuntime.new(Logger.new("timer-limit", LogLevel.Error))
val scheduled = runtime.eval(
    "var frames = 0; function frame() { frames = frames + 1; if (frames < 3) { requestAnimationFrame(frame); } } requestAnimationFrame(frame);"
)
expect(scheduled.is_ok()).to_equal(true)

expect(runtime.drain_due_timers(16)).to_equal(1)
expect(runtime.drain_due_timers(32)).to_equal(1)
expect(runtime.drain_due_timers(48)).to_equal(1)
expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(0)
expect(runtime.interpreter.timer_handle_ids.len()).to_equal(0)
expect(runtime.interpreter.timer_handle_object_ids.len()).to_equal(0)
expect(runtime.eval(
    "var canceled = setTimeout(function() { frames = frames + 100; }, 1); clearTimeout(canceled);"
).is_ok()).to_equal(true)
expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(0)
expect(runtime.interpreter.timer_handle_ids.len()).to_equal(0)
expect(runtime.interpreter.timer_handle_object_ids.len()).to_equal(0)
match runtime.eval("frames"):
    Ok(JsValue.Number(frames)):
        expect(frames).to_equal(3.0)
    _:
        fail("Expected each requestAnimationFrame callback once")
```

</details>

#### preserves actual frame time when animation handles are refreshed

- preserves actual frame time when animation handles are refreshed
   - Expected: runtime.drain_due_timers(33) equals `1`
   - Expected: runtime.eval("refreshedFrame.refresh() === refreshedFrame").is_ok() is true
   - Expected: runtime.drain_due_timers(66) equals `1`
   - Expected: metadata equals `33:66:66`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves actual frame time when animation handles are refreshed")
var runtime = JsRuntime.new(Logger.new("timer-limit", LogLevel.Error))
expect(runtime.eval(
    "var frameTimes = ''; var refreshedFrame = requestAnimationFrame(function(frameTime) { frameTimes = frameTimes + frameTime + ':'; }); refreshedFrame.refresh();"
).is_ok()).to_equal(true)

expect(runtime.drain_due_timers(33)).to_equal(1)
expect(runtime.eval("refreshedFrame.refresh() === refreshedFrame").is_ok()).to_equal(true)
expect(runtime.drain_due_timers(66)).to_equal(1)
match runtime.eval("frameTimes + refreshedFrame.lastFiredAt"):
    Ok(JsValue.String(metadata)):
        expect(metadata).to_equal("33:66:66")
    _:
        fail("Expected refreshed animation frames to use dispatch time")
```

</details>

#### refreshes a completed timeout from the current clock

- refreshes a completed timeout from the current clock
   - Expected: usable is true
   - Expected: runtime.drain_due_timers(10) equals `1`
   - Expected: runtime.interpreter.timer_handle_ids.len() equals `0`
   - Expected: usable is true
   - Expected: same_handle is true
   - Expected: runtime.interpreter.timer_handle_ids.len() equals `1`
   - Expected: runtime.interpreter.timer_handle_object_ids.len() equals `1`
   - Expected: metadata equals `10:10:20:true:false`
   - Expected: runtime.drain_due_timers(19) equals `0`
   - Expected: runtime.drain_due_timers(20) equals `1`
   - Expected: runtime.drain_due_timers(21) equals `0`
   - Expected: runtime.interpreter.timer_handle_ids.len() equals `0`
   - Expected: runtime.interpreter.timer_handle_object_ids.len() equals `0`
   - Expected: metadata equals `2:2:false:true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refreshes a completed timeout from the current clock")
var runtime = JsRuntime.new(Logger.new("timer-limit", LogLevel.Error))
expect(runtime.eval(
    "var refreshTicks = 0; var refreshed = setTimeout(function() { refreshTicks = refreshTicks + 1; }, 10); var numericId = refreshed.valueOf(); var refBefore = refreshed.hasRef(); refreshed.unref(); var unrefed = refreshed.hasRef(); refreshed.ref(); var rerefed = refreshed.hasRef();"
).is_ok()).to_equal(true)
match runtime.eval(
    "numericId === refreshed.id && refBefore === true && unrefed === false && rerefed === true"
):
    Ok(JsValue.Boolean(usable)):
        expect(usable).to_equal(true)
    _:
        fail("Expected timer handle methods to remain usable")

expect(runtime.drain_due_timers(10)).to_equal(1)
expect(runtime.interpreter.timer_handle_ids.len()).to_equal(0)
match runtime.eval(
    "refreshed.unref(); var completedUnrefed = refreshed.hasRef(); refreshed.ref(); numericId === refreshed.valueOf() && completedUnrefed === false && refreshed.hasRef() === true"
):
    Ok(JsValue.Boolean(usable)):
        expect(usable).to_equal(true)
    _:
        fail("Expected completed timer handle methods to remain usable")
match runtime.eval("refreshed.refresh() === refreshed"):
    Ok(JsValue.Boolean(same_handle)):
        expect(same_handle).to_equal(true)
    _:
        fail("Expected refresh to return the completed handle")
expect(runtime.interpreter.timer_handle_ids.len()).to_equal(1)
expect(runtime.interpreter.timer_handle_object_ids.len()).to_equal(1)
match runtime.eval(
    "refreshed.scheduledAt + ':' + refreshed.refreshedAt + ':' + refreshed.dueAt + ':' + refreshed.active + ':' + refreshed.completed"
):
    Ok(JsValue.String(metadata)):
        expect(metadata).to_equal("10:10:20:true:false")
    _:
        fail("Expected refreshed timeout deadlines from the current clock")

expect(runtime.drain_due_timers(19)).to_equal(0)
expect(runtime.drain_due_timers(20)).to_equal(1)
expect(runtime.drain_due_timers(21)).to_equal(0)
expect(runtime.interpreter.timer_handle_ids.len()).to_equal(0)
expect(runtime.interpreter.timer_handle_object_ids.len()).to_equal(0)
match runtime.eval(
    "refreshTicks + ':' + refreshed.fireCount + ':' + refreshed.active + ':' + refreshed.completed"
):
    Ok(JsValue.String(metadata)):
        expect(metadata).to_equal("2:2:false:true")
    _:
        fail("Expected refreshed timeout to fire once and retire")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/js_timer_drain_limit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JavaScript timer drain limit.
- JavaScript timer drain limit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `27d3c456255a56c0ad5f373862bcf907ab471fd475008e4d40171487b06d6fe1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `27d3c456255a56c0ad5f373862bcf907ab471fd475008e4d40171487b06d6fe1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `27d3c456255a56c0ad5f373862bcf907ab471fd475008e4d40171487b06d6fe1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/js_timer_drain_limit_spec.spl
mirror: doc/06_spec/01_unit/lib/common/js_timer_drain_limit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/js_timer_drain_limit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/js_timer_drain_limit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/js_timer_drain_limit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 47 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/js_timer_drain_limit_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mutates the active timer queues without replacement arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/js_timer_drain_limit_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not allocate Node timer handles in browser mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/js_timer_drain_limit_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'coalesces an overdue interval to one callback per clock advance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

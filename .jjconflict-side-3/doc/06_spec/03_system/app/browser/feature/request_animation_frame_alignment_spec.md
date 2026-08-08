# requestAnimationFrame Boundary Alignment

> BrowserSession and the canonical JavaScript timer owner align staggered
> requestAnimationFrame registrations to one document-clock refresh boundary.
> A callback registered during dispatch waits for the following boundary, and
> timer clears cannot cancel animation-frame callbacks (or vice versa).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

## At a Glance

| Field | Value |
|-------|-------|
| Status | Active source; qualified execution held |
| Requirements | REQ-WEB-BROWSER-004, 005, 006, 017, 021 |
| Plan | `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md` |
| Source | `test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl` |
| Updated | 2026-07-31 |

## Claim Boundary

This scenario proves deterministic BrowserSession-clock scheduling, exact
JavaScript callback timestamps, cancellation, bounded retained work after each
frame, canonical HTML Draw IR, and exact software Engine2D pixels. It does not
claim native execution until the focused spec runs on an admitted current
pure-Simple CLI.

## Scenario

### should keep timer and animation-frame cancellation domains separate

1. **Register the browser callback**
   - The page registers one rAF, one 16 ms timeout, and a once-only click
     listener. `clearTimeout(rAF)` and `cancelAnimationFrame(timeout)` must be
     no-ops, leaving exactly two pending callbacks.
   - Cancellation domains are exact: timeout and interval share one domain,
     rAF is separate, immediate is separate, and nextTick is never removable by
     a public clear API. Pairwise wrong-kind calls are no-ops.
   - Positive controls cross-clear timeout/interval, clear rAF and immediate
     with their matching APIs, and close rAF/immediate through unrestricted
     `handle.close()`.
   - Node-compatible wrong-kind handles remain `active=true`, `closed=false`,
     `cleared=false`, and keep an empty `clearedBy`. The retained task split is
     exactly two timers, one immediate, one rAF, and one nextTick.
   - The checker captures the actual owner-issued nextTick task ID, invokes all
     four public clear APIs against that ID one at a time, and after every call
     requires both five pending tasks and the same nextTick task to remain.
2. **Advance the monotonic browser clock**
   - At 15 ms no callback runs and state remains exactly `:0:-1`.
   - The Node control drains nextTick before immediate at time zero (`NM`), then
     rAF and two timers in creation order at 16 ms (`NMFTU`).
3. **Dispatch events and animation frames**
   - Two click dispatches invoke the once listener exactly once.
   - At 16 ms the rAF and timeout both run in registration order, producing
     exact state `FT:1:16`.
4. **Observe updated canonical Draw IR pixels and released resources**
   - The DOM style mutation lowers through the `html_ast` Draw IR batch as the
     `stage` rectangle at `(0,0)`, size `32x24`, color `#2563eb`.
   - The full `64x48` Engine2D buffer is exact: 768 stage pixels are blue and
     every one of the remaining 2,304 pixels is white, with no skipped command.
   - Pending tasks, timer-handle lookups, pending listener-operation arrays,
     and active listeners are zero. The once-listener tombstone holds an
     undefined callback, proving the callable was released.

### should align staggered and nested callbacks to deterministic frames

1. **Schedule staggered callbacks before one refresh**
   - `setup_raf_alignment_fixture` schedules one callback at document time zero,
     cancels a sibling handle, and schedules another callback from a 5 ms timer.
   - `check_shared_frame_deadline` requires exactly two retained rAF tasks and
     the exact shared deadline `16`.
2. **Advance to the shared frame boundary**
   - `advance_time(16)` must dispatch exactly two callbacks.
   - Both callbacks observe timestamp `16`; the canceled callback is absent.
3. **Schedule a callback during dispatch**
   - The first callback registers a nested callback while the 16 ms frame is
     dispatching.
   - `check_nested_callback_deferred` requires that sole retained task to have
     deadline `32`, while the log remains `outer@16;staggered@16;`.
4. **Render two aligned animation frames**
   - `check_aligned_draw_ir_frames` requires the 16 ms frame to contain the
     `stage` Draw IR rectangle at `(0,0)`, size `32x24`, color `#2563eb`.
   - Engine2D must paint exactly 768 blue pixels with no skipped commands.
   - At 32 ms the same canonical path must paint exactly 768 green pixels,
     record `nested@32;`, and leave zero pending timer/rAF tasks.

### should preserve aligned deadlines across clock edge cases

1. **Align a skipped refresh from a nonzero document origin**
   - A document opened at 100 ms aligns staggered tasks to absolute deadline
     116 ms.
   - Advancing directly to 121 ms gives both callbacks timestamp 21; the nested
     callback aligns to 132 ms and receives timestamp 32.
2. **Keep an overflowed nested frame out of the current drain**
   - A callback due at `i64.max` runs once.
   - Its dispatch-created successor has no representable deadline, reports
     `due_at_ms() == -1`, remains retained, and cannot run in the same drain.
3. **Refresh Node-compatible animation handles exactly**
   - Pending refresh metadata is
     `delay=7, scheduledAt=109, dueAt=116, refreshedAt=109`.
   - Completed refresh metadata is
     `delay=16, scheduledAt=116, dueAt=132, refreshedAt=116`.
   - Browser mode remains a numeric-handle API.
4. **Saturate worker wakeup after the drain cap**
   - 1,001 callbacks share the representable `i64.max` deadline.
   - The bounded drain executes 1,000 and retains one due callback.
   - Worker wakeup selection saturates at `i64.max`; it never wraps negative.

<details>
<summary>Executable SSpec</summary>

The runnable source contains the complete fixture and checker implementations.
The displayed scenario invokes each frozen helper directly:

```simple
it "should keep timer and animation-frame cancellation domains separate":
    step("Register the browser callback")
    var session = setup_cancel_domain_fixture()
    check_cancel_domain_registration(session)
    check_node_cancel_domain_handle_metadata()

    step("Advance the monotonic browser clock")
    expect(session.advance_time(15)).to_equal(0)
    expect(_read_js_text(
        session, "callbackLog+':'+clickCount+':'+frameStamp"
    )).to_equal(":0:-1")

    step("Dispatch events and animation frames")
    val _ = session.dispatch_dom_event(
        "stage", "click", true, true
    )
    val _ = session.dispatch_dom_event(
        "stage", "click", true, true
    )
    expect(session.advance_time(16)).to_equal(2)
    expect(_read_js_text(
        session, "callbackLog+':'+clickCount+':'+frameStamp"
    )).to_equal("FT:1:16")

    step("Observe updated canonical Draw IR pixels and released resources")
    check_cancel_domain_pixels_and_resources(session)

it "should align staggered and nested callbacks to deterministic frames":
    step("Schedule staggered callbacks before one refresh")
    var session = setup_raf_alignment_fixture()
    check_shared_frame_deadline(session)

    step("Advance to the shared frame boundary")
    expect(session.advance_time(16)).to_equal(2)

    step("Schedule a callback during dispatch")
    check_nested_callback_deferred(session)

    step("Render two aligned animation frames")
    check_aligned_draw_ir_frames(session)

it "should preserve aligned deadlines across clock edge cases":
    step("Align a skipped refresh from a nonzero document origin")
    check_nonzero_origin_skipped_boundary()

    step("Keep an overflowed nested frame out of the current drain")
    check_overflow_safe_nested_frame()

    step("Refresh Node-compatible animation handles exactly")
    check_node_compatible_raf_refresh_metadata()

    step("Saturate worker wakeup after the drain cap")
    check_worker_wakeup_saturates_after_drain_cap()
```

<details>
<summary>Core shared rendering and timing helper source</summary>

```simple
class RafAlignmentFrame:
    command: DrawIrCommand
    pixels: [u32]
    matching_pixels: i64
    rendered_commands: i32
    skipped_commands: i32
    source_kind: text

pub fn hosted_browser_renderer_safe_wakeup_ms(
    due_ms: i64, current_time_ms: i64
) -> i64:
    """Defer due work without wrapping the final monotonic timestamp."""
    if due_ms > current_time_ms:
        return due_ms
    if current_time_ms == 9223372036854775807:
        return current_time_ms
    current_time_ms + 1

fn _count_color(pixels: [u32], color: u32) -> i64:
    var count: i64 = 0
    for pixel in pixels:
        if pixel == color:
            count = count + 1
    count

fn _read_js_text(session: BrowserSession, expression: text) -> text:
    match session.eval_script(expression):
        Ok(JsValue.String(value)): value
        Ok(_): fail("Expected JavaScript string result for {expression}")
        Err(reason): fail("JavaScript state read failed: {reason}")

fn _render_raf_alignment_frame(
    session: BrowserSession, expected_color: u32
) -> RafAlignmentFrame:
    val width = 64
    val height = 48
    val html = session.render_html_document()
    session.prepare_css_animation_instances_with_html(width, html)
    val result = (
        simple_web_layout_render_html_draw_ir_result_at_time_with_animations_with_images(
            html, width, height,
            session.monotonic_time_ms - session.animation_start_time_ms,
            session.css_animation_instances, session.image_resources
        )
    )
    if result.composition.batches.len() == 0:
        fail("Expected the canonical HTML Draw IR batch")
    var stage: DrawIrCommand? = nil
    for command in result.composition.batches[0].commands:
        if command.component_id == "stage":
            stage = Some(command)
    val selected = match stage:
        Some(command): command
        nil: fail("Expected the aligned animation stage Draw IR command")
    val raster = Engine2dCompositorBackend.create_named(
        width, height, "software"
    )
    val rendered = raster.render_draw_ir_composition_resources(
        result.composition, session.image_resources
    )
    raster.shutdown()
    RafAlignmentFrame(
        command: selected,
        pixels: rendered.pixels,
        matching_pixels: _count_color(rendered.pixels, expected_color),
        rendered_commands: rendered.rendered_command_count,
        skipped_commands: rendered.skipped_command_count,
        source_kind: result.composition.batches[0].source.source_kind
    )

fn _expect_exact_raf_stage_buffer(
    frame: RafAlignmentFrame, stage_color: u32
):
    expect(frame.pixels.len()).to_equal(64 * 48)
    var mismatched_pixels = 0
    var y = 0
    while y < 48:
        var x = 0
        while x < 64:
            val expected = if x < 32 and y < 24:
                stage_color
            else:
                0xFFFFFFFFu32
            if frame.pixels[y * 64 + x] != expected:
                mismatched_pixels = mismatched_pixels + 1
            x = x + 1
        y = y + 1
    expect(mismatched_pixels).to_equal(0)

fn setup_raf_alignment_fixture() -> BrowserSession:
    var session = BrowserSession.new()
    val html = (
        "<!DOCTYPE html><html><head><style>" +
        "#stage{width:32px;height:24px;background-color:#ef4444}" +
        "</style></head><body><div id='stage'></div><script>" +
        "var frameLog='';" +
        "var stage=document.getElementById('stage');" +
        "var canceled=requestAnimationFrame(function(frameTime){" +
        "frameLog=frameLog+'canceled@'+frameTime+';';" +
        "stage.style.backgroundColor='#a855f7';});" +
        "cancelAnimationFrame(canceled);" +
        "requestAnimationFrame(function(frameTime){" +
        "frameLog=frameLog+'outer@'+frameTime+';';" +
        "stage.style.backgroundColor='#2563eb';" +
        "requestAnimationFrame(function(nestedTime){" +
        "frameLog=frameLog+'nested@'+nestedTime+';';" +
        "stage.style.backgroundColor='#16a34a';});});" +
        "setTimeout(function(){requestAnimationFrame(function(frameTime){" +
        "frameLog=frameLog+'staggered@'+frameTime+';';});},5);" +
        "</script></body></html>"
    )
    match session.open_html("https://example.test/raf-alignment", html):
        Ok(_): ()
        Err(reason): fail("rAF alignment fixture failed to open: {reason}")
    expect(session.advance_time(5)).to_equal(1)
    session

fn check_shared_frame_deadline(session: BrowserSession):
    expect(_read_js_text(session, "typeof canceled")).to_equal("number")
    if val Some(state) = session.runtime_state:
        val tasks = state.runtime.interpreter.pending_timer_tasks
        expect(tasks.len()).to_equal(2)
        for task in tasks:
            expect(task.is_animation_frame).to_equal(true)
            expect(task.scheduled_at_ms + task.delay_ms).to_equal(16)
        return
    fail("Expected an active browser JavaScript runtime")

fn check_nested_callback_deferred(session: BrowserSession):
    expect(_read_js_text(session, "frameLog")).to_equal(
        "outer@16;staggered@16;"
    )
    if val Some(state) = session.runtime_state:
        val tasks = state.runtime.interpreter.pending_timer_tasks
        expect(tasks.len()).to_equal(1)
        expect(tasks[0].is_animation_frame).to_equal(true)
        expect(tasks[0].scheduled_at_ms + tasks[0].delay_ms).to_equal(32)
        return
    fail("Expected the nested animation callback to remain document-owned")

fn check_aligned_draw_ir_frames(session: BrowserSession):
    val first = _render_raf_alignment_frame(session, 0xFF2563EBu32)
    expect(first.source_kind).to_equal("html_ast")
    expect(first.command.component_id).to_equal("stage")
    expect(first.command.x).to_equal(0)
    expect(first.command.y).to_equal(0)
    expect(first.command.width).to_equal(32)
    expect(first.command.height).to_equal(24)
    expect(first.command.color).to_equal(0xFF2563EBu32)
    expect(first.matching_pixels).to_equal(32 * 24)
    expect(first.rendered_commands).to_be_greater_than(0)
    expect(first.skipped_commands).to_equal(0)

    expect(session.advance_time(32)).to_equal(1)
    val second = _render_raf_alignment_frame(session, 0xFF16A34Au32)
    expect(second.source_kind).to_equal("html_ast")
    expect(second.command.component_id).to_equal("stage")
    expect(second.command.x).to_equal(0)
    expect(second.command.y).to_equal(0)
    expect(second.command.width).to_equal(32)
    expect(second.command.height).to_equal(24)
    expect(second.command.color).to_equal(0xFF16A34Au32)
    expect(second.matching_pixels).to_equal(32 * 24)
    expect(second.rendered_commands).to_be_greater_than(0)
    expect(second.skipped_commands).to_equal(0)
    expect(_read_js_text(session, "frameLog")).to_equal(
        "outer@16;staggered@16;nested@32;"
    )
    if val Some(state) = session.runtime_state:
        expect(state.runtime.interpreter.pending_timer_tasks.len()).to_equal(0)
    else:
        fail("Expected the aligned frame runtime to remain active")

fn check_nonzero_origin_skipped_boundary():
    var session = BrowserSession.new()
    expect(session.advance_time(100)).to_equal(0)
    val html = (
        "<html><body><script>var frameLog='';" +
        "requestAnimationFrame(function(frameTime){" +
        "frameLog=frameLog+'outer@'+frameTime+';';" +
        "requestAnimationFrame(function(nestedTime){" +
        "frameLog=frameLog+'nested@'+nestedTime+';';});});" +
        "setTimeout(function(){requestAnimationFrame(function(frameTime){" +
        "frameLog=frameLog+'staggered@'+frameTime+';';});},5);" +
        "</script></body></html>"
    )
    expect(session.open_html(
        "https://example.test/raf-nonzero-origin", html
    ).is_ok()).to_equal(true)
    expect(session.advance_time(105)).to_equal(1)
    if val Some(state) = session.runtime_state:
        val tasks = state.runtime.interpreter.pending_timer_tasks
        expect(tasks.len()).to_equal(2)
        for task in tasks:
            expect(task.due_at_ms()).to_equal(116)
    else:
        fail("Expected nonzero-origin rAF tasks")
    expect(session.advance_time(121)).to_equal(2)
    expect(_read_js_text(session, "frameLog")).to_equal(
        "outer@21;staggered@21;"
    )
    if val Some(state) = session.runtime_state:
        val tasks = state.runtime.interpreter.pending_timer_tasks
        expect(tasks.len()).to_equal(1)
        expect(tasks[0].due_at_ms()).to_equal(132)
    else:
        fail("Expected skipped-boundary nested rAF task")
    expect(session.advance_time(132)).to_equal(1)
    expect(_read_js_text(session, "frameLog")).to_equal(
        "outer@21;staggered@21;nested@32;"
    )

fn check_overflow_safe_nested_frame():
    var runtime = JsRuntime.new_browser(
        Logger.new("raf-overflow", LogLevel.Error)
    )
    runtime.interpreter.timer_time_origin_ms = 9223372036854775791
    runtime.interpreter.timer_current_time_ms = 9223372036854775791
    expect(runtime.eval(
        "var frames=0;var stamp=-1;" +
        "function frame(frameTime){frames=frames+1;stamp=frameTime;" +
        "if(frames<2){requestAnimationFrame(frame);}}" +
        "requestAnimationFrame(frame);"
    ).is_ok()).to_equal(true)
    expect(runtime.drain_due_timers(9223372036854775807)).to_equal(1)
    expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(1)
    expect(
        runtime.interpreter.pending_timer_tasks[0].due_at_ms()
    ).to_equal(-1)
    expect(runtime.drain_due_timers(9223372036854775807)).to_equal(0)
    match runtime.eval("frames+':'+stamp"):
        Ok(JsValue.String(value)): expect(value).to_equal("1:16")
        Ok(_): fail("Expected overflow rAF state text")
        Err(reason): fail("Overflow rAF state read failed: {reason}")

fn check_node_compatible_raf_refresh_metadata():
    var runtime = JsRuntime.new(
        Logger.new("raf-refresh-metadata", LogLevel.Error)
    )
    runtime.interpreter.timer_time_origin_ms = 100
    runtime.interpreter.timer_current_time_ms = 105
    expect(runtime.eval(
        "var frameTimes='';var handle=requestAnimationFrame(" +
        "function(frameTime){frameTimes=frameTimes+frameTime+';';});"
    ).is_ok()).to_equal(true)
    runtime.interpreter.timer_current_time_ms = 109
    match runtime.eval("handle.refresh()===handle"):
        Ok(JsValue.Boolean(value)): expect(value).to_equal(true)
        Ok(_): fail("Expected pending rAF refresh identity")
        Err(reason): fail("Pending rAF refresh failed: {reason}")
    match runtime.eval(
        "handle.delay+':'+handle.scheduledAt+':'+handle.dueAt+':'+" +
        "handle.refreshedAt"
    ):
        Ok(JsValue.String(value)): expect(value).to_equal("7:109:116:109")
        Ok(_): fail("Expected pending rAF refresh metadata text")
        Err(reason): fail("Pending rAF refresh metadata failed: {reason}")
    expect(runtime.drain_due_timers(116)).to_equal(1)
    match runtime.eval(
        "handle.active+':'+handle.completed+':'+handle.lastFiredAt"
    ):
        Ok(JsValue.String(value)): expect(value).to_equal("false:true:116")
        Ok(_): fail("Expected completed rAF metadata text")
        Err(reason): fail("Completed rAF metadata failed: {reason}")
    match runtime.eval("handle.refresh()===handle"):
        Ok(JsValue.Boolean(value)): expect(value).to_equal(true)
        Ok(_): fail("Expected completed rAF refresh identity")
        Err(reason): fail("Completed rAF refresh failed: {reason}")
    match runtime.eval(
        "handle.delay+':'+handle.scheduledAt+':'+handle.dueAt+':'+" +
        "handle.refreshedAt"
    ):
        Ok(JsValue.String(value)): expect(value).to_equal("16:116:132:116")
        Ok(_): fail("Expected completed rAF refresh metadata text")
        Err(reason): fail("Completed rAF refresh metadata failed: {reason}")
    expect(runtime.drain_due_timers(132)).to_equal(1)
    match runtime.eval("frameTimes"):
        Ok(JsValue.String(value)): expect(value).to_equal("16;32;")
        Ok(_): fail("Expected refreshed rAF timestamp text")
        Err(reason): fail("Refreshed rAF timestamp read failed: {reason}")

fn check_worker_wakeup_saturates_after_drain_cap():
    var session = BrowserSession.new()
    expect(session.advance_time(9223372036854775791)).to_equal(0)
    expect(session.open_html(
        "https://example.test/raf-worker-wakeup-cap",
        "<html><body><script>function noop(){}" +
        "for(var i=0;i<1001;i=i+1){" +
        "requestAnimationFrame(noop);}</script></body></html>"
    ).is_ok()).to_equal(true)
    expect(session.advance_time(9223372036854775807)).to_equal(1000)
    val remaining_due = session.next_script_timer_due_ms()
    expect(remaining_due).to_equal(9223372036854775807)
    val wakeup = hosted_browser_renderer_safe_wakeup_ms(
        remaining_due, 9223372036854775807
    )
    expect(wakeup).to_equal(9223372036854775807)
    expect(wakeup).to_be_greater_than(-1)
    if val Some(state) = session.runtime_state:
        expect(
            state.runtime.interpreter.pending_timer_tasks.len()
        ).to_equal(1)
    else:
        fail("Expected one capped rAF task to remain document-owned")
```

</details>

Complete executable source:
`test/03_system/app/browser/feature/request_animation_frame_alignment_spec.spl`.

</details>

</details>

# Browser Script History Traversal

> Proves page script history traversal is owned by the canonical BrowserSession

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Script History Traversal

Proves page script history traversal is owned by the canonical BrowserSession

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves page script history traversal is owned by the canonical BrowserSession
ledger and restores the same document, browser controls, Draw IR, and Engine2D
pixels as browser chrome traversal.

## Scenarios

### Browser page-script history traversal

#### should restore committed pages through canonical history and rendering

- should restore committed pages through canonical history and rendering
   - GUI capture: after_step (HTML preferred when available)
- Enter and commit a destination
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: session.current_url equals `HISTORY_SECOND_URL`
   - Expected: session.current_title equals `Second`
- Record the navigation entry
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 6 expected checks
   - Expected: session.history.len() equals `2`
   - Expected: session.current_index equals `1`
   - Expected: session.history[0].url equals `HISTORY_FIRST_URL`
   - Expected: session.history[0].title equals `First`
   - Expected: session.history[1].url equals `HISTORY_SECOND_URL`
   - Expected: session.history[1].title equals `Second`
- Move backward forward or stop
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 10 expected checks
   - Expected: session.current_index equals `0`
   - Expected: session.current_url equals `HISTORY_FIRST_URL`
   - Expected: session.current_title equals `First`
   - Expected: session.current_index equals `0`
   - Expected: session.current_url equals `HISTORY_FIRST_URL`
   - Expected: session.current_index equals `1`
   - Expected: session.current_url equals `HISTORY_SECOND_URL`
   - Expected: session.current_title equals `Second`
   - Expected: session.current_index equals `1`
   - Expected: session.current_url equals `HISTORY_SECOND_URL`
- Render the restored document and controls
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 14 expected checks
   - Expected: back_commands[first_index].kind equals `rect`
   - Expected: back_commands[first_index].x equals `0`
   - Expected: back_commands[first_index].y equals `0`
   - Expected: back_commands[first_index].width equals `16`
   - Expected: back_commands[first_index].height equals `16`
   - Expected: back_commands[first_index].color equals `0xFF00FF00u32`
   - Expected: back_rendered.skipped_command_count equals `0`
   - Expected: forward_commands[second_index].kind equals `rect`
   - Expected: forward_commands[second_index].x equals `0`
   - Expected: forward_commands[second_index].y equals `0`
   - Expected: forward_commands[second_index].width equals `16`
   - Expected: forward_commands[second_index].height equals `16`
   - Expected: forward_commands[second_index].color equals `0xFF0000FFu32`
   - Expected: forward_rendered.skipped_command_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 136 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should restore committed pages through canonical history and rendering")
step("Enter and commit a destination")
var session = BrowserSession.new()
expect(session.open_html(
    HISTORY_FIRST_URL, HISTORY_FIRST_HTML
).is_ok()).to_be(true)
session.register_resource(HISTORY_SECOND_URL, HISTORY_SECOND_HTML)
val address_edit = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "set_value",
    text_value: HISTORY_SECOND_URL, x: 0, y: 0
))
val address_submit = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "submit",
    text_value: "", x: 0, y: 0
))
expect(address_edit.ok).to_be(true)
expect(address_submit.ok).to_be(true)
expect(session.current_url).to_equal(HISTORY_SECOND_URL)
expect(session.current_title).to_equal("Second")
expect(session.current_body_html).to_contain("Second page")

step("Record the navigation entry")
expect(session.history.len()).to_equal(2)
expect(session.current_index).to_equal(1)
expect(session.history[0].url).to_equal(HISTORY_FIRST_URL)
expect(session.history[0].title).to_equal("First")
expect(session.history[1].url).to_equal(HISTORY_SECOND_URL)
expect(session.history[1].title).to_equal("Second")

step("Move backward forward or stop")
match session.eval_script("history.back()"):
    Ok(_): ()
    Err(reason): fail("history.back evaluation failed: {reason}")
expect(session.current_index).to_equal(0)
expect(session.current_url).to_equal(HISTORY_FIRST_URL)
expect(session.current_title).to_equal("First")
expect(session.current_body_html).to_contain("First page")
val back_snapshot = session.ui_access_snapshot()
expect(ui_access_find_nodes(
    back_snapshot, "browser:session", "button", "Back", 1
)[0].enabled).to_be(false)
expect(ui_access_find_nodes(
    back_snapshot, "browser:session", "button", "Forward", 1
)[0].enabled).to_be(true)
expect(ui_access_find_nodes(
    back_snapshot, "browser:session", "button", "Stop", 1
)[0].enabled).to_be(false)
expect(ui_access_find_nodes(
    back_snapshot, "browser:session", "textfield",
    HISTORY_FIRST_URL, 1
).len()).to_equal(1)
match session.eval_script("history.back()"):
    Ok(_): ()
    Err(reason): fail("bounded history.back evaluation failed: {reason}")
expect(session.current_index).to_equal(0)
expect(session.current_url).to_equal(HISTORY_FIRST_URL)
val back_composition = simple_web_layout_render_html_draw_ir_with_images(
    session.render_html_document(), 32, 24, session.image_resources
)
val back_raster = Engine2dCompositorBackend.create_named(
    32, 24, "software"
)
val back_rendered = back_raster.render_draw_ir_composition(
    back_composition, []
)
back_raster.shutdown()

match session.eval_script("history.forward()"):
    Ok(_): ()
    Err(reason): fail("history.forward evaluation failed: {reason}")
expect(session.current_index).to_equal(1)
expect(session.current_url).to_equal(HISTORY_SECOND_URL)
expect(session.current_title).to_equal("Second")
expect(session.current_body_html).to_contain("Second page")
val forward_snapshot = session.ui_access_snapshot()
expect(ui_access_find_nodes(
    forward_snapshot, "browser:session", "button", "Back", 1
)[0].enabled).to_be(true)
expect(ui_access_find_nodes(
    forward_snapshot, "browser:session", "button", "Forward", 1
)[0].enabled).to_be(false)
expect(ui_access_find_nodes(
    forward_snapshot, "browser:session", "button", "Stop", 1
)[0].enabled).to_be(false)
expect(ui_access_find_nodes(
    forward_snapshot, "browser:session", "textfield",
    HISTORY_SECOND_URL, 1
).len()).to_equal(1)
match session.eval_script("history.forward()"):
    Ok(_): ()
    Err(reason): fail("bounded history.forward evaluation failed: {reason}")
expect(session.current_index).to_equal(1)
expect(session.current_url).to_equal(HISTORY_SECOND_URL)

step("Render the restored document and controls")
expect(back_composition.batches.len()).to_be_greater_than(0)
expect(
    back_composition.batches[0].source.source_kind
).to_equal("html_ast")
val back_commands = back_composition.batches[0].commands
val first_index = _history_command_index(back_commands, "first")
expect(first_index).to_be_greater_than(-1)
expect(back_commands[first_index].kind).to_equal("rect")
expect(back_commands[first_index].x).to_equal(0)
expect(back_commands[first_index].y).to_equal(0)
expect(back_commands[first_index].width).to_equal(16)
expect(back_commands[first_index].height).to_equal(16)
expect(back_commands[first_index].color).to_equal(0xFF00FF00u32)
expect(back_rendered.skipped_command_count).to_equal(0)
_expect_history_full_buffer(back_rendered.pixels, 0xFF00FF00u32)
val forward_composition = simple_web_layout_render_html_draw_ir_with_images(
    session.render_html_document(), 32, 24, session.image_resources
)
expect(forward_composition.batches.len()).to_be_greater_than(0)
expect(
    forward_composition.batches[0].source.source_kind
).to_equal("html_ast")
val forward_commands = forward_composition.batches[0].commands
val second_index = _history_command_index(forward_commands, "second")
expect(second_index).to_be_greater_than(-1)
expect(forward_commands[second_index].kind).to_equal("rect")
expect(forward_commands[second_index].x).to_equal(0)
expect(forward_commands[second_index].y).to_equal(0)
expect(forward_commands[second_index].width).to_equal(16)
expect(forward_commands[second_index].height).to_equal(16)
expect(forward_commands[second_index].color).to_equal(0xFF0000FFu32)
val forward_raster = Engine2dCompositorBackend.create_named(
    32, 24, "software"
)
val forward_rendered = forward_raster.render_draw_ir_composition(
    forward_composition, []
)
forward_raster.shutdown()
expect(forward_rendered.skipped_command_count).to_equal(0)
_expect_history_full_buffer(forward_rendered.pixels, 0xFF0000FFu32)
```

</details>

#### should defer page-script traversal until the loader unwinds

- should defer page-script traversal until the loader unwinds
   - Protocol capture: after_step
- Commit two pages before loading a scripted destination
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: session.history.len() equals `2`
   - Expected: session.current_index equals `1`
- Request Back from the destination inline script
   - Protocol capture: after_step
- Finalize the destination before restoring the prior page
   - Protocol capture: after_step
   - Evidence: protocol response verified by 12 expected checks
   - Expected: session.current_index equals `1`
   - Expected: session.current_url equals `HISTORY_SECOND_URL`
   - Expected: session.current_title equals `Second`
   - Expected: session.local_storage_item("thirdRuns") ?? "" equals `1`
   - Expected: session.history.len() equals `3`
   - Expected: session.history[2].url equals `HISTORY_THIRD_URL`
   - Expected: session.history[2].title equals `Third Script`
   - Expected: session.history_proposal_action equals ``
   - Expected: session.history_proposal_url_kind equals `O`
   - Expected: session.history_proposal_raw_url equals ``
   - Expected: session.pending_history_traversal_delta equals `0`
   - Expected: delta equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should defer page-script traversal until the loader unwinds")
step("Commit two pages before loading a scripted destination")
var session = BrowserSession.new()
match session.open_html(HISTORY_FIRST_URL, HISTORY_FIRST_HTML):
    Ok(_): ()
    Err(reason): fail("first page failed: {reason}")
match session.open_html(HISTORY_SECOND_URL, HISTORY_SECOND_HTML):
    Ok(_): ()
    Err(reason): fail("second page failed: {reason}")
expect(session.history.len()).to_equal(2)
expect(session.current_index).to_equal(1)

step("Request Back from the destination inline script")
match session.open_html(
    HISTORY_THIRD_URL, HISTORY_SCRIPTED_THIRD_HTML
):
    Ok(_): ()
    Err(reason): fail("scripted destination failed: {reason}")

step("Finalize the destination before restoring the prior page")
expect(session.current_index).to_equal(1)
expect(session.current_url).to_equal(HISTORY_SECOND_URL)
expect(session.current_title).to_equal("Second")
expect(session.current_body_html).to_contain("Second page")
expect(session.local_storage_item("thirdRuns") ?? "").to_equal("1")
expect(session.history.len()).to_equal(3)
expect(session.history[2].url).to_equal(HISTORY_THIRD_URL)
expect(session.history[2].title).to_equal("Third Script")
match session.eval_script("'runtime-alive'"):
    Ok(_): ()
    Err(reason): fail("restored runtime evaluation failed: {reason}")
expect(session.history_proposal_action).to_equal("")
expect(session.history_proposal_url_kind).to_equal("O")
expect(session.history_proposal_raw_url).to_equal("")
expect(session.pending_history_traversal_delta).to_equal(0)
expect(session.active_load).to_be_nil()
match session.eval_script("history.__simple_traversal_delta"):
    Ok(JsValue.Number(delta)):
        expect(delta).to_equal(0.0)
    Ok(_): fail("history traversal proposal was not numeric")
    Err(reason): fail("history proposal inspection failed: {reason}")
```

</details>

#### should queue a restored inline traversal without recursive ping-pong

- should queue a restored inline traversal without recursive ping-pong
   - Protocol capture: after_step
- Commit pages whose restored scripts request opposite traversal
   - Protocol capture: after_step
- Observe the restored request queued after the outer Back unwinds
   - Protocol capture: after_step
   - Evidence: protocol response verified by 5 expected checks
   - Expected: session.current_index equals `0`
   - Expected: session.current_url equals `HISTORY_FIRST_URL`
   - Expected: session.local_storage_item("firstRuns") ?? "" equals `2`
   - Expected: session.local_storage_item("secondRuns") ?? "" equals `1`
   - Expected: session.pending_history_traversal_delta equals `1`
- Pump the queued Forward exactly once on the next outer operation
   - Protocol capture: after_step
   - Evidence: protocol response verified by 6 expected checks
   - Expected: value equals `outer-unwound`
   - Expected: session.current_index equals `1`
   - Expected: session.current_url equals `HISTORY_SECOND_URL`
   - Expected: session.local_storage_item("firstRuns") ?? "" equals `2`
   - Expected: session.local_storage_item("secondRuns") ?? "" equals `2`
   - Expected: session.pending_history_traversal_delta equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should queue a restored inline traversal without recursive ping-pong")
step("Commit pages whose restored scripts request opposite traversal")
var session = BrowserSession.new()
match session.open_html(HISTORY_FIRST_URL, HISTORY_RESTORED_FIRST_HTML):
    Ok(_): ()
    Err(reason): fail("first scripted page failed: {reason}")
match session.open_html(HISTORY_SECOND_URL, HISTORY_BACK_SECOND_HTML):
    Ok(_): ()
    Err(reason): fail("second scripted page failed: {reason}")

step("Observe the restored request queued after the outer Back unwinds")
expect(session.current_index).to_equal(0)
expect(session.current_url).to_equal(HISTORY_FIRST_URL)
expect(session.local_storage_item("firstRuns") ?? "").to_equal("2")
expect(session.local_storage_item("secondRuns") ?? "").to_equal("1")
expect(session.pending_history_traversal_delta).to_equal(1)
expect(session.history_traversal_pump_active).to_be(false)
expect(session.active_load).to_be_nil()

step("Pump the queued Forward exactly once on the next outer operation")
match session.eval_script("'outer-unwound'"):
    Ok(JsValue.String(value)):
        expect(value).to_equal("outer-unwound")
    Ok(_): fail("outer operation returned an unexpected value")
    Err(reason): fail("outer operation failed: {reason}")
expect(session.current_index).to_equal(1)
expect(session.current_url).to_equal(HISTORY_SECOND_URL)
expect(session.local_storage_item("firstRuns") ?? "").to_equal("2")
expect(session.local_storage_item("secondRuns") ?? "").to_equal("2")
expect(session.pending_history_traversal_delta).to_equal(0)
expect(session.history_traversal_pump_active).to_be(false)
expect(session.active_load).to_be_nil()
```

</details>

#### should consume traversal once after an external script completes

- should consume traversal once after an external script completes
   - Protocol capture: after_step
- Suspend a queued Back on an external script response
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: session.pending_history_traversal_delta equals `-1`
- Complete the external script before restoring the prior page
   - Protocol capture: after_step
   - Evidence: protocol response verified by 6 expected checks
   - Expected: session.current_index equals `1`
   - Expected: session.current_url equals `HISTORY_SECOND_URL`
   - Expected: session.history.len() equals `3`
   - Expected: session.history[2].url equals `HISTORY_THIRD_URL`
   - Expected: session.local_storage_item("externalRuns") ?? "" equals `1`
   - Expected: session.pending_history_traversal_delta equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should consume traversal once after an external script completes")
step("Suspend a queued Back on an external script response")
var session = BrowserSession.new()
match session.open_html(HISTORY_FIRST_URL, HISTORY_FIRST_HTML):
    Ok(_): ()
    Err(reason): fail("first page failed: {reason}")
match session.open_html(HISTORY_SECOND_URL, HISTORY_SECOND_HTML):
    Ok(_): ()
    Err(reason): fail("second page failed: {reason}")
match session.open_html(HISTORY_THIRD_URL, HISTORY_SUSPENDED_THIRD_HTML):
    Ok(_): ()
    Err(reason): fail("suspended destination failed: {reason}")
val script_request = session.take_pending_request().unwrap()
expect(session.pending_history_traversal_delta).to_equal(-1)

step("Complete the external script before restoring the prior page")
match session.commit_network_response(BrowserResponse.create(
    request_id: script_request.id, kind: script_request.kind,
    url: script_request.url, status: 200,
    headers: "Content-Type: application/javascript",
    body: "localStorage.setItem('externalRuns','1');", error: ""
)):
    Ok(_): ()
    Err(reason): fail("external script response failed: {reason}")
expect(session.current_index).to_equal(1)
expect(session.current_url).to_equal(HISTORY_SECOND_URL)
expect(session.history.len()).to_equal(3)
expect(session.history[2].url).to_equal(HISTORY_THIRD_URL)
expect(session.local_storage_item("externalRuns") ?? "").to_equal("1")
expect(session.pending_history_traversal_delta).to_equal(0)
expect(session.history_traversal_pump_active).to_be(false)
expect(session.active_load).to_be_nil()
```

</details>

<details>
<summary>Advanced: should cancel traversal queued by a replaced suspended load</summary>

#### should cancel traversal queued by a replaced suspended load

- should cancel traversal queued by a replaced suspended load
- Commit two pages before a suspended scripted destination
- Queue Back before suspending on an external script
   - Expected: session.pending_history_traversal_delta equals `-1`
- Replace the load without consuming its stale traversal
   - Expected: session.current_url equals `HISTORY_REPLACEMENT_URL`
   - Expected: session.current_title equals `Replacement`
   - Expected: session.current_index equals `2`
   - Expected: session.history.len() equals `3`
   - Expected: session.pending_history_traversal_delta equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cancel traversal queued by a replaced suspended load")
step("Commit two pages before a suspended scripted destination")
var session = BrowserSession.new()
match session.open_html(HISTORY_FIRST_URL, HISTORY_FIRST_HTML):
    Ok(_): ()
    Err(reason): fail("first page failed: {reason}")
match session.open_html(HISTORY_SECOND_URL, HISTORY_SECOND_HTML):
    Ok(_): ()
    Err(reason): fail("second page failed: {reason}")

step("Queue Back before suspending on an external script")
match session.open_html(
    HISTORY_THIRD_URL, HISTORY_SUSPENDED_THIRD_HTML
):
    Ok(_): ()
    Err(reason): fail("suspended destination failed: {reason}")
match session.active_load:
    Some(_): ()
    nil: fail("external script did not suspend the active load")
expect(session.pending_history_traversal_delta).to_equal(-1)

step("Replace the load without consuming its stale traversal")
match session.open_html(
    HISTORY_REPLACEMENT_URL,
    "<html><head><title>Replacement</title></head>" +
    "<body>Replacement page</body></html>"
):
    Ok(_): ()
    Err(reason): fail("replacement page failed: {reason}")
expect(session.current_url).to_equal(HISTORY_REPLACEMENT_URL)
expect(session.current_title).to_equal("Replacement")
expect(session.current_index).to_equal(2)
expect(session.history.len()).to_equal(3)
expect(session.pending_history_traversal_delta).to_equal(0)
expect(session.active_load).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: should clear suspended traversal on Stop and Close</summary>

#### should clear suspended traversal on Stop and Close

- should clear suspended traversal on Stop and Close
- Stop one suspended traversal without navigating Back
   - Expected: stopped.pending_history_traversal_delta equals `-1`
   - Expected: stopped.current_index equals `1`
   - Expected: stopped.pending_history_traversal_delta equals `0`
- Close another suspended traversal without navigating Back
   - Expected: closed.pending_history_traversal_delta equals `-1`
   - Expected: closed.current_index equals `0`
   - Expected: closed.pending_history_traversal_delta equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should clear suspended traversal on Stop and Close")
step("Stop one suspended traversal without navigating Back")
var stopped = BrowserSession.new()
match stopped.open_html(HISTORY_FIRST_URL, HISTORY_FIRST_HTML):
    Ok(_): ()
    Err(reason): fail("stopped first page failed: {reason}")
match stopped.open_html(HISTORY_SECOND_URL, HISTORY_SUSPENDED_THIRD_HTML):
    Ok(_): ()
    Err(reason): fail("stopped suspended page failed: {reason}")
expect(stopped.pending_history_traversal_delta).to_equal(-1)
stopped.stop_loading()
expect(stopped.current_index).to_equal(1)
expect(stopped.pending_history_traversal_delta).to_equal(0)
expect(stopped.active_load).to_be_nil()

step("Close another suspended traversal without navigating Back")
var closed = BrowserSession.new()
match closed.open_html(HISTORY_FIRST_URL, HISTORY_FIRST_HTML):
    Ok(_): ()
    Err(reason): fail("closed first page failed: {reason}")
match closed.open_html(HISTORY_SECOND_URL, HISTORY_SUSPENDED_THIRD_HTML):
    Ok(_): ()
    Err(reason): fail("closed suspended page failed: {reason}")
expect(closed.pending_history_traversal_delta).to_equal(-1)
closed.close()
expect(closed.current_index).to_equal(0)
expect(closed.pending_history_traversal_delta).to_equal(0)
expect(closed.history_traversal_pump_active).to_be(false)
expect(closed.active_load).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: should deny script traversal without CSP top-navigation capability</summary>

#### should deny script traversal without CSP top-navigation capability

- should deny script traversal without CSP top-navigation capability
- Load a script-enabled sandbox without top-navigation
- Keep the sandboxed page and clear the denied proposal
   - Expected: session.current_index equals `1`
   - Expected: session.current_url equals `HISTORY_SECOND_URL`
   - Expected: session.pending_history_traversal_delta equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should deny script traversal without CSP top-navigation capability")
step("Load a script-enabled sandbox without top-navigation")
var session = BrowserSession.new()
match session.open_html(HISTORY_FIRST_URL, HISTORY_FIRST_HTML):
    Ok(_): ()
    Err(reason): fail("sandbox first page failed: {reason}")
match session.begin_network_navigation(
    HISTORY_SECOND_URL, "GET", "", "", ""
):
    Ok(_): ()
    Err(reason): fail("sandbox navigation failed: {reason}")
val document_request = session.take_pending_request().unwrap()
match session.commit_network_response(BrowserResponse.create(
    request_id: document_request.id, kind: "document",
    url: document_request.url, status: 200,
    headers: "Content-Security-Policy: sandbox allow-scripts",
    body: "<html><head><title>Sandboxed</title></head><body>" +
        "<script>history.back();</script></body></html>", error: ""
)):
    Ok(_): ()
    Err(reason): fail("sandbox response failed: {reason}")

step("Keep the sandboxed page and clear the denied proposal")
expect(session.current_index).to_equal(1)
expect(session.current_url).to_equal(HISTORY_SECOND_URL)
expect(session.csp_sandbox_policy.allow_scripts).to_be(true)
expect(session.csp_sandbox_policy.allow_top_navigation).to_be(false)
expect(session.warnings.join("|")).to_contain(
    "CSP sandbox blocked history traversal"
)
expect(session.pending_history_traversal_delta).to_equal(0)
expect(session.history_traversal_pump_active).to_be(false)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2569003af13c8957a902f2bcd785ebeb69cf55e06103d948cd24a28b88ebda76`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2569003af13c8957a902f2bcd785ebeb69cf55e06103d948cd24a28b88ebda76`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2569003af13c8957a902f2bcd785ebeb69cf55e06103d948cd24a28b88ebda76`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_script_history_traversal_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_script_history_traversal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_script_history_traversal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 42 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should restore committed pages through canonical history and rendering' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should restore committed pages through canonical history and rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl:238:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should defer page-script traversal until the loader unwinds' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should defer page-script traversal until the loader unwinds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl:285:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should queue a restored inline traversal without recursive ping-pong' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl:285:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should queue a restored inline traversal without recursive ping-pong' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl:323:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should consume traversal once after an external script completes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl:360:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cancel traversal queued by a replaced suspended load' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/browser/feature/browser_script_history_traversal_spec.spl:400:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clear suspended traversal on Stop and Close' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

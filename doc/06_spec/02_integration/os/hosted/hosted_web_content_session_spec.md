# Hosted Web Content Session Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Web Content Session Specification

## Scenarios

### hosted Web content session

#### applies CSS and advances Simple Script and JavaScript animation on the host clock

- Simple Script creates the CSS-targeted red first frame.
- The host monotonic clock keeps requestAnimationFrame pending through 15 ms.
- At 16 ms JavaScript mutates the live DOM and Engine2D renders a distinct
  blue frame.

#### fails closed when no semantic element is hit or focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = HostedWebContentSession.create(
    9, "<input id='name' value='ready'>", 80, 40
)
val miss = session.dispatch_pointer_at(1, 100, 100, false)
expect(miss.reason).to_equal("no-semantic-target")
expect(miss.callback_count).to_equal(0)
val unfocused = session.dispatch_text(2, "Ada")
expect(unfocused.reason).to_equal("no-focused-semantic-target")
expect(unfocused.mutation_revision).to_equal(0)
```

</details>

#### carries one compositor-local pointer release through BrowserSession and the canonical Engine2D frame

- var comp = HostCompositor new headless
- 1, 1, COMP CREATE WINDOW to i64
- target unwrap
- target unwrap
- target unwrap
- target unwrap
   - Expected: receipt.event_id equals `17`
   - Expected: receipt.wm_target_id equals `target.unwrap().window_id`
   - Expected: receipt.semantic_target_id equals `accept`
   - Expected: receipt.callback_count equals `1`
   - Expected: receipt.mutation_revision equals `1`
- comp = host compositor update window content
   - Expected: frame.len() equals `240 * 180`
- raster shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = HostCompositor.new_headless(Size(width: 240u64, height: 180u64))
comp.apply_bridge_request(
    1, 1, COMP_CREATE_WINDOW.to_i64(), 0, "Form", 20, 48, 180, 100,
    "<style>input{display:block;width:40px;height:28px;background-color:#ef4444}input[checked]{background-color:#2563eb}</style><input id='accept' type='checkbox'>",
    1, "hosted-web-event"
)
val target = comp.content_target(40, 90)
expect(target.is_some()).to_be(true)

var session = HostedWebContentSession.create(
    target.unwrap().window_id,
    target.unwrap().body_html,
    target.unwrap().width,
    target.unwrap().height
)
val before = session.render_to_pixels()
val receipt = session.dispatch_pointer_at(17, target.unwrap().local_x, target.unwrap().local_y, false)

expect(receipt.event_id).to_equal(17)
expect(receipt.wm_target_id).to_equal(target.unwrap().window_id)
expect(receipt.semantic_target_id).to_equal("accept")
expect(receipt.callback_count).to_equal(1)
expect(receipt.mutation_revision).to_equal(1)
expect(session.current_body_html()).to_contain("checked=\"checked\"")
expect(checksum(session.render_to_pixels()) == checksum(before)).to_be(false)

comp = host_compositor_update_window_content(comp, target.unwrap().window_id, session.current_body_html())
val raster = Engine2dCompositorBackend.create_named(240, 180, "software")
expect(comp.render_frame_engine2d(raster)).to_be(true)
val frame = comp.pure_simple_pixel_buffer()
expect(frame.len()).to_equal(240 * 180)
expect(checksum(frame)).to_be_greater_than(0)
raster.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/hosted/hosted_web_content_session_spec.spl` |
| Updated | 2026-07-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- hosted Web content session

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

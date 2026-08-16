# Tiny Ui Web Wm Specification

> **Stale generated-manual handoff (2026-08-16):** the executable source now has seven scenarios, including three intentional fail-closed blockers for optional descriptor/Vulkan evidence, RV32 R0-R4 evidence, and the S0 409,600-byte closure. This four-scenario generated body is retained only as the last docgen artifact; it is not current PASS evidence. Regenerate only with an admitted pure-Simple runner after the blockers are satisfied. See `doc/08_tracking/bug/tiny_ui_web_wm_integration_blockers_2026-08-14.md`.

> Tests covering Tiny fullscreen browser profile.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tiny Ui Web Wm Specification

## Scenarios

### Tiny fullscreen browser profile

#### presents an admitted page as one fullscreen opaque root

- Boot the bounded Tiny browser profile
   - Expected: browser.install_controls().code equals `0`
- Render the shared nested-pane page fullscreen
   - Expected: receipt.status.code equals `0`
   - Expected: receipt.frame.visible_surfaces equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot the bounded Tiny browser profile")
var browser = TinyBrowser.create(160, 120)
expect(browser.install_controls().code).to_equal(0)

step("Render the shared nested-pane page fullscreen")
val receipt = browser.render_html("<body><div><p>Tiny Browser</p><button>Open</button><input></body>")
expect(receipt.status.code).to_equal(0)
expect(receipt.parsed_nodes).to_be_greater_than(4)
expect(receipt.draw_words).to_be_greater_than(10)
expect(receipt.checksum).to_be_greater_than(0)
expect(receipt.frame.visible_surfaces).to_equal(1)
```

</details>

#### routes keyboard text and pointer events to visible controls

- Navigate controls with keyboard and pointer
   - Expected: browser.dispatch(tab).target_index equals `0`
   - Expected: browser.dispatch(click).target_index equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var browser = TinyBrowser.create(160, 120)
browser.install_controls()

step("Navigate controls with keyboard and pointer")
val tab = TinyEvent(kind: TINY_EVENT_KEY, point: TinyPoint(x: 0, y: 0), code: TINY_KEY_TAB, value: 0)
expect(browser.dispatch(tab).target_index).to_equal(0)
val typed = TinyEvent(kind: TINY_EVENT_TEXT, point: TinyPoint(x: 0, y: 0), code: 84, value: 0)
expect(browser.dispatch(typed).changed).to_be(true)
val click = TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 20, y: 90), code: 1, value: 1)
expect(browser.dispatch(click).target_index).to_equal(2)
```

</details>

#### clips nested content and composes one bounded popup

- Scroll and clip nested content
   - Expected: browser.open_popup(2, TinyRect(x: 140, y: 100, width: 40, height: 40)).code equals `0`
   - Expected: browser.wm.surfaces[1].resolved.width equals `20`
   - Expected: browser.wm.surfaces[1].resolved.height equals `20`
- Open and dismiss a bounded popup
   - Expected: browser.close_popup(2).code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var browser = TinyBrowser.create(160, 120)
browser.render_html("<body><p>Tiny</p></body>")

step("Scroll and clip nested content")
expect(browser.open_popup(2, TinyRect(x: 140, y: 100, width: 40, height: 40)).code).to_equal(0)
expect(browser.wm.surfaces[1].resolved.width).to_equal(20)
expect(browser.wm.surfaces[1].resolved.height).to_equal(20)

step("Open and dismiss a bounded popup")
expect(browser.wm.frame_receipt().direct_present).to_be(false)
expect(browser.close_popup(2).code).to_equal(0)
```

</details>

#### reports bounded failure instead of rendering partial over-capacity input

- Report backend, memory, dependency, and size evidence
   - Expected: result.status.code equals `1`
   - Expected: result.checksum equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Report backend, memory, dependency, and size evidence")
var browser = TinyBrowser.create(80, 60)
browser.max_nodes = 2
val result = browser.render_html("<body><div><p>over capacity</p></div></body>")
expect(result.status.code).to_equal(1)
expect(result.checksum).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Tiny fullscreen browser profile.
- Tiny fullscreen browser profile

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

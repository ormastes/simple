# Tiny Ui Web Wm Specification

> Tests covering Tiny fullscreen browser profile.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tiny Ui Web Wm Specification

## Scenarios

### Tiny fullscreen browser profile

#### presents an admitted page as one fullscreen opaque root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- presents an admitted page as one fullscreen opaque root
   - Protocol capture: after_step
- Boot the bounded Tiny browser profile
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: host.register(7, TINY_RESOURCE_BUILTIN, "/index.html", text_to_bytes(source)).code equals `0`
   - Expected: browser.bind_web_host(host).code equals `0`
- Render the shared nested-pane page fullscreen
   - Protocol capture: after_step
   - Evidence: protocol response verified by 13 expected checks
   - Expected: receipt.status.code equals `0`
   - Expected: receipt.presented_checksum equals `receipt.checksum`
   - Expected: receipt.resource_id equals `7`
   - Expected: receipt.resource_bytes equals `source.len()`
   - Expected: receipt.css_status.code equals `0`
   - Expected: receipt.unsupported_count equals `0`
   - Expected: browser.present.last_surface.checksum equals `browser.renderer.checksum()`
   - Expected: browser.present.last_surface.pixel_count equals `160 * 120`
   - Expected: receipt.frame.visible_surfaces equals `1`
   - Expected: browser.wm.surface_count equals `1`
   - Expected: browser.gui.nodes.len() equals `3`
   - Expected: browser.gui.nodes[1].bounds.width equals `44`
   - Expected: browser.control_max_length(1) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("presents an admitted page as one fullscreen opaque root")
step("Boot the bounded Tiny browser profile")
var browser = TinyBrowser.create(160, 120)
val source = "<html><head><style>#name { width: 44px } .hidden { display: none }</style></head><body><div><p>Tiny Browser</p><button>Open</button><input id='name' type='text' value='Ada' maxlength='3'><input type='checkbox' checked disabled><input class='hidden' type='text' value='Gone'></div></body></html>"
var host = TinyWebMemoryHost.bounded(160, 120, 1, 512)
expect(host.register(7, TINY_RESOURCE_BUILTIN, "/index.html", text_to_bytes(source)).code).to_equal(0)
expect(browser.bind_web_host(host).code).to_equal(0)

step("Render the shared nested-pane page fullscreen")
val receipt = browser.render_resource_id(7, 512)
expect(receipt.status.code).to_equal(0)
expect(receipt.parsed_nodes).to_be_greater_than(4)
expect(receipt.draw_words).to_be_greater_than(10)
expect(receipt.checksum).to_be_greater_than(0)
expect(receipt.surface_id).to_be_greater_than(0)
expect(receipt.frame_id).to_be_greater_than(0)
expect(receipt.presented_checksum).to_equal(receipt.checksum)
expect(receipt.resource_id).to_equal(7)
expect(receipt.resource_bytes).to_equal(source.len())
expect(receipt.css_status.code).to_equal(0)
expect(receipt.unsupported_count).to_equal(0)
expect(browser.present.last_surface.checksum).to_equal(browser.renderer.checksum())
expect(browser.present.last_surface.pixel_count).to_equal(160 * 120)
expect(receipt.frame.visible_surfaces).to_equal(1)
expect(receipt.frame.direct_present).to_be(true)
expect(browser.wm.surface_count).to_equal(1)
expect(browser.gui.nodes.len()).to_equal(3)
expect(browser.gui.nodes[1].bounds.width).to_equal(44)
expect(browser.control_max_length(1)).to_equal(3)
expect(browser.control_is_disabled(2)).to_be(true)
```

</details>

#### navigates built-in ROM and VFS resources through one bounded host

- navigates built-in ROM and VFS resources through one bounded host
   - Protocol capture: after_step
- Bind one sealed host with built-in ROM and VFS pages
   - Protocol capture: after_step
   - Evidence: protocol response verified by 5 expected checks
   - Expected: host.register(21, TINY_RESOURCE_BUILTIN, "/index.html", text_to_bytes(builtin)).code equals `0`
   - Expected: host.register(22, TINY_RESOURCE_ROM, "/rom.html", text_to_bytes(rom)).code equals `0`
   - Expected: host.register(23, TINY_RESOURCE_VFS, "/vfs.html", text_to_bytes(vfs)).code equals `0`
   - Expected: browser.bind_web_host(host).code equals `0`
   - Expected: first.status.code equals `0`
- Navigate to ROM and then VFS while repainting each accepted page
   - Protocol capture: after_step
   - Evidence: protocol response verified by 10 expected checks
   - Expected: from_rom.status.code equals `0`
   - Expected: from_rom.resource_id equals `22`
   - Expected: browser.current_provider_kind equals `TINY_RESOURCE_ROM`
   - Expected: browser.page_source equals `rom`
   - Expected: from_vfs.status.code equals `0`
   - Expected: from_vfs.resource_id equals `23`
   - Expected: from_vfs.presented_checksum equals `browser.present.last_surface.checksum`
   - Expected: browser.current_provider_kind equals `TINY_RESOURCE_VFS`
   - Expected: browser.current_path equals `/vfs.html`
   - Expected: browser.page_source equals `vfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("navigates built-in ROM and VFS resources through one bounded host")
step("Bind one sealed host with built-in ROM and VFS pages")
val builtin = "<body><p>Built in</p></body>"
val rom = "<body><p>ROM page</p></body>"
val vfs = "<body><p>VFS page</p></body>"
var host = TinyWebMemoryHost.bounded(120, 80, 3, 128)
expect(host.register(21, TINY_RESOURCE_BUILTIN, "/index.html", text_to_bytes(builtin)).code).to_equal(0)
expect(host.register(22, TINY_RESOURCE_ROM, "/rom.html", text_to_bytes(rom)).code).to_equal(0)
expect(host.register(23, TINY_RESOURCE_VFS, "/vfs.html", text_to_bytes(vfs)).code).to_equal(0)
var browser = TinyBrowser.create(120, 80)
expect(browser.bind_web_host(host).code).to_equal(0)
val first = browser.render_resource_id(21, 128)
expect(first.status.code).to_equal(0)

step("Navigate to ROM and then VFS while repainting each accepted page")
val from_rom = browser.navigate_resource(TINY_RESOURCE_ROM, "/rom.html", 128)
expect(from_rom.status.code).to_equal(0)
expect(from_rom.resource_id).to_equal(22)
expect(from_rom.frame_id).to_be_greater_than(first.frame_id)
expect(browser.current_provider_kind).to_equal(TINY_RESOURCE_ROM)
expect(browser.page_source).to_equal(rom)
val from_vfs = browser.navigate_resource(TINY_RESOURCE_VFS, "/vfs.html", 128)
expect(from_vfs.status.code).to_equal(0)
expect(from_vfs.resource_id).to_equal(23)
expect(from_vfs.frame_id).to_be_greater_than(from_rom.frame_id)
expect(from_vfs.presented_checksum).to_equal(browser.present.last_surface.checksum)
expect(browser.current_provider_kind).to_equal(TINY_RESOURCE_VFS)
expect(browser.current_path).to_equal("/vfs.html")
expect(browser.page_source).to_equal(vfs)
```

</details>

#### routes keyboard text and pointer events to visible controls

- routes keyboard text and pointer events to visible controls
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: browser.install_controls().code equals `0`
   - Expected: browser.wm.surface_count equals `1`
- Navigate controls with keyboard and pointer
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 7 expected checks
   - Expected: focused.target_index equals `0`
   - Expected: focused.routed_content_id equals `1`
   - Expected: typed_receipt.checksum_after equals `browser.present.last_surface.checksum`
   - Expected: click_receipt.target_index equals `2`
   - Expected: click_receipt.routed_content_id equals `1`
   - Expected: browser.wm.captured_content_id equals `1`
   - Expected: browser.wm.captured_content_id equals `-1`
- Scroll and clip nested content
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: browser.scroll.offset_y equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes keyboard text and pointer events to visible controls")
var browser = TinyBrowser.create(160, 120)
expect(browser.install_controls().code).to_equal(0)
expect(browser.wm.surface_count).to_equal(1)

step("Navigate controls with keyboard and pointer")
val tab = TinyEvent(kind: TINY_EVENT_KEY, point: TinyPoint(x: 0, y: 0), code: TINY_KEY_TAB, value: 0)
val focused = browser.dispatch(tab)
expect(focused.target_index).to_equal(0)
expect(focused.routed_content_id).to_equal(1)
expect(focused.presented).to_be(true)
val typed = TinyEvent(kind: TINY_EVENT_TEXT, point: TinyPoint(x: 0, y: 0), code: 84, value: 0)
val typed_receipt = browser.dispatch(typed)
expect(typed_receipt.changed).to_be(true)
expect(typed_receipt.presented).to_be(true)
expect(typed_receipt.damage_count).to_be_greater_than(0)
expect(typed_receipt.frame_id).to_be_greater_than(focused.frame_id)
expect(typed_receipt.checksum_after).to_equal(browser.present.last_surface.checksum)
val click = TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 20, y: 90), code: 1, value: 1)
val click_receipt = browser.dispatch(click)
expect(click_receipt.target_index).to_equal(2)
expect(click_receipt.routed_content_id).to_equal(1)
expect(click_receipt.presented).to_be(true)
expect(browser.wm.captured_content_id).to_equal(1)
val release = TinyEvent(kind: TINY_EVENT_POINTER_UP, point: TinyPoint(x: 20, y: 90), code: 1, value: 0)
browser.dispatch(release)
expect(browser.wm.captured_content_id).to_equal(-1)

step("Scroll and clip nested content")
browser.scroll = TinyScrollState(offset_y: 0, viewport_height: 120, content_height: 240)
val wheel = TinyEvent(kind: TINY_EVENT_WHEEL, point: TinyPoint(x: 20, y: 90), code: 0, value: 16)
val wheel_receipt = browser.dispatch(wheel)
expect(wheel_receipt.changed).to_be(true)
expect(wheel_receipt.presented).to_be(true)
expect(wheel_receipt.damage_count).to_be_greater_than(0)
expect(browser.scroll.offset_y).to_equal(16)
```

</details>

#### clips nested content and composes one bounded popup

- clips nested content and composes one bounded popup
   - GUI capture: after_step (HTML preferred when available)
- Clip nested popup content to the fullscreen root
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 7 expected checks
   - Expected: popup.status.code equals `0`
   - Expected: popup.checksum_after equals `browser.present.last_surface.checksum`
   - Expected: popup.sample_pixel equals `-65536`
   - Expected: browser.wm.surfaces[1].resolved.width equals `40`
   - Expected: browser.wm.surfaces[1].resolved.height equals `40`
   - Expected: browser.wm.surfaces[1].clip.width equals `20`
   - Expected: browser.wm.surfaces[1].clip.height equals `20`
- Navigate controls with keyboard and pointer
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: blocked_receipt.status.code equals `TINY_ERR_INVALID`
   - Expected: blocked_receipt.routed_content_id equals `2`
- Open and dismiss a bounded popup
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: browser.close_popup(2).code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clips nested content and composes one bounded popup")
var browser = TinyBrowser.create(160, 120)
browser.render_html("<body><p>Tiny</p></body>")

step("Clip nested popup content to the fullscreen root")
val popup = browser.open_visible_popup(2, TinyRect(x: 140, y: 100, width: 40, height: 40), -65536)
expect(popup.status.code).to_equal(0)
expect(popup.presented).to_be(true)
expect(popup.checksum_after).to_equal(browser.present.last_surface.checksum)
expect(popup.frame.direct_present).to_be(false)
expect(popup.sample_pixel).to_equal(-65536)
expect(browser.wm.surfaces[1].resolved.width).to_equal(40)
expect(browser.wm.surfaces[1].resolved.height).to_equal(40)
expect(browser.wm.surfaces[1].clip.width).to_equal(20)
expect(browser.wm.surfaces[1].clip.height).to_equal(20)

step("Navigate controls with keyboard and pointer")
val blocked_text = TinyEvent(kind: TINY_EVENT_TEXT, point: TinyPoint(x: 0, y: 0), code: 88, value: 0)
val blocked_receipt = browser.dispatch(blocked_text)
expect(blocked_receipt.status.code).to_equal(TINY_ERR_INVALID)
expect(blocked_receipt.routed_content_id).to_equal(2)
expect(blocked_receipt.presented).to_be(false)

step("Open and dismiss a bounded popup")
expect(browser.wm.frame_receipt().direct_present).to_be(false)
expect(browser.close_popup(2).code).to_equal(0)
```

</details>

#### reports bounded failure instead of rendering partial over-capacity input

- reports bounded failure instead of rendering partial over-capacity input
   - Protocol capture: after_step
- Report backend, memory, dependency, and size evidence
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: result.status.code equals `1`
   - Expected: result.checksum equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports bounded failure instead of rendering partial over-capacity input")
step("Report backend, memory, dependency, and size evidence")
var browser = TinyBrowser.create(80, 60)
browser.max_nodes = 2
val result = browser.render_html("<body><div><p>over capacity</p></div></body>")
expect(result.status.code).to_equal(1)
expect(result.checksum).to_equal(0)
```

</details>

#### blocks optional module and strict Vulkan claims until retained evidence exists

- blocks optional module and strict Vulkan claims until retained evidence exists
- Report backend, memory, dependency, and size evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks optional module and strict Vulkan claims until retained evidence exists")
step("Report backend, memory, dependency, and size evidence")
fail("blocked: service-form parity, static/dynamic descriptors, excluded-pack closure, and strict Vulkan device readback are not verified")
```

</details>

#### blocks RV32 completion until build framebuffer and physical input evidence exists

- blocks RV32 completion until build framebuffer and physical input evidence exists
- Render the shared nested-pane page fullscreen


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks RV32 completion until build framebuffer and physical input evidence exists")
step("Render the shared nested-pane page fullscreen")
fail("blocked: R0-R4 require fresh RV32 build/boot, RGB565, fullscreen present, physical input, and module receipts")
```

</details>

#### blocks the 409600-byte closure claim until ELF and PT_LOAD evidence exists

- blocks the 409600-byte closure claim until ELF and PT_LOAD evidence exists
- Report backend, memory, dependency, and size evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks the 409600-byte closure claim until ELF and PT_LOAD evidence exists")
step("Report backend, memory, dependency, and size evidence")
fail("blocked: S0 requires stripped ELF, PT_LOAD, section, symbol, dependency, module-delta, and reserve evidence")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Tiny fullscreen browser profile.
- Tiny fullscreen browser profile

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `d494c9372f6c9517c10fbc6a1786faaef6308d89ca298190c37d7e31c7a5e38e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d494c9372f6c9517c10fbc6a1786faaef6308d89ca298190c37d7e31c7a5e38e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d494c9372f6c9517c10fbc6a1786faaef6308d89ca298190c37d7e31c7a5e38e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl
mirror: doc/06_spec/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 39 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'presents an admitted page as one fullscreen opaque root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'navigates built-in ROM and VFS resources through one bounded host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes keyboard text and pointer events to visible controls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

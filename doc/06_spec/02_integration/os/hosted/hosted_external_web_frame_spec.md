# Hosted External Web Frame Specification

> Tests covering hosted external browser frames.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted External Web Frame Specification

## Scenarios

### hosted external browser frames

#### keeps positive-owner content out of the in-process renderer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps positive-owner content out of the in-process renderer


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps positive-owner content out of the in-process renderer")
val hostile = (
    "<style>body{background-color:#ef4444}</style>" +
    "<script>document.body.setAttribute('data-ran','yes')</script>"
)
var local = HostCompositor.new_headless(Size(
    width: 160u64, height: 120u64
))
local.apply_bridge_request(
    1, 0, COMP_CREATE_WINDOW.to_i64(), 0, "Local",
    8, 8, 100, 80, hostile, 1, "hosted-web-event"
)
expect(local.requires_external_web_frame(1)).to_be(false)
val local_raster = Engine2dCompositorBackend.create_named(
    160, 120, "software"
)
expect(local.render_frame_engine2d(local_raster)).to_be(true)
expect(count_color(
    local.pure_simple_pixel_buffer(), 0xFFEF4444u32
)).to_be_greater_than(0)
local_raster.shutdown()

var remote = HostCompositor.new_headless(Size(
    width: 160u64, height: 120u64
))
remote.apply_bridge_request(
    1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Remote",
    8, 8, 100, 80, hostile, 77, "hosted-web-event"
)
expect(remote.requires_external_web_frame(1)).to_be(true)
val remote_raster = Engine2dCompositorBackend.create_named(
    160, 120, "software"
)
expect(remote.render_frame_engine2d(remote_raster)).to_be(false)
expect(count_color(
    remote.pure_simple_pixel_buffer(), 0xFFEF4444u32
)).to_equal(0)
remote_raster.shutdown()
```

</details>

#### keeps trusted frames isolated by window through close

- keeps trusted frames isolated by window through close
- Open two browser compositor windows
- 1, 1, COMP CREATE WINDOW to i64
- 2, 2, COMP CREATE WINDOW to i64
- Attach distinct trusted external frames
- Close one window without releasing the other frame
   - Expected: comp.external_web_window_ids.len() equals `1`
   - Expected: comp.external_web_frames.len() equals `1`
   - Expected: comp.external_web_window_ids[0] equals `2`
   - Expected: comp.external_web_frames[0].window_id equals `2`
- comp pure simple pixel buffer
- comp pure simple pixel buffer
- raster shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps trusted frames isolated by window through close")
step("Open two browser compositor windows")
val first_body = "<div>first parent body</div>"
val second_body = "<div>second parent body</div>"
var comp = HostCompositor.new_headless(Size(
    width: 260u64, height: 220u64
))
comp.apply_bridge_request(
    1, 1, COMP_CREATE_WINDOW.to_i64(), 0, "First",
    8, 8, 112, 160, first_body, 1, "browser"
)
comp.apply_bridge_request(
    2, 2, COMP_CREATE_WINDOW.to_i64(), 0, "Second",
    140, 8, 112, 160, second_body, 2, "browser"
)
expect(comp.require_external_web_frame(1)).to_be(true)
expect(comp.require_external_web_frame(2)).to_be(true)

step("Attach distinct trusted external frames")
val theme = default_theme_id()
val first_revision = simple_web_content_revision_with_theme(
    theme, "First", first_body, 104, 80, 0
)
val second_revision = simple_web_content_revision_with_theme(
    theme, "Second", second_body, 104, 80, 0
)
val first = trusted_frame("1", first_revision, 0xFF123456u32)
val second = trusted_frame("2", second_revision, 0xFFABCDEFu32)
expect(comp.set_external_web_frame(1, first)).to_be(true)
expect(comp.set_external_web_frame(2, second)).to_be(true)
val raster = Engine2dCompositorBackend.create_named(
    260, 220, "software"
)
expect(comp.render_frame_engine2d(raster)).to_be(true)
val both_pixels = comp.pure_simple_pixel_buffer()
expect(count_color(both_pixels, 0xFF123456u32)).to_be_greater_than(5000)
expect(count_color(both_pixels, 0xFFABCDEFu32)).to_be_greater_than(5000)

step("Close one window without releasing the other frame")
comp.destroy_window(1)
expect(comp.external_web_window_ids.len()).to_equal(1)
expect(comp.external_web_frames.len()).to_equal(1)
expect(comp.external_web_window_ids[0]).to_equal(2)
expect(comp.external_web_frames[0].window_id).to_equal("2")
expect(comp.set_external_web_frame(1, first)).to_be(false)
expect(comp.render_frame_engine2d(raster)).to_be(true)
expect(count_color(
    comp.pure_simple_pixel_buffer(), 0xFF123456u32
)).to_equal(0)
expect(count_color(
    comp.pure_simple_pixel_buffer(), 0xFFABCDEFu32
)).to_be_greater_than(5000)
raster.shutdown()
```

</details>

#### patches only an exact retained external frame base

- patches only an exact retained external frame base
   - Expected: comp.dirty.count() equals `1`
   - Expected: dirty.x equals `8 + 4 + 1`
   - Expected: dirty.w equals `1`
   - Expected: dirty.h equals `1`
   - Expected: committed.pixels[1 * 104 + 1] equals `0xFFABCDEFu32`
   - Expected: committed.pixels[0] equals `0xFF123456u32`
   - Expected: base.pixels[1 * 104 + 1] equals `0xFF123456u32`

## Overview

<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("patches only an exact retained external frame base")
val body = "<div>retained damage</div>"
var comp = HostCompositor.new_headless(Size(
    width: 160u64, height: 120u64
))
comp.apply_bridge_request(
    1, 1, COMP_CREATE_WINDOW.to_i64(), 0, "Retained",
    8, 8, 112, 160, body, 1, "browser"
)
expect(comp.require_external_web_frame(1)).to_be(true)
val theme = default_theme_id()
val base_revision = simple_web_content_revision_with_theme(
    theme, "Retained", body, 104, 80, 0
)
val base = trusted_frame("1", base_revision, 0xFF123456u32)
expect(comp.set_external_web_frame(1, base)).to_be(true)
# Isolate the packed-delta invalidation from window creation/full
# frame admission.  A local content patch must not widen to desktop.
comp.dirty.clear()
val delta = trusted_damage_frame(
    "1", base_revision, base_revision + 1, 0xFFABCDEFu32)
expect(comp.set_external_web_frame(1, delta)).to_be(true)
expect(comp.dirty.count()).to_equal(1)
val dirty = comp.dirty.bounding_box()
# The frame's [1,1,1,1] content-local delta is translated through the
# normal 4px border / 28px titlebar / browser toolbar content origin.
expect(dirty.x).to_equal(8 + 4 + 1)
expect(dirty.y).to_equal(
    8 + 32 + shared_wm_browser_content_extra_height("browser") + 1)
expect(dirty.w).to_equal(1)
expect(dirty.h).to_equal(1)
val committed = comp.external_web_frames[0]
expect(committed.pixels[1 * 104 + 1]).to_equal(0xFFABCDEFu32)
expect(committed.pixels[0]).to_equal(0xFF123456u32)
expect(base.pixels[1 * 104 + 1]).to_equal(0xFF123456u32)
expect(committed.checksum).to_equal(
    wm_content_frame_checksum(committed.pixels))
expect(comp.set_external_web_frame(1, delta)).to_be(false)
val no_base = trusted_damage_frame(
    "1", 0, base_revision + 2, 0xFF16A34Au32)
expect(comp.set_external_web_frame(1, no_base)).to_be(false)
```

</details>

#### reuses a consumed registry-owned retained base across deltas

- reuses a consumed registry-owned retained base across deltas
   - Expected: comp.external_web_in_place_delta_count equals `1`
   - Expected: comp.external_web_in_place_delta_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reuses a consumed registry-owned retained base across deltas")
val body = "<div>owned retained damage</div>"
var comp = HostCompositor.new_headless(Size(
    width: 160u64, height: 120u64
))
comp.apply_bridge_request(
    1, 1, COMP_CREATE_WINDOW.to_i64(), 0, "Owned",
    8, 8, 112, 160, body, 1, "browser"
)
expect(comp.require_external_web_frame(1)).to_be(true)
val revision = simple_web_content_revision_with_theme(
    default_theme_id(), "Owned", body, 104, 80, 0
)
# This models HostedBrowserRendererRegistry.take_frame(): once handed
# off, the caller must not retain or mutate the full pixel array.
expect(comp.set_external_web_frame_owned(
    1, trusted_frame("1", revision, 0xFF123456u32)
)).to_be(true)
val raster = Engine2dCompositorBackend.create_named(
    160, 120, "software"
)
expect(comp.render_frame_engine2d(raster)).to_be(true)

val first = trusted_damage_frame(
    "1", revision, revision + 1, 0xFFABCDEFu32)
expect(comp.set_external_web_frame_owned(1, first)).to_be(true)
expect(comp.external_web_in_place_delta_count).to_equal(1)
expect(comp.external_web_frames[0].pixels[1 * 104 + 1]).to_equal(
    0xFFABCDEFu32)
expect(comp.render_frame_engine2d(raster)).to_be(true)

val second = trusted_damage_frame(
    "1", revision + 1, revision + 2, 0xFF16A34Au32)
expect(comp.set_external_web_frame_owned(1, second)).to_be(true)
expect(comp.external_web_in_place_delta_count).to_equal(2)
expect(comp.external_web_frames[0].pixels[1 * 104 + 1]).to_equal(
    0xFF16A34Au32)
raster.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/hosted/hosted_external_web_frame_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Tests covering hosted external browser frames.
- hosted external browser frames

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-WEB-BROWSER-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a82818f340f877dec638c40c5080a2e5dbf70ed279dd6e8ad08eb383300d3767`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a82818f340f877dec638c40c5080a2e5dbf70ed279dd6e8ad08eb383300d3767`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a82818f340f877dec638c40c5080a2e5dbf70ed279dd6e8ad08eb383300d3767`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/os/hosted/hosted_external_web_frame_spec.spl
mirror: doc/06_spec/02_integration/os/hosted/hosted_external_web_frame_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/02_integration/os/hosted/hosted_external_web_frame_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/hosted/hosted_external_web_frame_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/hosted/hosted_external_web_frame_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/hosted/hosted_external_web_frame_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/02_integration/os/hosted/hosted_external_web_frame_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps positive-owner content out of the in-process renderer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/hosted/hosted_external_web_frame_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps trusted frames isolated by window through close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/hosted/hosted_external_web_frame_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'patches only an exact retained external frame base' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

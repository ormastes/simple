# hosted_external_web_frame_spec

> Verifies the hosted external web frame behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hosted_external_web_frame_spec

Verifies the hosted external web frame behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/hosted/hosted_external_web_frame_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the hosted external web frame behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### hosted external browser frames

#### keeps positive-owner content out of the in-process renderer

- Verify: keeps positive-owner content out of the in-process renderer


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014
step("Verify: keeps positive-owner content out of the in-process renderer")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val hostile = (
    "<style>body{{background-color:#ef4444}}</style>" +
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
)).to_equal(0)  # oracle: pinned constant asserted by this scenario
remote_raster.shutdown()
```

</details>

#### keeps trusted frames isolated by window through close

- Verify: keeps trusted frames isolated by window through close
- Open two browser compositor windows
- Attach distinct trusted external frames
- Close one window without releasing the other frame
   - Expected: comp.external_web_window_ids.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: comp.external_web_frames.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: comp.external_web_window_ids[0] equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: comp.external_web_frames[0].window_id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014
step("Verify: keeps trusted frames isolated by window through close")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(comp.external_web_window_ids.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(comp.external_web_frames.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(comp.external_web_window_ids[0]).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(comp.external_web_frames[0].window_id).to_equal("2")
expect(comp.set_external_web_frame(1, first)).to_be(false)
expect(comp.render_frame_engine2d(raster)).to_be(true)
expect(count_color(
    comp.pure_simple_pixel_buffer(), 0xFF123456u32
)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(count_color(
    comp.pure_simple_pixel_buffer(), 0xFFABCDEFu32
)).to_be_greater_than(5000)
raster.shutdown()
```

</details>

#### patches only an exact retained external frame base

- Verify: patches only an exact retained external frame base
   - Expected: comp.dirty.count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: dirty.x equals `8 + 4 + 1`
   - Expected: dirty.w equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: dirty.h equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: committed.pixels[1 * 104 + 1] equals `0xFFABCDEFu32`
   - Expected: committed.pixels[0] equals `0xFF123456u32`
   - Expected: base.pixels[1 * 104 + 1] equals `0xFF123456u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014
step("Verify: patches only an exact retained external frame base")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(comp.dirty.count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
val dirty = comp.dirty.bounding_box()
# The frame's [1,1,1,1] content-local delta is translated through the
# normal 4px border / 28px titlebar / browser toolbar content origin.
expect(dirty.x).to_equal(8 + 4 + 1)
expect(dirty.y).to_equal(
    8 + 32 + shared_wm_browser_content_extra_height("browser") + 1)
expect(dirty.w).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(dirty.h).to_equal(1)  # oracle: pinned constant asserted by this scenario
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

- Verify: reuses a consumed registry-owned retained base across deltas
   - Expected: comp.external_web_in_place_delta_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: comp.external_web_in_place_delta_count equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-014
step("Verify: reuses a consumed registry-owned retained base across deltas")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(comp.external_web_in_place_delta_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(comp.external_web_frames[0].pixels[1 * 104 + 1]).to_equal(
    0xFFABCDEFu32)
expect(comp.render_frame_engine2d(raster)).to_be(true)

val second = trusted_damage_frame(
    "1", revision + 1, revision + 2, 0xFF16A34Au32)
expect(comp.set_external_web_frame_owned(1, second)).to_be(true)
expect(comp.external_web_in_place_delta_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(comp.external_web_frames[0].pixels[1 * 104 + 1]).to_equal(
    0xFF16A34Au32)
raster.shutdown()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6fc1a63d645d224c546c40226da87b423b4f2ab66ad1cf9ba96ee626fda2eed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6fc1a63d645d224c546c40226da87b423b4f2ab66ad1cf9ba96ee626fda2eed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6fc1a63d645d224c546c40226da87b423b4f2ab66ad1cf9ba96ee626fda2eed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/os/hosted/hosted_external_web_frame_spec.spl
mirror: doc/06_spec/02_integration/os/hosted/hosted_external_web_frame_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/hosted/hosted_external_web_frame_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/os/hosted/hosted_external_web_frame_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/hosted/hosted_external_web_frame_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

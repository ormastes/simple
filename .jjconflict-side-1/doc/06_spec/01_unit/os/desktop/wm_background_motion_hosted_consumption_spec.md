# wm_background_motion_hosted_consumption_spec

> Plan item B follow-up 1+2

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_background_motion_hosted_consumption_spec

Plan item B follow-up 1+2

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/wm_background_motion_hosted_consumption_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Plan item B follow-up 1+2
(doc/03_plan/os/desktop/wm_window_render_api_hardening_plan.md 'Status
(fix-round, 2026-07-07): I8 staged-deferred'): the motion-background PROVIDER
(background_motion_provider.spl) and the resolver
(shared_wm_scene_resolve_background) landed already, but nothing in the
hosted-WM chrome consumer (HostCompositor.render_frame(), host_compositor_
entry.spl) ever called the resolver — a configured "motion" BackgroundSpec
was registered and reachable, but never actually consumed and presented on
this lane. Design invariant I8 ("background-only advance does NOT re-raster
windows/chrome") was also staged-deferred pending region-dirty tracking.

This spec proves both follow-ups on the real HostCompositor type (not a
throwaway executor double): a "motion" BackgroundSpec advances frames across
two distinct absolute-time samples through HostCompositor.render_background_
only, an unknown/unregistered motion source fails loud (the visible marker
color is painted, never a silent stale/default background), a background-only
advance leaves previously-drawn window pixels byte-exact (I8), and
HostCompositor.render_frame()'s direct-draw lane also resolves a configured
motion background instead of hardcoding the theme color.

## Scenarios

### Hosted-WM chrome consumer: HostCompositor consumes a 'motion' BackgroundSpec (plan item B follow-up 2)

#### render_background_only advances frames across two distinct absolute-time samples (I8 region-dirty path)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- render_background_only advances frames across two distinct absolute-time samples (I8 region-dirty path)
- t=0 selects frame 0 (red)
   - Expected: backend0.pixels[_BG_SAMPLE_IDX] equals `_RED`
- t=one interval selects frame 1 (blue) — same comp, only time changed
   - Expected: backend1.pixels[_BG_SAMPLE_IDX] equals `_BLUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("render_background_only advances frames across two distinct absolute-time samples (I8 region-dirty path)")
host_motion_background_provider_reset()
host_background_image_provider_reset()
val manifest = _write_two_frame_manifest()
match HostMotionBackgroundSource.create(manifest, _W, _H, "stretch"):
    Ok(source):
        shared_wm_scene_register_motion_background_source(source)
        val comp = _new_comp()
        comp.set_background(_motion_background(manifest))
        step("t=0 selects frame 0 (red)")
        val ok0 = comp.render_background_only(0)
        assert_true(ok0)
        val backend0 = comp.backend
        expect(backend0.pixels[_BG_SAMPLE_IDX]).to_equal(_RED)
        step("t=one interval selects frame 1 (blue) — same comp, only time changed")
        val ok1 = comp.render_background_only(_INTERVAL)
        assert_true(ok1)
        val backend1 = comp.backend
        expect(backend1.pixels[_BG_SAMPLE_IDX]).to_equal(_BLUE)
        shared_wm_scene_register_motion_background_source(nil)
    Err(message):
        print "unexpected motion source create failure: {message}"
        assert_true(false)
```

</details>

#### background-only advance leaves window pixels byte-exact (I8: does NOT re-raster windows/chrome)

- background-only advance leaves window pixels byte-exact (I8: does NOT re-raster windows/chrome)
- A full render_frame() with the default color background establishes window chrome pixels
   - Expected: window_pixel_before equals `theme.host_window_body`
- Switching to a motion background and driving two background-only frames must not touch the window pixel
   - Expected: backend0.pixels[_BG_SAMPLE_IDX] equals `_RED`
   - Expected: backend0.pixels[_WINDOW_BODY_SAMPLE_IDX] equals `theme.host_window_body`
   - Expected: backend1.pixels[_BG_SAMPLE_IDX] equals `_BLUE`
   - Expected: backend1.pixels[_WINDOW_BODY_SAMPLE_IDX] equals `theme.host_window_body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("background-only advance leaves window pixels byte-exact (I8: does NOT re-raster windows/chrome)")
host_motion_background_provider_reset()
host_background_image_provider_reset()
# Pin the direct-draw chrome path: on a Metal-capable host,
# render_frame()'s FIRST call below (background still kind:"color" at
# that point) would otherwise take the fast CSS/GUI-web lane, whose
# per-window content insets (+28/-32) differ from the direct-draw
# lane's (+32/-36) — sampling a direct-draw-lane offset against a
# fast-lane render lands inside the content area instead of the
# window body, which is a TEST bug, not a production one (once
# self.background.kind becomes "motion" below, render_frame's own
# fast-lane gate already forces direct-draw for real, matching this).
host_wm_force_direct_chrome(true)
val manifest = _write_two_frame_manifest()
match HostMotionBackgroundSource.create(manifest, _W, _H, "stretch"):
    Ok(source):
        val comp = _new_comp()
        _seed_one_window(comp)
        step("A full render_frame() with the default color background establishes window chrome pixels")
        comp.render_frame()
        val theme = wm_chrome_theme()
        val backend_full = comp.backend
        val window_pixel_before = backend_full.pixels[_WINDOW_BODY_SAMPLE_IDX]
        expect(window_pixel_before).to_equal(theme.host_window_body)
        step("Switching to a motion background and driving two background-only frames must not touch the window pixel")
        shared_wm_scene_register_motion_background_source(source)
        comp.set_background(_motion_background(manifest))
        val ok0 = comp.render_background_only(0)
        assert_true(ok0)
        val backend0 = comp.backend
        expect(backend0.pixels[_BG_SAMPLE_IDX]).to_equal(_RED)
        expect(backend0.pixels[_WINDOW_BODY_SAMPLE_IDX]).to_equal(theme.host_window_body)
        val ok1 = comp.render_background_only(_INTERVAL)
        assert_true(ok1)
        val backend1 = comp.backend
        expect(backend1.pixels[_BG_SAMPLE_IDX]).to_equal(_BLUE)
        expect(backend1.pixels[_WINDOW_BODY_SAMPLE_IDX]).to_equal(theme.host_window_body)
        shared_wm_scene_register_motion_background_source(nil)
    Err(message):
        print "unexpected motion source create failure: {message}"
        assert_true(false)
host_wm_force_direct_chrome(false)
```

</details>

#### fails loud at the hosted consumption layer: an unregistered motion source paints the visible unresolved marker, never a silent default

- fails loud at the hosted consumption layer: an unregistered motion source paints the visible unresolved marker, never a silent default
   - Expected: backend.pixels[_BG_SAMPLE_IDX] equals `WM_BACKGROUND_UNRESOLVED_MARKER_COLOR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails loud at the hosted consumption layer: an unregistered motion source paints the visible unresolved marker, never a silent default")
host_motion_background_provider_reset()
host_background_image_provider_reset()
shared_wm_scene_register_motion_background_source(nil)
val comp = _new_comp()
comp.set_background(_motion_background("{_fixture_dir()}/never_registered.manifest"))
val ok = comp.render_background_only(0)
assert_true(ok)
val backend = comp.backend
expect(backend.pixels[_BG_SAMPLE_IDX]).to_equal(WM_BACKGROUND_UNRESOLVED_MARKER_COLOR)
```

</details>

#### render_frame()'s direct-draw lane resolves a configured motion background instead of hardcoding theme.compositor_bg

- render_frame()'s direct-draw lane resolves a configured motion background instead of hardcoding theme.compositor_bg
- Single-frame manifest is a deterministic static image regardless of wall-clock time, so render_frame()'s internal real-time read is not a source of flakiness here
   - Expected: backend.pixels[_BG_SAMPLE_IDX] equals `_RED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("render_frame()'s direct-draw lane resolves a configured motion background instead of hardcoding theme.compositor_bg")
host_motion_background_provider_reset()
host_background_image_provider_reset()
val manifest = _write_single_frame_manifest()
match HostMotionBackgroundSource.create(manifest, _W, _H, "stretch"):
    Ok(source):
        shared_wm_scene_register_motion_background_source(source)
        val comp = _new_comp()
        comp.set_background(_motion_background(manifest))
        step("Single-frame manifest is a deterministic static image regardless of wall-clock time, so render_frame()'s internal real-time read is not a source of flakiness here")
        comp.render_frame()
        val backend = comp.backend
        expect(backend.pixels[_BG_SAMPLE_IDX]).to_equal(_RED)
        val theme = wm_chrome_theme()
        val not_default = backend.pixels[_BG_SAMPLE_IDX] != theme.compositor_bg
        assert_true(not_default)
        shared_wm_scene_register_motion_background_source(nil)
    Err(message):
        print "unexpected motion source create failure: {message}"
        assert_true(false)
```

</details>

### I8 region-dirty math: host_background_visible_rects (pure rectangle subtraction)

#### computes the desktop rect minus a window hole exactly, with no returned rect overlapping the window

- computes the desktop rect minus a window hole exactly, with no returned rect overlapping the window
   - Expected: area equals `100 * 100 - 30 * 30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("computes the desktop rect minus a window hole exactly, with no returned rect overlapping the window")
val windows = [HostedWindow(id: 1, owner_port: 0, title: "W", x: 20, y: 20, w: 30, h: 30, content: "", process_id: 0, app_id: "", minimized: false, focused: false)]
val region = host_background_visible_rects(windows, 100, 100)
assert_true(region.computed)
var area = 0
var any_overlap = false
for r in region.rects:
    area = area + r.width * r.height
    if r.x < 50 and r.x + r.width > 20 and r.y < 50 and r.y + r.height > 20:
        any_overlap = true
assert_false(any_overlap)
expect(area).to_equal(100 * 100 - 30 * 30)
```

</details>

#### treats a minimized window as fully background-visible (no hole)

- treats a minimized window as fully background-visible (no hole)
   - Expected: region.rects.len() equals `1`
   - Expected: region.rects[0].width * region.rects[0].height equals `100 * 100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("treats a minimized window as fully background-visible (no hole)")
val windows = [HostedWindow(id: 1, owner_port: 0, title: "W", x: 20, y: 20, w: 30, h: 30, content: "", process_id: 0, app_id: "", minimized: true, focused: false)]
val region = host_background_visible_rects(windows, 100, 100)
assert_true(region.computed)
expect(region.rects.len()).to_equal(1)
expect(region.rects[0].width * region.rects[0].height).to_equal(100 * 100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a262c80ef67d11c83e9805ef82f405eb5256f96de898a5ec0c279dd38b2a07b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a262c80ef67d11c83e9805ef82f405eb5256f96de898a5ec0c279dd38b2a07b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a262c80ef67d11c83e9805ef82f405eb5256f96de898a5ec0c279dd38b2a07b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/desktop/wm_background_motion_hosted_consumption_spec.spl
mirror: doc/06_spec/01_unit/os/desktop/wm_background_motion_hosted_consumption_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/desktop/wm_background_motion_hosted_consumption_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/desktop/wm_background_motion_hosted_consumption_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/desktop/wm_background_motion_hosted_consumption_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/desktop/wm_background_motion_hosted_consumption_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'render_background_only advances frames across two distinct absolute-time samples (I8 region-dirty path)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/wm_background_motion_hosted_consumption_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'background-only advance leaves window pixels byte-exact (I8: does NOT re-raster windows/chrome)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/wm_background_motion_hosted_consumption_spec.spl:189:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails loud at the hosted consumption layer: an unregistered motion source paints the visible unresolved marker, never a silent default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

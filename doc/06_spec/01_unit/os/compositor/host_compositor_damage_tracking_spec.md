# host_compositor_damage_tracking_spec

> HostCompositor damage tracking / no-op frame skip (hardening item 4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# host_compositor_damage_tracking_spec

HostCompositor damage tracking / no-op frame skip (hardening item 4).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/host_compositor_damage_tracking_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

HostCompositor damage tracking / no-op frame skip (hardening item 4).

dirty_rect.spl's DirtyRegion had zero call sites before this change and
host_compositor_core.spl redrew every window every frame regardless of
whether anything changed. This wires DirtyRegion in minimally and honestly:
window create/destroy/move/resize/content-update/focus-change mark the
affected (old + new) rects dirty; render_frame() skips the chrome-paint +
scene-composite + present step entirely when nothing is dirty (the real
perf win), and always keeps the existing full recomposite otherwise (no
partial/rect-level recomposition yet — see the ponytail comment in
render_frame). The per-window content-pixel cache (task #15,
host_compositor_content_cache_spec.spl) keeps its own independent hit/miss
bookkeeping every call regardless of this skip, so that pre-existing
contract is untouched.

## Scenarios

### HostCompositor damage tracking (item 4)

#### skips the second of two identical consecutive frames

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- skips the second of two identical consecutive frames
   - Expected: presents_after_first equals `1`
   - Expected: comp.backend.present_count equals `presents_after_first`
   - Expected: comp.skipped_frame_count equals `skipped_before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("skips the second of two identical consecutive frames")
host_wm_force_direct_chrome(true)
val backend = HeadlessHostCompositorBackend.new(200, 200)
val comp = HostCompositor.new(backend, Size.wh(200, 200))

# Frame 1: fresh compositor is seeded with full-screen damage, so it
# always renders and presents once.
comp.render_frame()
val presents_after_first = comp.backend.present_count
expect(presents_after_first).to_equal(1)
val skipped_before = comp.skipped_frame_count

# Frame 2: nothing changed since frame 1 -> no-op path, no present.
comp.render_frame()
expect(comp.backend.present_count).to_equal(presents_after_first)
expect(comp.skipped_frame_count).to_equal(skipped_before + 1)
```

</details>

#### a window move marks damage and forces the next frame to render

- a window move marks damage and forces the next frame to render
   - Expected: comp.backend.present_count equals `presents_after_settle + 1`
   - Expected: comp.skipped_frame_count equals `skipped_after_settle`
   - Expected: comp.windows[0].x equals `90`
   - Expected: comp.windows[0].y equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a window move marks damage and forces the next frame to render")
host_wm_force_direct_chrome(true)
val backend = HeadlessHostCompositorBackend.new(200, 200)
val comp = HostCompositor.new(backend, Size.wh(200, 200))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Term", 10, 10, 40, 40, "x", 1, "/sys/apps/one")
val wid = comp.windows[0].id

comp.render_frame() # create damage -> renders
comp.render_frame() # settled -> skipped
val presents_after_settle = comp.backend.present_count
val skipped_after_settle = comp.skipped_frame_count

comp.apply_bridge_request(2, 77, COMP_MOVE.to_i64(), wid, "", 90, 90, 0, 0, "", 0, "")
comp.render_frame()
expect(comp.backend.present_count).to_equal(presents_after_settle + 1)
expect(comp.skipped_frame_count).to_equal(skipped_after_settle)
expect(comp.windows[0].x).to_equal(90)
expect(comp.windows[0].y).to_equal(90)
```

</details>

#### a moved window's dirty rects cover both the old and new position

- a moved window's dirty rects cover both the old and new position
   - Expected: bbox.x <= 10 is true
   - Expected: bbox.y <= 10 is true
   - Expected: bbox.x + bbox.w >= 130 is true
   - Expected: bbox.y + bbox.h >= 130 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a moved window's dirty rects cover both the old and new position")
val backend = HeadlessHostCompositorBackend.new(200, 200)
val comp = HostCompositor.new(backend, Size.wh(200, 200))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Term", 10, 10, 40, 40, "x", 1, "/sys/apps/one")
val wid = comp.windows[0].id
comp.render_frame() # clears dirty from the create

comp.apply_bridge_request(2, 77, COMP_MOVE.to_i64(), wid, "", 90, 90, 0, 0, "", 0, "")
val bbox = comp.dirty.bounding_box()
# Old rect is (10,10,40,40), new rect is (90,90,40,40) -- the
# bounding box of both must contain both corners.
expect(bbox.x <= 10).to_equal(true)
expect(bbox.y <= 10).to_equal(true)
expect(bbox.x + bbox.w >= 130).to_equal(true)
expect(bbox.y + bbox.h >= 130).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `84efd2648e330226cf6c2e6de398bfc6d1cbcab6e76d87ed7b183da46398ac13`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84efd2648e330226cf6c2e6de398bfc6d1cbcab6e76d87ed7b183da46398ac13`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84efd2648e330226cf6c2e6de398bfc6d1cbcab6e76d87ed7b183da46398ac13`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/compositor/host_compositor_damage_tracking_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/host_compositor_damage_tracking_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/host_compositor_damage_tracking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/host_compositor_damage_tracking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/host_compositor_damage_tracking_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/compositor/host_compositor_damage_tracking_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips the second of two identical consecutive frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/host_compositor_damage_tracking_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a window move marks damage and forces the next frame to render' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/host_compositor_damage_tracking_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a moved window's dirty rects cover both the old and new position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

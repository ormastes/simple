# wm_background_motion_provider_spec

> BackgroundSpec kind:motion (plan item B,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_background_motion_provider_spec

BackgroundSpec kind:motion (plan item B,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/wm_background_motion_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

BackgroundSpec kind:motion (plan item B,
doc/03_plan/os/desktop/wm_window_render_api_hardening_plan.md; design
doc/05_design/os/desktop/simple_gui_internal_window_impl_spec.md 'Phase-2
Provider Design') implements the moving-image background as a frame-source
abstraction: an ordered PPM frame set + a per-frame interval, described by a
plain-text manifest (line 1 = frame_interval_micros, remaining lines = frame
paths). No video codecs — frames are just images and reuse the kind:image
provider's content-hash cache + fit resampling.

All time in this spec is an injected fake clock (explicit t_micros values) —
frame selection is a pure function of absolute time
(index = (t / interval) % frame_count), so the tests are deterministic with
zero sleeps. The same absolute-time indexing IS the frame-drop policy: a
caller that falls behind by several intervals lands on the current frame and
skips the missed ones instead of stalling to catch up.

Cadence/dirty contract (design invariant I8): the present loop stays
dirty-gated (GUI-5a). shared_wm_motion_background_next_due_micros() exposes
the next-due timestamp and the pure predicate shared_wm_motion_dirty_due
fires exactly once per due value once it has arrived — never per-tick, and an
un-advancing due value cannot force perpetual re-presents.

## Scenarios

### BackgroundSpec kind:motion provider (background_motion_provider + window_scene resolver)

#### loud-fails source construction on a missing manifest, an empty manifest, a bad interval, and an empty frame set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loud-fails source construction on a missing manifest, an empty manifest, a bad interval, and an empty frame set
- Missing manifest file is a typed Err, never a silent default
   - Expected: true is false
- Empty manifest (no lines) is a typed Err
   - Expected: true is false
- Non-positive / non-numeric frame interval is a typed Err
   - Expected: true is false
- Interval but zero frame paths is a typed Err (empty frame set)
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("loud-fails source construction on a missing manifest, an empty manifest, a bad interval, and an empty frame set")
step("Missing manifest file is a typed Err, never a silent default")
match HostMotionBackgroundSource.create("{_fixture_dir()}/does_not_exist.manifest", 4, 4, "cover"):
    Ok(_):
        expect(true).to_equal(false)
    Err(message):
        expect(message).to_contain("unreadable")
step("Empty manifest (no lines) is a typed Err")
val empty_path = _write_manifest("{_fixture_dir()}/empty.manifest", [])
match HostMotionBackgroundSource.create(empty_path, 4, 4, "cover"):
    Ok(_):
        expect(true).to_equal(false)
    Err(message):
        expect(message).to_contain("empty")
step("Non-positive / non-numeric frame interval is a typed Err")
val bad_interval_path = _write_manifest("{_fixture_dir()}/bad_interval.manifest", ["not-a-number", "frame.ppm"])
match HostMotionBackgroundSource.create(bad_interval_path, 4, 4, "cover"):
    Ok(_):
        expect(true).to_equal(false)
    Err(message):
        expect(message).to_contain("frame_interval_micros")
step("Interval but zero frame paths is a typed Err (empty frame set)")
val no_frames_path = _write_manifest("{_fixture_dir()}/no_frames.manifest", ["{_INTERVAL}"])
match HostMotionBackgroundSource.create(no_frames_path, 4, 4, "cover"):
    Ok(_):
        expect(true).to_equal(false)
    Err(message):
        expect(message).to_contain("no frame paths")
```

</details>

#### advances frames at the manifest cadence as a pure function of injected time, dropping missed frames instead of stalling

- advances frames at the manifest cadence as a pure function of injected time, dropping missed frames instead of stalling
- t=0 selects frame 0 (red)
   - Expected: frame0.width equals `4`
   - Expected: frame0.pixels[0] equals `_RED`
- t=one interval selects frame 1 (blue)
   - Expected: frame1.pixels[0] equals `_BLUE`
- A caller that falls behind (t jumps to 2.5 intervals) lands on the CURRENT frame for that absolute time (wraps to frame 0), skipping the missed frame rather than replaying it
   - Expected: frame_wrapped.pixels[0] equals `_RED`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("advances frames at the manifest cadence as a pure function of injected time, dropping missed frames instead of stalling")
host_motion_background_provider_reset()
host_background_image_provider_reset()
if val source = _create_two_frame_source():
    step("t=0 selects frame 0 (red)")
    val frame0 = source.frame_for_time(0)
    expect(frame0.width).to_equal(4)
    expect(frame0.pixels[0]).to_equal(_RED)
    step("t=one interval selects frame 1 (blue)")
    val frame1 = source.frame_for_time(_INTERVAL)
    expect(frame1.pixels[0]).to_equal(_BLUE)
    step("A caller that falls behind (t jumps to 2.5 intervals) lands on the CURRENT frame for that absolute time (wraps to frame 0), skipping the missed frame rather than replaying it")
    val frame_wrapped = source.frame_for_time(_INTERVAL * 2 + _INTERVAL / 2)
    expect(frame_wrapped.pixels[0]).to_equal(_RED)
else:
    expect(true).to_equal(false)
```

</details>

<details>
<summary>Advanced: exposes next_frame_due so the present loop marks dirty exactly when a frame is due, once per due value (I8)</summary>

#### exposes next_frame_due so the present loop marks dirty exactly when a frame is due, once per due value (I8)

- exposes next_frame_due so the present loop marks dirty exactly when a frame is due, once per due value (I8)
- With no source registered the seam reports -1 (never due) and the predicate never fires
   - Expected: shared_wm_motion_background_next_due_micros() equals `-1`
   - Expected: shared_wm_motion_dirty_due(999999999, -1, -1) is false
- Consuming the frame for t=0 schedules the next frame at exactly one interval
   - Expected: due equals `_INTERVAL`
- Before the due time the dirty trigger does NOT fire (not per-tick)
   - Expected: shared_wm_motion_dirty_due(due - 1, due, -1) is false
- At the due time it fires
   - Expected: shared_wm_motion_dirty_due(due, due, -1) is true
- After firing once for this due value it stays quiet until the due value advances
   - Expected: shared_wm_motion_dirty_due(due + 50000, due, due) is false
- Consuming the due frame advances next-due and re-arms the trigger
   - Expected: due2 equals `_INTERVAL * 2`
   - Expected: shared_wm_motion_dirty_due(due2, due2, due) is true
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("exposes next_frame_due so the present loop marks dirty exactly when a frame is due, once per due value (I8)")
host_motion_background_provider_reset()
host_background_image_provider_reset()
step("With no source registered the seam reports -1 (never due) and the predicate never fires")
shared_wm_scene_register_motion_background_source(nil)
expect(shared_wm_motion_background_next_due_micros()).to_equal(-1)
expect(shared_wm_motion_dirty_due(999999999, -1, -1)).to_equal(false)
if val source = _create_two_frame_source():
    shared_wm_scene_register_motion_background_source(source)
    step("Consuming the frame for t=0 schedules the next frame at exactly one interval")
    source.frame_for_time(0)
    val due = shared_wm_motion_background_next_due_micros()
    expect(due).to_equal(_INTERVAL)
    step("Before the due time the dirty trigger does NOT fire (not per-tick)")
    expect(shared_wm_motion_dirty_due(due - 1, due, -1)).to_equal(false)
    step("At the due time it fires")
    expect(shared_wm_motion_dirty_due(due, due, -1)).to_equal(true)
    step("After firing once for this due value it stays quiet until the due value advances")
    expect(shared_wm_motion_dirty_due(due + 50000, due, due)).to_equal(false)
    step("Consuming the due frame advances next-due and re-arms the trigger")
    source.frame_for_time(due)
    val due2 = shared_wm_motion_background_next_due_micros()
    expect(due2).to_equal(_INTERVAL * 2)
    expect(shared_wm_motion_dirty_due(due2, due2, due)).to_equal(true)
    shared_wm_scene_register_motion_background_source(nil)
else:
    expect(true).to_equal(false)
```

</details>


</details>

#### degrades a single-frame set to a static image: valid frame, but never due again

- degrades a single-frame set to a static image: valid frame, but never due again
   - Expected: frame.pixels[0] equals `_RED`
- next_frame_due is the never-due sentinel, so the dirty trigger cannot fire again
   - Expected: host_motion_background_provider_next_due_micros() equals `_NEVER_DUE`
   - Expected: shared_wm_motion_dirty_due(999999999999, _NEVER_DUE, -1) is false
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("degrades a single-frame set to a static image: valid frame, but never due again")
host_motion_background_provider_reset()
host_background_image_provider_reset()
val red = _write_frame("{_fixture_dir()}/only_frame.ppm", _RED)
val manifest = _write_manifest("{_fixture_dir()}/single.manifest", ["{_INTERVAL}", red])
match HostMotionBackgroundSource.create(manifest, 4, 4, "stretch"):
    Ok(source):
        val frame = source.frame_for_time(0)
        expect(frame.pixels[0]).to_equal(_RED)
        step("next_frame_due is the never-due sentinel, so the dirty trigger cannot fire again")
        expect(host_motion_background_provider_next_due_micros()).to_equal(_NEVER_DUE)
        expect(shared_wm_motion_dirty_due(999999999999, _NEVER_DUE, -1)).to_equal(false)
    Err(message):
        print "unexpected single-frame create failure: {message}"
        expect(true).to_equal(false)
```

</details>

#### routes frames through the kind:image content-hash cache: repeated frames are cache hits, not re-decodes

- routes frames through the kind:image content-hash cache: repeated frames are cache hits, not re-decodes
- First pass over the two frames decodes each once (2 misses)
   - Expected: host_background_image_provider_misses() equals `2`
   - Expected: host_background_image_provider_hits() equals `0`
- The loop wrapping back to frame 0 is a content-hash cache hit
   - Expected: host_background_image_provider_misses() equals `2`
   - Expected: host_background_image_provider_hits() equals `1`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes frames through the kind:image content-hash cache: repeated frames are cache hits, not re-decodes")
host_motion_background_provider_reset()
host_background_image_provider_reset()
if val source = _create_two_frame_source():
    step("First pass over the two frames decodes each once (2 misses)")
    source.frame_for_time(0)
    source.frame_for_time(_INTERVAL)
    expect(host_background_image_provider_misses()).to_equal(2)
    expect(host_background_image_provider_hits()).to_equal(0)
    step("The loop wrapping back to frame 0 is a content-hash cache hit")
    source.frame_for_time(_INTERVAL * 2)
    expect(host_background_image_provider_misses()).to_equal(2)
    expect(host_background_image_provider_hits()).to_equal(1)
else:
    expect(true).to_equal(false)
```

</details>

#### fails loudly at resolve time: no source registered, and a frame that is unreadable with no prior good decode

- fails loudly at resolve time: no source registered, and a frame that is unreadable with no prior good decode
- kind:motion with no registered source resolves to the loud unresolved marker
   - Expected: no_source.resolved is false
   - Expected: no_source.color equals `WM_BACKGROUND_UNRESOLVED_MARKER_COLOR`
- A manifest whose frame file does not exist (and was never readable) resolves to the loud marker, never a fabricated frame
   - Expected: resolution.resolved is false
   - Expected: resolution.color equals `WM_BACKGROUND_UNRESOLVED_MARKER_COLOR`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails loudly at resolve time: no source registered, and a frame that is unreadable with no prior good decode")
host_motion_background_provider_reset()
host_background_image_provider_reset()
step("kind:motion with no registered source resolves to the loud unresolved marker")
shared_wm_scene_register_motion_background_source(nil)
val no_source = shared_wm_scene_resolve_background(_motion_background(""), 4, 4, 0)
expect(no_source.resolved).to_equal(false)
expect(no_source.color).to_equal(WM_BACKGROUND_UNRESOLVED_MARKER_COLOR)
step("A manifest whose frame file does not exist (and was never readable) resolves to the loud marker, never a fabricated frame")
val manifest = _write_manifest("{_fixture_dir()}/ghost.manifest", ["{_INTERVAL}", "{_fixture_dir()}/ghost_frame.ppm", "{_fixture_dir()}/ghost_frame2.ppm"])
match HostMotionBackgroundSource.create(manifest, 4, 4, "stretch"):
    Ok(source):
        shared_wm_scene_register_motion_background_source(source)
        val resolution = shared_wm_scene_resolve_background(_motion_background(manifest), 4, 4, 0)
        expect(resolution.resolved).to_equal(false)
        expect(resolution.color).to_equal(WM_BACKGROUND_UNRESOLVED_MARKER_COLOR)
        expect(resolution.error_message).to_contain("no frame")
        shared_wm_scene_register_motion_background_source(nil)
    Err(message):
        print "unexpected ghost-manifest create failure: {message}"
        expect(true).to_equal(false)
```

</details>

#### renders motion frames through the stateless executor with injected time: same scene, different t_micros, different background pixels; chrome stays on top

- renders motion frames through the stateless executor with injected time: same scene, different t_micros, different background pixels; chrome stays on top
- The source is constructed at the desktop size (100x140) — the real wiring (init_host_wm) does the same with cfg.initial_size, so the blitted frame covers the whole canvas
- At t=0 the desktop area (between the 44px command lane and the taskbar) shows frame 0 (red)
   - Expected: backend_t0.pixels[60 * 100 + 10] equals `_RED`
- At t=one interval the SAME scene renders frame 1 (blue) — time is the only input that changed
   - Expected: backend_t1.pixels[60 * 100 + 10] equals `_BLUE`
- Chrome still draws on top of the motion frame (command-lane band)
   - Expected: backend_t1.pixels[0 * 100 + 0] equals `theme.command_lane`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("renders motion frames through the stateless executor with injected time: same scene, different t_micros, different background pixels; chrome stays on top")
host_motion_background_provider_reset()
host_background_image_provider_reset()
step("The source is constructed at the desktop size (100x140) — the real wiring (init_host_wm) does the same with cfg.initial_size, so the blitted frame covers the whole canvas")
val manifest = _write_two_frame_manifest()
var scene_source: HostMotionBackgroundSource? = nil
match HostMotionBackgroundSource.create(manifest, 100, 140, "stretch"):
    Ok(created):
        scene_source = created
    Err(message):
        print "unexpected scene-source create failure: {message}"
if val source = scene_source:
    shared_wm_scene_register_motion_background_source(source)
    val scene = SharedWmScene(width: 100, height: 140, backend: "motion-spec", windows: [], background: _motion_background(manifest))
    step("At t=0 the desktop area (between the 44px command lane and the taskbar) shows frame 0 (red)")
    val backend_t0 = TestPixelBackend.create(100, 140, 0u32)
    shared_wm_scene_render_to_backend(backend_t0, scene, 0)
    expect(backend_t0.pixels[60 * 100 + 10]).to_equal(_RED)
    step("At t=one interval the SAME scene renders frame 1 (blue) — time is the only input that changed")
    val backend_t1 = TestPixelBackend.create(100, 140, 0u32)
    shared_wm_scene_render_to_backend(backend_t1, scene, _INTERVAL)
    expect(backend_t1.pixels[60 * 100 + 10]).to_equal(_BLUE)
    step("Chrome still draws on top of the motion frame (command-lane band)")
    val theme = wm_chrome_theme()
    expect(backend_t1.pixels[0 * 100 + 0]).to_equal(theme.command_lane)
    shared_wm_scene_register_motion_background_source(nil)
else:
    expect(true).to_equal(false)
```

</details>

#### animates through the real production caller (shared_mdi_framebuffer_scene wrapper), not just the raw executor: same scene rebuilt at t and t+interval yields different background pixels

- animates through the real production caller (shared_mdi_framebuffer_scene wrapper), not just the raw executor: same scene rebuilt at t and t+interval yields different background pixels
- Fix-round regression guard: render_shared_mdi_framebuffer_scene_for_windows used to hardcode t_micros=0 when forwarding to render_shared_mdi_framebuffer_scene_for_simple_gui_scene, so a registered motion source could never advance no matter what a caller passed in. This exercises the actual production wrapper (shared_mdi_framebuffer_scene.spl), not the lower-level shared_wm_scene_render_to_backend executor the previous test already covers.
- t=0 through the production wrapper resolves frame 0 (red)
   - Expected: frame0_px equals `_RED`
- t=one interval through the SAME production wrapper call resolves frame 1 (blue) — proves t_micros reaches the resolver via the real caller, not a hardcoded 0
   - Expected: frame1_px equals `_BLUE`
- The two production-lane renders are not pixel-identical (t_micros genuinely reached the resolver)
   - Expected: frame0_equals_frame1 is false
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("animates through the real production caller (shared_mdi_framebuffer_scene wrapper), not just the raw executor: same scene rebuilt at t and t+interval yields different background pixels")
host_motion_background_provider_reset()
host_background_image_provider_reset()
step("Fix-round regression guard: render_shared_mdi_framebuffer_scene_for_windows used to hardcode t_micros=0 when forwarding to render_shared_mdi_framebuffer_scene_for_simple_gui_scene, so a registered motion source could never advance no matter what a caller passed in. This exercises the actual production wrapper (shared_mdi_framebuffer_scene.spl), not the lower-level shared_wm_scene_render_to_backend executor the previous test already covers.")
val manifest = _write_two_frame_manifest()
var scene_source: HostMotionBackgroundSource? = nil
match HostMotionBackgroundSource.create(manifest, 100, 140, "stretch"):
    Ok(created):
        scene_source = created
    Err(message):
        print "unexpected production-lane source create failure: {message}"
if val source = scene_source:
    shared_wm_scene_register_motion_background_source(source)
    val scene = SharedWmScene(width: 100, height: 140, backend: "motion-production-lane", windows: [], background: _motion_background(manifest))
    step("t=0 through the production wrapper resolves frame 0 (red)")
    val frame0 = render_shared_mdi_framebuffer_scene_for_simple_gui_scene(scene, 0)
    val frame0_px = frame0.pixels[60 * 100 + 10]
    expect(frame0_px).to_equal(_RED)
    step("t=one interval through the SAME production wrapper call resolves frame 1 (blue) — proves t_micros reaches the resolver via the real caller, not a hardcoded 0")
    val frame1 = render_shared_mdi_framebuffer_scene_for_simple_gui_scene(scene, _INTERVAL)
    val frame1_px = frame1.pixels[60 * 100 + 10]
    expect(frame1_px).to_equal(_BLUE)
    step("The two production-lane renders are not pixel-identical (t_micros genuinely reached the resolver)")
    val frame0_equals_frame1 = frame0_px == frame1_px
    expect(frame0_equals_frame1).to_equal(false)
    shared_wm_scene_register_motion_background_source(nil)
else:
    expect(true).to_equal(false)
```

</details>

#### never fires the dirty trigger before a real first due is established (no spurious epoch fire from an uninitialized 0 sentinel)

- never fires the dirty trigger before a real first due is established (no spurious epoch fire from an uninitialized 0 sentinel)
- Fix-round regression guard: _motion_next_due_micros used to start at 0, which the seam read as 'due at the epoch' — always <= any real wall-clock now, so the very first present-loop iteration after registration fired a spurious dirty trigger before any frame had ever been selected. It now starts at the same -1 'not yet scheduled' sentinel the seam already uses for 'no source registered', so the trigger cannot fire until a real due timestamp exists.
   - Expected: host_motion_background_provider_next_due_micros() equals `-1`
- A huge real-looking wall-clock 'now' does not fire against the not-yet-scheduled sentinel
   - Expected: shared_wm_motion_dirty_due(1893456000000000, -1, -1) is false
- Before the source has ever resolved a frame, the sentinel still holds and the seam stays quiet
   - Expected: source.next_frame_due_micros() equals `-1`
   - Expected: shared_wm_motion_dirty_due(1893456000000000, source.next_frame_due_micros(), -1) is false
- Only once frame_for_time establishes a real due (mirroring the registration-time seed in host_compositor_entry.ensure_host_motion_background_source_registered) does a due value exist to fire against
   - Expected: real_due equals `1893456000000000 + _INTERVAL`
   - Expected: shared_wm_motion_dirty_due(real_due, real_due, -1) is true
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("never fires the dirty trigger before a real first due is established (no spurious epoch fire from an uninitialized 0 sentinel)")
host_motion_background_provider_reset()
step("Fix-round regression guard: _motion_next_due_micros used to start at 0, which the seam read as 'due at the epoch' — always <= any real wall-clock now, so the very first present-loop iteration after registration fired a spurious dirty trigger before any frame had ever been selected. It now starts at the same -1 'not yet scheduled' sentinel the seam already uses for 'no source registered', so the trigger cannot fire until a real due timestamp exists.")
expect(host_motion_background_provider_next_due_micros()).to_equal(-1)
step("A huge real-looking wall-clock 'now' does not fire against the not-yet-scheduled sentinel")
expect(shared_wm_motion_dirty_due(1893456000000000, -1, -1)).to_equal(false)
val manifest = _write_two_frame_manifest()
match HostMotionBackgroundSource.create(manifest, 4, 4, "stretch"):
    Ok(source):
        step("Before the source has ever resolved a frame, the sentinel still holds and the seam stays quiet")
        expect(source.next_frame_due_micros()).to_equal(-1)
        expect(shared_wm_motion_dirty_due(1893456000000000, source.next_frame_due_micros(), -1)).to_equal(false)
        step("Only once frame_for_time establishes a real due (mirroring the registration-time seed in host_compositor_entry.ensure_host_motion_background_source_registered) does a due value exist to fire against")
        source.frame_for_time(1893456000000000)
        val real_due = source.next_frame_due_micros()
        expect(real_due).to_equal(1893456000000000 + _INTERVAL)
        expect(shared_wm_motion_dirty_due(real_due, real_due, -1)).to_equal(true)
    Err(message):
        print "unexpected sentinel-test source create failure: {message}"
        expect(true).to_equal(false)
```

</details>

#### self-re-arms at the seam: shared_wm_motion_background_consume_due advances next-due without any render-side consumption, firing exactly once per interval across 2 intervals

- self-re-arms at the seam: shared_wm_motion_background_consume_due advances next-due without any render-side consumption, firing exactly once per interval across 2 intervals
- Fix-round regression guard: the present loop's dirty trigger only re-arms when next-due advances to a NEW value, which used to depend entirely on render_frame() consuming a motion frame — but no production render lane actually did that, so the trigger fired once and then went permanently stale. shared_wm_motion_background_consume_due lets the seam itself advance next-due, independent of whether anything renders.
- Seed the first schedule the same way registration does, without going through render at all
   - Expected: due1 equals `_INTERVAL`
- Iteration 1: the trigger fires for due1 and the seam self-re-arms via consume_due, with zero calls to shared_wm_scene_render_to_backend / any render path
   - Expected: due2 equals `_INTERVAL * 2`
- Between due1 and due2 the trigger stays quiet (once-per-due-value, not per-tick)
   - Expected: shared_wm_motion_dirty_due(due1 + 1, due2, last_fired) is false
- Iteration 2: the re-armed trigger fires again for due2, self-re-arming again with no render consumption
   - Expected: due3 equals `_INTERVAL * 3`
   - Expected: fire_count equals `2`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("self-re-arms at the seam: shared_wm_motion_background_consume_due advances next-due without any render-side consumption, firing exactly once per interval across 2 intervals")
host_motion_background_provider_reset()
host_background_image_provider_reset()
step("Fix-round regression guard: the present loop's dirty trigger only re-arms when next-due advances to a NEW value, which used to depend entirely on render_frame() consuming a motion frame — but no production render lane actually did that, so the trigger fired once and then went permanently stale. shared_wm_motion_background_consume_due lets the seam itself advance next-due, independent of whether anything renders.")
if val source = _create_two_frame_source():
    shared_wm_scene_register_motion_background_source(source)
    step("Seed the first schedule the same way registration does, without going through render at all")
    source.frame_for_time(0)
    val due1 = shared_wm_motion_background_next_due_micros()
    expect(due1).to_equal(_INTERVAL)
    var fire_count = 0
    var last_fired: i64 = -1
    step("Iteration 1: the trigger fires for due1 and the seam self-re-arms via consume_due, with zero calls to shared_wm_scene_render_to_backend / any render path")
    if shared_wm_motion_dirty_due(due1, due1, last_fired):
        fire_count = fire_count + 1
        last_fired = due1
        shared_wm_motion_background_consume_due(due1)
    val due2 = shared_wm_motion_background_next_due_micros()
    expect(due2).to_equal(_INTERVAL * 2)
    step("Between due1 and due2 the trigger stays quiet (once-per-due-value, not per-tick)")
    expect(shared_wm_motion_dirty_due(due1 + 1, due2, last_fired)).to_equal(false)
    step("Iteration 2: the re-armed trigger fires again for due2, self-re-arming again with no render consumption")
    if shared_wm_motion_dirty_due(due2, due2, last_fired):
        fire_count = fire_count + 1
        last_fired = due2
        shared_wm_motion_background_consume_due(due2)
    val due3 = shared_wm_motion_background_next_due_micros()
    expect(due3).to_equal(_INTERVAL * 3)
    expect(fire_count).to_equal(2)
    shared_wm_scene_register_motion_background_source(nil)
else:
    expect(true).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `fad75e7e730aaa6e8f1008eb6d87d78736f245abe585e283e15e4622257aa973`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fad75e7e730aaa6e8f1008eb6d87d78736f245abe585e283e15e4622257aa973`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fad75e7e730aaa6e8f1008eb6d87d78736f245abe585e283e15e4622257aa973`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/desktop/wm_background_motion_provider_spec.spl
mirror: doc/06_spec/01_unit/os/desktop/wm_background_motion_provider_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/desktop/wm_background_motion_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/desktop/wm_background_motion_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/desktop/wm_background_motion_provider_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/desktop/wm_background_motion_provider_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loud-fails source construction on a missing manifest, an empty manifest, a bad interval, and an empty frame set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/wm_background_motion_provider_spec.spl:230:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advances frames at the manifest cadence as a pure function of injected time, dropping missed frames instead of stalling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/wm_background_motion_provider_spec.spl:249:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes next_frame_due so the present loop marks dirty exactly when a frame is due, once per due value (I8)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

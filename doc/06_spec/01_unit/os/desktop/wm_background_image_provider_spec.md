# wm_background_image_provider_spec

> BackgroundSpec kind:image (plan item A,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_background_image_provider_spec

BackgroundSpec kind:image (plan item A,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/wm_background_image_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

BackgroundSpec kind:image (plan item A,
doc/03_plan/os/desktop/wm_window_render_api_hardening_plan.md; design
doc/05_design/os/desktop/simple_gui_internal_window_impl_spec.md 'Phase-2
Provider Design') extends the existing loud-fail background contract with a
real fs-backed image provider: source resolution, per-fit resampling
(cover/contain/stretch/tile), a content-hash-keyed cache, and stale-serve
semantics that avoid a wallpaper flash on a transient read/decode error.

This spec pins invariants I1-I8 from the design's invariant table:
  I1 kind:color stays byte-identical to today.
  I2 unknown kind / kind:image with no provider / kind:motion still fails loud.
  I3 the executor stays stateless; caching lives on the compositor provider.
  I4 no per-pixel FFI: the executor blits one resampled buffer.
  I5 cache key = (content_hash(source_bytes), target_w, target_h, fit).
  I6 stale-serve returns the last-good surface + stale:true, marker only
     when there is no prior good surface.
  I7 the image background must not mask desktop chrome (command lane /
     taskbar bands still draw on top of the blitted surface).
  I8 (motion cadence) is out of scope for this item -- kind:motion stays
     reserved and is asserted to still hit the loud marker, not implemented.

## Scenarios

### BackgroundSpec kind:image provider (background_image_provider + window_scene resolver)

#### resolves kind:color byte-identical to today (I1)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves kind:color byte-identical to today (I1)
- A plain color BackgroundSpec resolves with no surface, regardless of target size
   - Expected: resolution.resolved is true
   - Expected: resolution.color equals `0xFF223344u32`
   - Expected: resolution.stale is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("resolves kind:color byte-identical to today (I1)")
step("A plain color BackgroundSpec resolves with no surface, regardless of target size")
val resolution = shared_wm_scene_resolve_background(shared_wm_background_color(0xFF223344u32), 100, 80)
expect(resolution.resolved).to_equal(true)
expect(resolution.color).to_equal(0xFF223344u32)
expect(resolution.stale).to_equal(false)
```

</details>

#### fails loudly with the unresolved marker for kind:image with no provider registered, and for kind:motion (I2, I8)

- fails loudly with the unresolved marker for kind:image with no provider registered, and for kind:motion (I2, I8)
- No provider is registered in this test
   - Expected: image_resolution.resolved is false
   - Expected: image_resolution.color equals `WM_BACKGROUND_UNRESOLVED_MARKER_COLOR`
- kind:motion is still reserved and hits the same loud marker path
   - Expected: motion_resolution.resolved is false
   - Expected: motion_resolution.color equals `WM_BACKGROUND_UNRESOLVED_MARKER_COLOR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails loudly with the unresolved marker for kind:image with no provider registered, and for kind:motion (I2, I8)")
step("No provider is registered in this test")
shared_wm_scene_register_background_image_provider(nil)
val image_bg = _image_background("some/path.ppm", "cover")
val image_resolution = shared_wm_scene_resolve_background(image_bg, 40, 40)
expect(image_resolution.resolved).to_equal(false)
expect(image_resolution.color).to_equal(WM_BACKGROUND_UNRESOLVED_MARKER_COLOR)
step("kind:motion is still reserved and hits the same loud marker path")
val motion_bg = BackgroundSpec(kind: WM_BACKGROUND_KIND_MOTION, color: 0xFF000000u32, source: "", fit: "cover")
val motion_resolution = shared_wm_scene_resolve_background(motion_bg, 40, 40)
expect(motion_resolution.resolved).to_equal(false)
expect(motion_resolution.color).to_equal(WM_BACKGROUND_UNRESOLVED_MARKER_COLOR)
```

</details>

#### resolves kind:image through a registered provider, returning a decoded+resampled surface

- resolves kind:image through a registered provider, returning a decoded+resampled surface
- Register a fresh HostBackgroundImageProvider and resolve a real PPM fixture
   - Expected: resolution.resolved is true
   - Expected: resolution.stale is false
   - Expected: surface.width equals `4`
   - Expected: surface.height equals `4`
   - Expected: surface.pixels.len() equals `16`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("resolves kind:image through a registered provider, returning a decoded+resampled surface")
step("Register a fresh HostBackgroundImageProvider and resolve a real PPM fixture")
host_background_image_provider_reset()
val provider = HostBackgroundImageProvider.create()
shared_wm_scene_register_background_image_provider(provider)
val path = _write_quad_fixture()
val resolution = shared_wm_scene_resolve_background(_image_background(path, "stretch"), 4, 4)
shared_wm_scene_register_background_image_provider(nil)
expect(resolution.resolved).to_equal(true)
expect(resolution.stale).to_equal(false)
if val surface = resolution.surface:
    expect(surface.width).to_equal(4)
    expect(surface.height).to_equal(4)
    expect(surface.pixels.len()).to_equal(16)
else:
    expect(true).to_equal(false)
```

</details>

#### each fit policy produces the documented geometry (cover/contain/stretch/tile)

- each fit policy produces the documented geometry (cover/contain/stretch/tile)
- stretch to 4x4: each source pixel becomes a 2x2 quadrant block
   - Expected: s.pixels[0 * 4 + 0] equals `_RED`
   - Expected: s.pixels[0 * 4 + 3] equals `_GREEN`
   - Expected: s.pixels[3 * 4 + 0] equals `_BLUE`
   - Expected: s.pixels[3 * 4 + 3] equals `_YELLOW`
   - Expected: true is false
- cover to 4x2: crops to the top row (red/green), bottom row (blue/yellow) is discarded
   - Expected: s.pixels[0 * 4 + 0] equals `_RED`
   - Expected: s.pixels[0 * 4 + 3] equals `_GREEN`
   - Expected: s.pixels[1 * 4 + 0] equals `_RED`
   - Expected: s.pixels[1 * 4 + 3] equals `_GREEN`
   - Expected: true is false
- contain to 4x2: the 2x2 source stays square, letterboxed left/right with the desktop-chrome fill color
   - Expected: s.pixels[0 * 4 + 0] equals `theme.desktop_bg`
   - Expected: s.pixels[0 * 4 + 3] equals `theme.desktop_bg`
   - Expected: s.pixels[0 * 4 + 1] equals `_RED`
   - Expected: s.pixels[0 * 4 + 2] equals `_GREEN`
   - Expected: s.pixels[1 * 4 + 1] equals `_BLUE`
   - Expected: s.pixels[1 * 4 + 2] equals `_YELLOW`
   - Expected: true is false
- tile to 4x4: the 2x2 source repeats twice in each direction, no resampling
   - Expected: s.pixels[0 * 4 + 0] equals `_RED`
   - Expected: s.pixels[0 * 4 + 2] equals `_RED`
   - Expected: s.pixels[1 * 4 + 0] equals `_BLUE`
   - Expected: s.pixels[2 * 4 + 2] equals `_RED`
   - Expected: s.pixels[3 * 4 + 3] equals `_YELLOW`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("each fit policy produces the documented geometry (cover/contain/stretch/tile)")
host_background_image_provider_reset()
val provider = HostBackgroundImageProvider.create()
shared_wm_scene_register_background_image_provider(provider)
val path = _write_quad_fixture()

step("stretch to 4x4: each source pixel becomes a 2x2 quadrant block")
val stretched = shared_wm_scene_resolve_background(_image_background(path, "stretch"), 4, 4)
if val s = stretched.surface:
    expect(s.pixels[0 * 4 + 0]).to_equal(_RED)
    expect(s.pixels[0 * 4 + 3]).to_equal(_GREEN)
    expect(s.pixels[3 * 4 + 0]).to_equal(_BLUE)
    expect(s.pixels[3 * 4 + 3]).to_equal(_YELLOW)
else:
    expect(true).to_equal(false)

step("cover to 4x2: crops to the top row (red/green), bottom row (blue/yellow) is discarded")
val covered = shared_wm_scene_resolve_background(_image_background(path, "cover"), 4, 2)
if val s = covered.surface:
    expect(s.pixels[0 * 4 + 0]).to_equal(_RED)
    expect(s.pixels[0 * 4 + 3]).to_equal(_GREEN)
    expect(s.pixels[1 * 4 + 0]).to_equal(_RED)
    expect(s.pixels[1 * 4 + 3]).to_equal(_GREEN)
else:
    expect(true).to_equal(false)

step("contain to 4x2: the 2x2 source stays square, letterboxed left/right with the desktop-chrome fill color")
val theme = wm_chrome_theme()
val contained = shared_wm_scene_resolve_background(_image_background(path, "contain"), 4, 2)
if val s = contained.surface:
    expect(s.pixels[0 * 4 + 0]).to_equal(theme.desktop_bg)
    expect(s.pixels[0 * 4 + 3]).to_equal(theme.desktop_bg)
    expect(s.pixels[0 * 4 + 1]).to_equal(_RED)
    expect(s.pixels[0 * 4 + 2]).to_equal(_GREEN)
    expect(s.pixels[1 * 4 + 1]).to_equal(_BLUE)
    expect(s.pixels[1 * 4 + 2]).to_equal(_YELLOW)
else:
    expect(true).to_equal(false)

step("tile to 4x4: the 2x2 source repeats twice in each direction, no resampling")
val tiled = shared_wm_scene_resolve_background(_image_background(path, "tile"), 4, 4)
if val s = tiled.surface:
    expect(s.pixels[0 * 4 + 0]).to_equal(_RED)
    expect(s.pixels[0 * 4 + 2]).to_equal(_RED)
    expect(s.pixels[1 * 4 + 0]).to_equal(_BLUE)
    expect(s.pixels[2 * 4 + 2]).to_equal(_RED)
    expect(s.pixels[3 * 4 + 3]).to_equal(_YELLOW)
else:
    expect(true).to_equal(false)

shared_wm_scene_register_background_image_provider(nil)
```

</details>

#### counts cache hits and misses as real events (I5)

- counts cache hits and misses as real events (I5)
- Cache/counter state is process-global module state (see background_image_provider.spl's module-var note); reset it first for a clean count
- First resolve at a given (content-hash, target_w, target_h, fit) key is a miss
   - Expected: host_background_image_provider_misses() equals `1`
   - Expected: host_background_image_provider_hits() equals `0`
- An identical resolve is a cache hit, not a second decode
   - Expected: host_background_image_provider_misses() equals `1`
   - Expected: host_background_image_provider_hits() equals `1`
- A different target size or fit is a different key, so it is a miss again
   - Expected: host_background_image_provider_misses() equals `2`
   - Expected: host_background_image_provider_misses() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("counts cache hits and misses as real events (I5)")
step("Cache/counter state is process-global module state (see background_image_provider.spl's module-var note); reset it first for a clean count")
host_background_image_provider_reset()
val provider = HostBackgroundImageProvider.create()
val path = _write_quad_fixture()
step("First resolve at a given (content-hash, target_w, target_h, fit) key is a miss")
provider.resolve(path, 8, 8, "cover")
expect(host_background_image_provider_misses()).to_equal(1)
expect(host_background_image_provider_hits()).to_equal(0)
step("An identical resolve is a cache hit, not a second decode")
provider.resolve(path, 8, 8, "cover")
expect(host_background_image_provider_misses()).to_equal(1)
expect(host_background_image_provider_hits()).to_equal(1)
step("A different target size or fit is a different key, so it is a miss again")
provider.resolve(path, 16, 16, "cover")
expect(host_background_image_provider_misses()).to_equal(2)
provider.resolve(path, 8, 8, "tile")
expect(host_background_image_provider_misses()).to_equal(3)
```

</details>

#### serves the last-good surface with stale:true after a resolve error, and only marks loud when there is no prior good surface (I6)

- serves the last-good surface with stale:true after a resolve error, and only marks loud when there is no prior good surface (I6)
- A source that has never resolved successfully hard-fails with no stale flag
   - Expected: first.resolved is false
   - Expected: first.stale is false
- A successful resolve populates last-good for this (source, target, fit)
   - Expected: good.resolved is true
   - Expected: good.stale is false
- Removing the source file and re-resolving serves the last-good surface, marked stale, with a diagnostic
   - Expected: stale.resolved is true
   - Expected: stale.stale is true
   - Expected: stale_surface.pixels.len() equals `good_surface.pixels.len()`
   - Expected: mismatch is false
   - Expected: true is false
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("serves the last-good surface with stale:true after a resolve error, and only marks loud when there is no prior good surface (I6)")
host_background_image_provider_reset()
val provider = HostBackgroundImageProvider.create()
shared_wm_scene_register_background_image_provider(provider)
val missing_path = "{_fixture_dir()}/does_not_exist.ppm"
step("A source that has never resolved successfully hard-fails with no stale flag")
val first = shared_wm_scene_resolve_background(_image_background(missing_path, "cover"), 4, 4)
expect(first.resolved).to_equal(false)
expect(first.stale).to_equal(false)

val path = "{_fixture_dir()}/stale_target.ppm"
_write_fixture(path, [_RED, _GREEN, _BLUE, _YELLOW])
step("A successful resolve populates last-good for this (source, target, fit)")
val good = shared_wm_scene_resolve_background(_image_background(path, "cover"), 4, 4)
expect(good.resolved).to_equal(true)
expect(good.stale).to_equal(false)

step("Removing the source file and re-resolving serves the last-good surface, marked stale, with a diagnostic")
# File.delete (the class static method) hits an unrelated,
# pre-existing interpreter bug ("unknown property or method 'path'
# on String") independent of this change; the free extern-backed
# file_delete function works correctly, so use that instead.
file_delete(path)
val stale = shared_wm_scene_resolve_background(_image_background(path, "cover"), 4, 4)
expect(stale.resolved).to_equal(true)
expect(stale.stale).to_equal(true)
expect(stale.error_message).to_contain("last-good")
if val good_surface = good.surface:
    if val stale_surface = stale.surface:
        expect(stale_surface.pixels.len()).to_equal(good_surface.pixels.len())
        var i = 0
        var mismatch = false
        while i < good_surface.pixels.len():
            if good_surface.pixels[i] != stale_surface.pixels[i]:
                mismatch = true
            i = i + 1
        expect(mismatch).to_equal(false)
    else:
        expect(true).to_equal(false)
else:
    expect(true).to_equal(false)
shared_wm_scene_register_background_image_provider(nil)
```

</details>

#### reflects changed source content on the next frame (change-then-reresolve, distinct from stale-serve)

- reflects changed source content on the next frame (change-then-reresolve, distinct from stale-serve)
- Resolve once, then overwrite the source with different content
   - Expected: s.pixels[0] equals `_RED`
   - Expected: true is false
   - Expected: after.stale is false
   - Expected: s.pixels[0] equals `_BLUE`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reflects changed source content on the next frame (change-then-reresolve, distinct from stale-serve)")
step("Resolve once, then overwrite the source with different content")
host_background_image_provider_reset()
val provider = HostBackgroundImageProvider.create()
shared_wm_scene_register_background_image_provider(provider)
val path = "{_fixture_dir()}/live_update.ppm"
_write_fixture(path, [_RED, _RED, _RED, _RED])
val before = shared_wm_scene_resolve_background(_image_background(path, "stretch"), 2, 2)
if val s = before.surface:
    expect(s.pixels[0]).to_equal(_RED)
else:
    expect(true).to_equal(false)
_write_fixture(path, [_BLUE, _BLUE, _BLUE, _BLUE])
val after = shared_wm_scene_resolve_background(_image_background(path, "stretch"), 2, 2)
expect(after.stale).to_equal(false)
if val s = after.surface:
    expect(s.pixels[0]).to_equal(_BLUE)
else:
    expect(true).to_equal(false)
shared_wm_scene_register_background_image_provider(nil)
```

</details>

#### blits the resolved surface before chrome, so command-lane/taskbar bands still draw on top (I3, I4, I7)

- blits the resolved surface before chrome, so command-lane/taskbar bands still draw on top (I3, I4, I7)
- Build a windowless scene whose background is a resolvable image; canvas is tall enough (140) to leave a real desktop gap between the fixed 44px command lane and 56px taskbar bands
- A desktop-area pixel (y=60, inside [44,84), left half of the stretched quad image) shows the source's red, not a flat clear color
   - Expected: desktop_probe equals `_RED`
- The command-lane band (y in [0,44)) still paints chrome on top of the image
   - Expected: backend.pixels[0 * 100 + 0] equals `theme.command_lane`
- Rendering the identical scene into a second, differently-initialized backend gives identical pixels (lane parity)
   - Expected: mismatch is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("blits the resolved surface before chrome, so command-lane/taskbar bands still draw on top (I3, I4, I7)")
step("Build a windowless scene whose background is a resolvable image; canvas is tall enough (140) to leave a real desktop gap between the fixed 44px command lane and 56px taskbar bands")
val provider = HostBackgroundImageProvider.create()
shared_wm_scene_register_background_image_provider(provider)
val path = _write_quad_fixture()
val scene = SharedWmScene(width: 100, height: 140, backend: "executor-spec", windows: [], background: _image_background(path, "stretch"))
val backend = TestPixelBackend.create(100, 140, 0u32)
shared_wm_scene_render_to_backend(backend, scene)
step("A desktop-area pixel (y=60, inside [44,84), left half of the stretched quad image) shows the source's red, not a flat clear color")
val desktop_probe = backend.pixels[60 * 100 + 10]
expect(desktop_probe).to_equal(_RED)
step("The command-lane band (y in [0,44)) still paints chrome on top of the image")
val theme = wm_chrome_theme()
expect(backend.pixels[0 * 100 + 0]).to_equal(theme.command_lane)
step("Rendering the identical scene into a second, differently-initialized backend gives identical pixels (lane parity)")
val backend_b = TestPixelBackend.create(100, 140, 0xFFFFFFFFu32)
shared_wm_scene_render_to_backend(backend_b, scene)
var i = 0
var mismatch = false
while i < backend.pixels.len():
    if backend.pixels[i] != backend_b.pixels[i]:
        mismatch = true
    i = i + 1
expect(mismatch).to_equal(false)
shared_wm_scene_register_background_image_provider(nil)
```

</details>

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d1914c2836fa3d04157f9add05592390a926e1a62fe7a868ecfe87ca5bcf9949`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1914c2836fa3d04157f9add05592390a926e1a62fe7a868ecfe87ca5bcf9949`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1914c2836fa3d04157f9add05592390a926e1a62fe7a868ecfe87ca5bcf9949`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/desktop/wm_background_image_provider_spec.spl
mirror: doc/06_spec/01_unit/os/desktop/wm_background_image_provider_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/desktop/wm_background_image_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/desktop/wm_background_image_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/desktop/wm_background_image_provider_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/desktop/wm_background_image_provider_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves kind:color byte-identical to today (I1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/wm_background_image_provider_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails loudly with the unresolved marker for kind:image with no provider registered, and for kind:motion (I2, I8)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/wm_background_image_provider_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves kind:image through a registered provider, returning a decoded+resampled surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

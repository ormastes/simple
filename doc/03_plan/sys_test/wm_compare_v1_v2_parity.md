# wm_compare V1/V2 Parity — System Test Plan

**Status:** draft &middot; **Date:** 2026-04-14 &middot; **Owner:** GUI stack WG &middot;
**Plan item:** #2 in `doc/03_plan/gui_drawing_layer_variations.md` (Work plan
table) &middot; **Target artifact:** `test/sys/wm_compare/v1_v2_parity_spec.spl`

Goal: drive the **same** widget scene through V1 (`fb_backend`, baremetal
SimpleOS framebuffer) and V2 (`hosted_backend`, host OS via winit) and
pixel-diff the two captures inside one harness.

---

## 1. Current state of `wm_compare`

The harness lives in `src/app/wm_compare/` (4 files):
`main.spl`, `scene_registry.spl`, `live_capture.spl`, `html_compat.spl`.

| Concern | Where | Notes |
|---|---|---|
| Entry / CLI | `src/app/wm_compare/main.spl:15-19` | `--source=A|B|D|all --scene=<name> [--update-baseline] [--tolerance=...]` |
| Sources today | `src/app/wm_compare/main.spl:3-9` | A = Electron baseline, B = host `BrowserCompositorBackend` (in-process software), D = QEMU SimpleOS via QMP. **No V1 fb_backend, no V2 hosted_backend.** |
| Scene registry | `src/app/wm_compare/scene_registry.spl:18-23,180-208` | `SceneEntry { name, fixture_path, spec: WmSceneSpec }`; built by `build_empty_desktop`, `build_single_window`, `build_four_windows`; resolved via `resolve_scene(name, w, h)`; listed via `list_scene_names()`. |
| Capture imports | `src/app/wm_compare/main.spl:25-31` | `electron_capture`, `qemu_capture.capture_qemu_vm`, `screenshot_compare.{compare_exact, compare_per_channel, compare_pixel_buffers, generate_diff_image}`, `perceptual_compare.compare_perceptual`. |
| Tolerances | `src/app/wm_compare/main.spl:32-34` | `profile_strict`, `profile_text_tolerant`, `profile_wm_default`. |
| Diff strategy | `src/app/wm_compare/main.spl:11-13` | memcmp first, fall through to YIQ perceptual, dump PPM heat-map on mismatch. |
| Baselines on disk | `test/baselines/wm_compare/{empty_desktop,single_window,four_windows,phase5}/` | `B.ppm`, `B_live.ppm`, `report.sdn` per scene. |
| Live PPM helper | `src/app/wm_compare/live_capture.spl` | wraps in-process B-source rendering. |
| HTML report | `src/app/wm_compare/html_compat.spl` | static HTML diff page. |

Today's harness is therefore an **A/B/D triangle around the software
`BrowserCompositorBackend`**, not the locked V1/V2 backends.

## 2. Gap

Item-by-item against item 2 of the plan:

| # | Question | Answer / blocker |
|---|---|---|
| a | Can V1 (`fb_backend`) be driven without booting QEMU? | **No.** `src/os/compositor/fb_backend.spl` requires a real `FramebufferDriver` (`src/os/compositor/fb_backend.spl:9`) and `Ps2Keyboard`; both are baremetal-only constructors. Also the `present_rect` impl in `display_backend.spl:115-118` swaps the whole frame via `swap_buffers`. **(This is the #1 blocker — see §10.)** |
| b | How does V2 (`hosted_backend`) capture a winit surface in a test? | Possible but missing. `src/os/compositor/hosted_backend.spl:23-29` already exposes `rt_winit_buffer_get_pixels(buf) -> [i64]` and `rt_winit_buffer_create` — the buffer can exist with **no winit window attached**, so a test can read pixels directly without `present()`. There is no helper that does this yet. |
| c | Shared coordinate system / canvas size? | Yes, via `WmSceneSpec { width, height, ... }` (`scene_registry.spl:30,206`). Both backends honour `CompositorBackend::width()/height()` (`src/os/compositor/display_backend.spl:25-26`). The contract is already shared; no DPI scaling exists in either backend. |

## 3. Target harness shape

Recommendation: **extend `src/app/wm_compare/`** rather than fork into
`test/system/`. The CLI orchestrator, scene registry, baseline directory,
and HTML report machinery already live there; duplicating them under
`test/system/` would be over-engineering and would break the
"one place that knows how to run a scene" property.

```
src/app/wm_compare/
  main.spl              # add: source=V1, source=V2, source=parity
  scene_registry.spl    # add: build_calculator, build_terminal, build_label_button_row, build_glass_rect
  live_capture.spl      # extend: capture_v1_headless, capture_v2_headless
  html_compat.spl       # unchanged
  fb_headless.spl       # NEW: in-memory FramebufferDriver shim → FramebufferBackend
  hosted_headless.spl   # NEW: rt_winit_buffer_create + get_pixels (no window)
test/sys/wm_compare/
  v1_v2_parity_spec.spl # NEW: thin spec — invokes wm_compare per scene, asserts diff ≤ threshold
```

CLI sketch (Phase 2):

```
bin/simple run src/app/wm_compare/main.spl \
    --source=parity --backends=fb,hosted \
    --scene=calculator --tolerance=aa_aware \
    --width=320 --height=240 [--update-baseline]
```

`--source=parity` is a new mode that runs every backend in `--backends=`,
diffs each pair (here: `fb` vs `hosted`), writes `V1.ppm`, `V2.ppm`,
`V1_vs_V2.diff.ppm`, and a `report.sdn` row per scene under
`test/baselines/wm_compare/<scene>/parity/`.

## 4. Phase-1 scene set

All five exercise different rows of the locked `CompositorBackend` surface
(`src/os/compositor/display_backend.spl:24-37`).

| Scene | Builder (new unless noted) | Trait surface exercised |
|---|---|---|
| `empty_desktop` | existing `scene_registry.spl:28` | `clear`, `fill_rect`, `present` |
| `label_button_row` | new `build_label_button_row` | `fill_rect`, `draw_text`, `draw_char_8x16` |
| `calculator` | new `build_calculator` (uses `os.apps.calculator` widget tree) | `fill_rect`, `draw_text`, `draw_char_8x16`, `present_rect` |
| `terminal` | new `build_terminal` (uses `os.apps.terminal` widget tree) | `draw_char_8x16` heavy, `fill_rect` for cursor |
| `glass_rect` | new `build_glass_rect` (one `glass_panel` SceneElement, already supported by `scene_registry.spl:67`) | `blend_rect`, `blur_region`, `gradient_v`, `read_pixel` |

`single_window` and `four_windows` already exist and remain in the registry
but are **not** in the V1/V2 parity set for Phase 1 — they exercise mostly
the same surface as `empty_desktop` plus decoration chrome and would inflate
review effort without unique signal.

## 5. Capture strategy per backend

| Backend | Path | Why |
|---|---|---|
| **V1 `fb_backend`** | New `fb_headless.spl` — in-memory `FramebufferDriver` (just `width`, `height`, an ARGB `[i64]` array, no PCI/MMIO/PS/2). Wire it into `FramebufferBackend.create` (`fb_backend.spl` constructor). Read pixels back from the array after rendering. | Booting QEMU per scene per CI run is too slow and too flaky. The `qemu_capture.capture_qemu_vm` path stays available for the `--source=D` ground-truth run, but is **not** used for V1 parity. The headless shim is what the locked contract implies — the trait does not depend on real hardware. |
| **V2 `hosted_backend`** | New `hosted_headless.spl` — call `rt_winit_buffer_create(w, h, 0)` to get a buffer id, set `_hosted_buffer_id` / `_hosted_w` / `_hosted_h` (`hosted_backend.spl:32-35`), render, then `rt_winit_buffer_get_pixels(buf)` (`hosted_backend.spl:29`) to read the ARGB array. **Skip `present()` entirely** — no window opens. | Existing `live_capture.spl` is wired for source B (BrowserCompositorBackend), not for `HostedCompositorBackend`. Opening a real winit window in CI is fragile (DISPLAY, virtual frame buffer). We already have an FFI to read pixels from a windowless buffer. |

## 6. Perceptual tolerance

Use `os.compositor.perceptual_compare.compare_perceptual`
(`src/os/compositor/perceptual_compare.spl`) with the
`profile_text_tolerant` preset from
`src/os/compositor/tolerance_profile.spl:31` (and the AA-aware variant for
`glass_rect`).

- Default budget: **≤1 % perceptual delta** measured as `1 - min_match_pct/10000`
  using the YIQ thresholds already encoded in `RegionTolerance`
  (`tolerance_profile.spl:13-18`).
- `screenshot_compare.compare_exact` is too strict — `fb_backend` uses
  `FramebufferDriver.draw_text` (8x16 glyph blit) while `hosted_backend`
  uses the same `get_glyph_8x16` path (`hosted_backend.spl:13`), so glyphs
  should match exactly, **but** `blend_rect` / `blur_region` /
  `gradient_v` go through host FFI on V2 (`rt_winit_buffer_*`) and pure
  Simple math on V1 — sub-pixel rounding will diverge. Antialiasing
  divergence will concentrate on `glass_rect` and around the rounded
  borders of `decoration` chrome.
- `profile_strict` is reserved for the `empty_desktop` scene (no text, no
  blur).

## 7. CI integration

No GitHub Actions workflow currently mentions `wm_compare` (checked
`.github/workflows/*.yml`). Recommend a new job `wm-compare-parity` in
`.github/workflows/cross-platform.yml` (already runs the host-side stack)
that triggers on:

- every push to `main`
- any PR touching `src/os/compositor/**`, `src/lib/common/ui/**`, or
  `src/app/wm_compare/**`
- nightly cron (catch winit FFI regressions)

Trigger rule lives in the workflow's `paths:` filter; spec runner is
`bin/simple test test/sys/wm_compare/v1_v2_parity_spec.spl`. The QEMU
`--source=D` ground-truth pass is **not** in this job — it stays on the
`baremetal-tests.yml` lane (`.github/workflows/baremetal-tests.yml`).

## 8. Relationship to T1 contract tests

`gui_drawing_layer_variations.md` item #1 produces
`test/unit/os/compositor/trait_conformance_spec.spl` (referenced as
`gui_layer_contract.md` in that plan; the contract doc is not yet on disk —
it lands with item #1).

| Layer | Test | What it proves | Failure mode |
|---|---|---|---|
| Unit (T1) | `trait_conformance_spec.spl` | Every `CompositorBackend` impl compiles, every method dispatches, types line up. | Compile-time / dispatch wiring. |
| System (this plan) | `v1_v2_parity_spec.spl` | Two impls, fed the same `WmSceneSpec`, produce visually equal pixel buffers. | Behaviour drift between impls. |

**Do not merge them.** T1 cannot detect a `blur_region` that quietly
returns black; this plan cannot detect a missing trait method (the harness
won't compile). They are complementary.

## 9. Phased rollout

| Phase | Backends | Scenes | Threshold | Gate |
|---|---|---|---|---|
| 1 | fb (headless), hosted (headless) | `empty_desktop` only | none — write `V1.ppm` and `V2.ppm`, human reviews | manual |
| 2 | fb, hosted | + `label_button_row`, `calculator`, `terminal`, `glass_rect` | ≤1 % perceptual via `profile_text_tolerant` (`aa_aware` for `glass_rect`) | CI-blocking on the paths in §7 |
| 3 | fb, hosted, **browser** (`browser_compositor_backend.spl`), **electron** (`electron_capture.spl`) | same 5 | same | golden-image gate from item #8 of `gui_drawing_layer_variations.md` |

## 10. Open questions

1. **#1 blocker — headless `FramebufferDriver`.** Does
   `src/os/drivers/framebuffer/fb_driver.spl` already expose a constructor
   that takes a raw pixel buffer and dimensions, or do we need a new
   `FramebufferDriver.from_buffer(w, h, [i64])`? If the latter, that work
   is a prerequisite to Phase 1 and should be tracked as a sub-task on
   item #2 of `gui_drawing_layer_variations.md`.
2. `_hosted_window_id` / `_hosted_buffer_id` are **module-level vars**
   (`hosted_backend.spl:32-35`). Two `HostedCompositorBackend` instances
   in the same process therefore share state. Phase 1 only renders one
   scene at a time, so this is fine; document the constraint and revisit
   if Phase 3 wants to render V2 + V3 concurrently.
3. `fb_backend.spl:115-118` documents that `present_rect` falls back to a
   full `swap_buffers`. The headless shim has no swap chain — does
   "present" mean "do nothing" or "freeze a snapshot"? Plan assumes
   no-op; confirm with whoever lands the headless driver.
4. Should `live_capture.spl` be renamed / split into per-source modules
   (`live_capture_browser.spl`, `live_capture_v1.spl`,
   `live_capture_v2.spl`) or stay as one file with three entry points?
   Recommendation: stay as one file until it exceeds ~400 lines.
5. `--source=parity` semantics: does it imply `--update-baseline` is
   per-pair (`V1_vs_V2`) or per-source (`V1`, `V2`)? Plan assumes
   per-source.

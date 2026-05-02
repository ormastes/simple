# Phase 5 — Bit-Level Host WM ≡ QEMU OS WM — Report

Date: 2026-04-12

## Summary verdict

**Phase 5 is BLOCKED on Phase 6 (in-guest WM rendering).** The harness
extension works end-to-end and produces the requested artifacts, but the
only two captures that currently exist paint *different scenes, at
different resolutions, via different rasterizers*. Their ~100% pixel
divergence is structurally guaranteed and tells us nothing about whether
the host Simple WM and the QEMU Simple OS WM would agree on the same
rendering task — because neither side is currently doing that task.

The harness itself is verified working. The test it runs is a null test
until both sides render the same scene via comparable paths.

## Harness changes

All changes in `src/app/wm_compare/main.spl`. No other files modified.

| Section | Lines | Purpose |
|---|---|---|
| `CliOpts` struct | 46-69 | Added `source_a_path`, `source_b_path`, `out_dir` fields |
| `parse_opts` | 88-129 | Added `--source-a`, `--source-b`, `--out-dir` parsing |
| `_skip_ppm_ws_and_comments` | 484-498 | Inline PPM whitespace/comment skip |
| `_parse_ppm_int` | 500-509 | Inline PPM integer parse |
| `_parse_ppm_header` | 511-536 | Hand-rolled P6 header parser |
| `_decode_ppm_region` | 538-559 | Decode only an (x0,y0,w,h) region of a P6 body |
| `_decode_ppm_local` | 561-571 | Full-image variant of the above |
| `PpmHandle` struct | 573-583 | Raw bytes + parsed header without eager decode |
| `_load_ppm_handle` | 585-602 | Read + parse header, defer pixel materialization |
| `run_bit_compare_mode` | 604-730 | Phase 5 bit-compare entry point |
| main dispatch | 770-773 | `if opts.mode == "bit-compare": return run_bit_compare_mode(opts)` |

**Why the hand-rolled PPM decoder**: `src/lib/common/image/ppm_decode.spl`
(`decode_ppm_to_argb`) references a `Pair(first: ..., second: ...)`
constructor that has no matching struct definition reachable from the
bit-compare dependency graph, so it errors at runtime with
`function 'Pair' not found`. This is a pre-existing bug in the library
decoder — I did NOT fix it (out of scope and chain-fix rules). The inline
decoder in `main.spl` is a narrow workaround for Phase 5 only.

**Why `PpmHandle` / deferred decode**: source D is 1024×768 (786,432 px).
The interpreter's `array = array + [x]` pattern is O(N²) in the number of
appends and takes too long at that scale. Instead the harness parses
headers only, then decodes just the **overlapping top-left 320×240 region**
of both images — 76,800 pixels each, which the interpreter handles in
seconds. This also gives a spatially meaningful crop (row-aligned) instead
of a flat-buffer memcmp that would silently misalign rows across strides.

## Compare result

Invocation:

```
src/compiler_rust/target/bootstrap/simple run \
  src/app/wm_compare/main.spl -- \
    --mode=bit-compare \
    --source-a=test/baselines/wm_compare/four_windows/B_live.ppm \
    --source-b=test/baselines/wm_compare/engine2d_in_qemu/D.ppm \
    --out-dir=test/baselines/wm_compare/phase5
```

Artifacts written:

- `test/baselines/wm_compare/phase5/B_vs_D_diff.ppm` — 230,415 B P6
  320×240 diff heat-map produced by
  `os.compositor.screenshot_compare.generate_diff_image` over the
  overlapping top-left region.
- `test/baselines/wm_compare/phase5/report.sdn` — full metrics dump.

Headline numbers (from `report.sdn`):

| Metric | Value |
|---|---|
| A dimensions | 320 × 240 (76,800 px) |
| B dimensions | 1024 × 768 (786,432 px) |
| `dimensions_match` | `false` |
| `structurally_valid` | `false` |
| Overlap region compared | 320 × 240 = 76,800 px |
| `exact_match` | `false` |
| `differing_pixels` | **76,785** |
| `matching_pixels` | 15 |
| `match_percentage_10000` | 1 (i.e. 0.01%) |
| `max_channel_diff` | 218 |
| per-channel max ΔR / ΔG / ΔB / ΔA | 218 / 63 / 50 / 0 |
| `perceptual_match_percentage_10000` | 1 (0.01%) |
| `tolerance_profile` | strict |

**99.98% of overlapping pixels differ.** Of the 76,800 pixels compared,
only 15 happen to match — almost certainly collisions where the Web WM
happens to have painted the exact same 24-bit color that Engine2D
painted at the same coordinate.

## Structural analysis — why ~100% divergence was guaranteed

The two images are not comparable scenes. From the two source reports:

**Source B** (`test/baselines/wm_compare/four_windows/report.sdn` +
`phase3_report.md`): `B_live.ppm` is a 320×240 P6 capture of the Phase 1
live Web WM (`bin/simple run examples/ui/web_wm.spl`) driven through
Electron headless. It paints the `four_windows` scene rendered by the
post-Phase-3 Stitch/glass theme pipeline — a dark-mode desktop with four
translucent window panels, a title bar row, blur, text labels, and
1,689 distinct palette colors from the `glass_obsidian_dark` token set.
Rasterizer: Chromium (via Electron).

**Source D** (`test/baselines/wm_compare/engine2d_in_qemu/report.sdn`):
`D.ppm` is a 1024×768 P6 capture from QMP screendump of the baremetal
`gui_entry_engine2d_min.spl` boot. It paints a verification scene of 3
solid-color window rects drawn via `rt_gui_fill4` MMIO (NOT through
`Engine2D.draw_rect_filled`, which Phase 4 had to bypass due to the
seed compiler's method-dispatch recursion bug). It has exactly 5 unique
colors: `0xFF0A2540` clear, `0xFF1E1E2E` body, `0xFFE74C3C` /
`0xFF27AE60` / `0xFF2980B9` title bars. No text, no blur, no glass, no
alpha compositing.

So the two captures differ along **every** pixel-determining axis:

1. **Scene definition** — glass-themed four-panel desktop vs. three
   hardcoded solid rects.
2. **Resolution** — 320×240 vs. 1024×768.
3. **Color palette** — 1,689 colors vs. 5 colors.
4. **Rasterizer** — Chromium (B) vs. kernel C helper writing MMIO bytes (D).
5. **Text** — present in B (widget labels), absent in D.
6. **Gradients / blur / alpha** — present in B, absent in D.
7. **Coordinate frame** — overlapping top-left 320×240 crop of D catches
   roughly the clear background (`0xFF0A2540`) and the top-left corner of
   the red title bar. B's 320×240 shows the full Web WM desktop.

A byte-level compare under these conditions is a null test by
construction. The `compare_exact` helper is doing its job correctly — it
is faithfully reporting that the two images are different, which they
are, in every way.

## What bit-equivalence actually requires

For Phase 5 to produce a meaningful signal, **both sources must render
the same named scene via comparable pipelines** at the same resolution.
Concrete prerequisites, none of which are currently met:

1. **Same scene graph on both sides.** The most practical path is a
   hardware-agnostic SDN scene spec (e.g.
   `test/fixtures/wm_scenes/four_windows_minimal.sdn`) that both the
   host Web WM and the in-guest WM interpret identically. No Chromium
   on one side and solid rects on the other.
2. **Same rasterizer, or a documented tolerance profile.** Chromium's
   skia-based font and anti-aliasing stack will never be byte-identical
   to a kernel-space software rasterizer. Either (a) route the host side
   through the same software rasterizer that the kernel uses (e.g.
   `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`), or
   (b) accept a `text_tolerant` / `aa_aware` profile and restrict
   byte-equivalence to non-text regions only.
3. **Same resolution.** Both sides capture at 320×240 QVGA. D currently
   captures at the default BGA mode 1024×768 — `gui_entry_engine2d_min.spl`
   would need to either set BGA to 320×240 or the Phase 5 harness would
   need to crop+rescale. Rescaling defeats bit-equivalence, so BGA must
   be reconfigured.
4. **Same color space.** Chromium emits sRGB with gamma; baremetal
   framebuffer writes are raw linear bytes. Either both sides commit to
   raw linear (disable Chromium's color management) or both commit to a
   documented sRGB transform.
5. **Engine2D actually driving both sides.** Today the host `B_live`
   doesn't use Engine2D at all (it's Chromium), and the guest `D` bypasses
   Engine2D's method dispatch via `rt_gui_fill4`. Until Engine2D is the
   canonical renderer on both sides, "bit-level WM equivalence" isn't a
   claim about WM behavior — it's a claim about two different WMs that
   happen to share a name.
6. **(Phase 6) In-guest WM at all.** The cleanest way to make Phase 5
   meaningful is to run the Web WM *inside* QEMU — i.e. wire the deferred
   Source C from the original plan. Prerequisites for Source C were
   documented in Phase 6 of the plan: wire
   `src/lib/gc_async_mut/gpu/browser_engine/` into the QEMU OS boot
   path, add a DOM server thread and Engine2D bridge in the kernel.
   With Source C in place, both B and C would render identically by
   construction (same web engine, same scene graph) modulo any
   Chromium-vs-Simple-browser divergence that Phase 2 would already have
   bounded.

A simpler alternative to the full Source C path: define a "WM reference
scene" in SDN that is small enough (no text, no blur, no alpha) to be
rasterized bit-identically by a shared software rasterizer on both sides.
Then Phase 5 verifies only that shared rasterizer. This is cheaper than
Source C but also weaker — it does not test the actual Web WM rendering
path.

## Honest verdict

Phase 5 as defined in the plan ("same WM scene rendered by B and D must
be byte-identical") cannot be answered with the current inputs. What
Phase 5 CAN answer today, and does:

- **The compare harness works.** It reads two PPMs, detects resolution
  mismatch, crops to the overlapping region, runs exact / per-channel /
  perceptual compares, writes a diff heat-map, writes an SDN report.
- **The ~100% divergence is an honest report of the inputs**, not a
  harness bug.
- **The pre-existing `Pair` bug in `ppm_decode.spl`** is flagged (not
  fixed) — should be a follow-up item.
- **The `array += [x]` O(N²) interpreter cost** means decoding a full
  1024×768 image through the interpreter is impractical; real Phase 5
  runs against matched-resolution baselines (or a compiled harness) will
  not hit this.

**Verdict: BLOCKED on Phase 6 (or on a shared-rasterizer reference
scene).** Phase 5 is not "failing" in the sense of a regression; it is
untestable until one of the prerequisites above is in place.

## Concrete follow-ups (ordered by cost)

1. **Fix `ppm_decode.spl`** — replace the undefined `Pair` with a proper
   struct or tuple. Cheap, unblocks any caller that needs full-image
   decoding.
2. **Make `gui_entry_engine2d_min.spl` capture at 320×240** — change the
   BGA init to QVGA and re-record `D.ppm` so at least the resolution
   matches B.
3. **Define a minimal SDN reference scene** (3 solid rects, no text,
   matched coordinates) and render it on both sides via
   `backend_software.spl` — the only Engine2D backend that exists on
   both host and guest. This gives Phase 5 a *real* positive test.
4. **Fix Engine2D method-dispatch codegen** in the seed compiler so D
   can stop bypassing `draw_rect_filled` via `rt_gui_fill4`. Phase 4
   already documented this as out of scope, but Phase 5 re-raises it:
   without it, D is never rendering through the same API surface as B.
5. **Phase 6 / Source C** — in-guest browser engine + DOM server +
   Engine2D bridge. This is the path to meaningful bit-equivalence of
   the *actual Web WM*, not a subset of it.

## Artifacts index

- `src/app/wm_compare/main.spl` (harness extension)
- `test/baselines/wm_compare/phase5/B_vs_D_diff.ppm`
- `test/baselines/wm_compare/phase5/report.sdn`
- `doc/08_tracking/wm_compare/phase5_report.md` (this file)

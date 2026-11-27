# Engine2D translucent rect blend reads the whole frame back (2026-11-24)

**Status:** FIXED (branch `work/webrender-formsmedia-jit4x-20261124`)
**Area:** `src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl` (`emu_draw_rect_blend`)

## Symptom

forms-media at device scale 4 (3600x3040), JIT, page runner
`examples/06_io/ui/web_render_page_ppm.spl ... 900 760`:

| cap | wall | peak RSS | paint |
|---|---|---|---|
| `MemoryMax=8G` | 24-25 s | 8.27 GB (at the cap) | 7-10 s |
| `MemoryMax=16-20G` | 4.6-4.9 s | 12.7 GB | 1.1-1.2 s |

Other pages at 4x use 2.7-3.5 GB. The interpreter uses 2.9 GB on the same page.

## Root cause

`emu_draw_rect_blend` is the `draw_rect_blend` path Engine2D takes on the
software, cpu and cpu_simd lanes. To blend one rect it called
`core.read_pixels()`, which snapshots the WHOLE frame (10.9M px).

The `<summary>` disclosure triangle (`_engine2d_draw_ir_path_fill`, landed
2026-11-18) blends every anti-aliased edge pixel as a 1x1 rect. So one 44x44
`path` command copied the frame about 100 times.

A per-command RSS probe in `_engine2d_draw_ir_render_command_plan` showed
**+9071 MB across that single command**. The JIT does not reclaim the
snapshots before the page ends. The interpreter shares the array, so its cost
is time (15 ms per blend at 3000x3000), not memory.

With an 8 GB cap, the extra ~4.5 GB made the cgroup reclaim. Most of the 24 s
was that reclaim plus exit teardown. The `wrote` line lands at ~11-15 s and
the process exits at 25-76 s.

## Fix

The blend reads back only its own rect: `core.read_pixels_region_raw(x, y, w, h)`.

- SoftwareBackend overrides it natively. CpuBackend delegates to it.
- Every other backend uses the trait default (full read, then crop), which costs the same as before.
- Out-of-frame region pixels read as 0 and are still skipped by the bounds check, so results are unchanged.

## Evidence

- Spec `test/01_unit/lib/gc_async_mut/gpu/engine2d/rect_blend_reads_region_spec.spl`
  with fixture `test/fixtures/engine2d_blend_region/small_blend_loop.spl`:
  200 small blends on a 3000x3000 frame, one rect clipped by the right edge.
  - JIT: 6.07 s / 8.36 GB -> 0.2 ms.
  - Interpreter: 3.0 s -> 81 ms.
  - Checksums are equal across JIT, interpreter, base and fix.
- forms-media 4x JIT, `MemoryMax=8G`: 25 s / 8.27 GB -> 3.87 s / 3.43 GB, paint 463 ms.
- 8 pages at 1x and 4x, JIT and interpreter: every PPM is byte-identical to
  base, and JIT == interpreter.
- Engine2D blend specs (`backend_metal_device_free_contract`,
  `engine2d_facade_backend_mutation`, `rendering_parity_canonical`): the same
  pass/fail sets as base.
- 3-round alternating A/B (medians, `MemoryMax=8G`, same seed, base tree `d81cf89e4cd`):

  | run | wall (s) | peak RSS (MB) | paint (ms) | document (ms) |
  |---|---|---|---|---|
  | JIT forms-media 4x | 24.30 -> 3.87 | 8096 -> 3338 | 7550 -> 477 | 70 -> 68 |
  | interpreter forms-media 4x | 22.18 -> 20.40 | 2864 -> 2864 | 10711 -> 8815 | 6860 -> 6881 |
  | JIT forms-media 1x | 3.21 -> 3.28 | 2114 -> 2137 | | |
  | JIT html 4x | 4.08 -> 4.11 | 3450 -> 3455 | 467 -> 473 | 134 -> 137 |
  | JIT tab-bar 4x | 3.33 -> 3.37 | 2605 -> 2518 | 133 -> 126 | 13 -> 12 |

  All A/B PPMs are byte-identical. Lane gates pass: specs, combo matrix 81, and the Chrome catalog at baseline.

## Why #11183 reported 2.2 GB / 3.4-3.9 s

That lane's wiki gives forms-media 4x JIT as 3.4-3.9 s and 2.2 GB, with paint ~0.1 s.

- The seed was the same: `cargo-target-wr-jitweb-base`, sha256 d9dcc6f7, built from c8a6a542373.
- Re-measured on that seed with that lane's own branch tree (`b2dcad0d585`) and the same runner, size, backend and mode, I get paint 1.08 s and peak RSS 12.7 GB.
- Varying the backend (`cpu_simd`, `cpu`, `software`, unset), the `/usr/bin/time` vs `systemd-run` wrapping order, and default vs explicit size changes nothing.
- The catalog gate cannot be the source either: `check-chrome-catalog-pixel-diff.shs` runs the interpreter.

So the 2.2 GB figure does not reproduce. Their wall time does match an
uncapped run (4.6 s here under load ~10). The 24 s seen in this lane is the 8 GB
`MemoryMax` cap meeting the 12.7 GB peak.

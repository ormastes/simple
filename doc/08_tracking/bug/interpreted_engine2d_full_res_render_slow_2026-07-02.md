# Interpreted Engine2D full-resolution render is ~9s/frame, pushing 640x480 capture specs near the 120s test cap

Date: 2026-07-02
Status: open
Severity: P3 (test-throughput / DX; correctness unaffected)
Found by: fable, W1d GUI-enhancement lane (G1.2/G1.5/G1.6)

## Summary

Rendering a single 640x480 frame through `Engine2D.create_with_backend(w, h,
"cpu")` + `engine2d_draw_ir_adv_composition` under the interpreter takes
~9 seconds. Measured with the seed binary
(`src/compiler_rust/target/release/simple run`): a 0-render baseline is 0.5s,
6 renders is 56.4s → ~9.3s per full-frame render. The 307k-element PPM-encode
and pixel-diff loops, by contrast, are cheap (~1.2s each).

Consequence: the new capture-backed spec
`test/03_system/gui/ui_draw_ir_pipeline_spec.spl` needs ~8 full-res renders
and lands at ~101s wall — under the 120s default test-client cap
(`test_runner_single.spl` `timeout_secs = 120`) but with little margin. A
cold run or a slower host can exceed it; the spec was trimmed to 8 renders and
was also verified with `--timeout 600`.

## Evidence

- Bench (seed): 0 renders = 0.515s; 6 renders = 56.388s (~9.3s/render).
- `ui_draw_ir_pipeline_spec.spl` full run: Duration ~101–117s for 8 renders.
- PPM evidence (byte-verified pixels match): `build/gui_draw_ir/frame_*.ppm`.

## Suspected cause

The `cpu`/`software` Engine2D backend does its clear + per-rect fills +
`read_pixels` copy in pure Simple (`backend_cpu.spl` / `backend_software.spl`),
so a 307k-pixel clear plus fills runs as ~10^6 interpreted element ops per
frame. This is interpreter throughput, not a rendering bug.

## Impact / workarounds

- Capture specs that render at real window sizes must budget renders (≤ ~10 at
  640x480) or pass `--timeout <secs>`.
- Options: (a) a native fast-path for `clear`/`read_pixels` on the cpu/software
  backend, (b) let the test client read a per-spec timeout marker so
  render-heavy GUI specs opt into a longer cap without a global bump.

## Related

- `doc/08_tracking/bug/test_runner_masks_child_and_expectation_failures_2026-07-02.md`
  — because system-lane expectation failures are masked, this lane's pixel
  assertions were additionally verified out-of-band by byte-inspecting the
  evidence PPMs and by a non-masked unit spec
  (`test/01_unit/lib/skia/animation_timeline_spec.spl`).

## Re-measured baseline (2026-11-13, before any fix)

Base `9100f50e680` (`origin/release/1.0.0`). Host: shared DGX Spark, aarch64,
20 cores, load 11-13 during the series. Every run capped with
`systemd-run --user --scope -p MemoryMax=16G timeout 900`, serial.

Binary: `simple-seed-v4` (session scratchpad copy of the Rust seed),
53,548,096 bytes,
sha256 `af717f53d6bce3e511bfe81c5978b227976afd310d8a552bc8a7e88befb9ba4d`.

Bench: `test/05_perf/gui/bench_ui_draw_ir_pipeline_render.spl` — the same
widget tree, 640x480, `"cpu"` backend and `engine2d_draw_ir_adv_composition`
entry the capture spec uses, plus one isolated `read_pixels_with_source()` per
render. `E2D_RENDERS=<n>` selects the render count; three runs each.

| renders | wall (s) | user (s) | peak RSS (kB) |
|---------|----------|----------|---------------|
| 0 | 1.88 / 2.44 / 1.98 | 0.88 / 0.89 / 0.90 | 567,828 / 558,320 / 558,732 |
| 6 | 17.05 / 16.27 / 16.51 | 16.18 / 16.14 / 16.37 | 661,456 / 670,540 / 650,308 |

Phase timers, 6 renders (ms; three runs):

| phase | run 1 | run 2 | run 3 |
|-------|-------|-------|-------|
| engine create, 6x | 1094 | 1092 | 1086 |
| clear, 6x | 129 | 126 | 150 |
| widget tree -> Draw IR, 6x | 376 | 372 | 385 |
| compose, render 0 (cold glyphs) | 4646 | 4616 | 4626 |
| compose, mean of renders 1-5 | 1098 | 1090 | 1117 |
| isolated readback, per render | 425 | 427 | 427 |

Frame identity (all three runs): `frame_fnv=6981179665638654671`,
`readback_checksum=298222436`, PPM sha256 `460973e28029e86b8cf6...`.

The capture spec itself, `test/03_system/gui/ui_draw_ir_pipeline_spec.spl`:
25.10 s wall, 20.61 s user, 669,096 kB peak RSS (one run).

**The headline of this bug no longer reproduces at its original size.** A
render now costs ~1.3 s steady state plus a one-time ~3.5 s of cold glyph work,
not ~9.3 s, and the capture spec runs in 25 s against the 120 s cap, not ~101 s.
The span-kernel work recorded in
`engine2d_interpreter_span_kernel_marshalling_perf_gap_2026-08-14.md` removed
the clear/fill cost this report suspected. What is left is listed below.

### Where the time goes now

`SIMPLE_INTERP_SAMPLE=1` (CPU-time sampler, 10 ms tick) over the 6-render bench,
1514 samples; self-time share:

| function | share | what it is |
|----------|-------|------------|
| `engine2d_readback_with_identity` | 34.5 % | per-pixel provenance checksum, 2 readbacks per bench render |
| `parse_cmap_format12` + `read_u32_be` | 14.9 % | whole cmap subtable re-parsed on every glyph lookup |
| `_glyf_edge_coverage` | 13.6 % | glyph outline coverage, cold glyphs only |
| `init_with_initial_color` | 7.1 % | per-pixel surface fill at engine create |
| `_emu_scale_image_pixels` | 5.9 % | per-pixel nearest-neighbour image scale |
| `sw_fill_raw_span` + dirty marking | 6.7 % | rect fills, already span-based |

The run is on the tree-walk interpreter because the JIT refuses the module:
`backend_vulkan.spl` calls `env_get` with no import, three definitions are
co-compiled, and the whole module is demoted (`[jit-fallback]`).

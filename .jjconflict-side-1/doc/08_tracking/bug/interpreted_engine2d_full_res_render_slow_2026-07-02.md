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

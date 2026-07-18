# Showcase apps verification — 2026-07-18

Fresh evidence sweep of the 3 showcase apps × 3 surfaces on current main,
deployed `bin/simple` (v1.0.0-beta self-hosted, aarch64-apple-darwin-macho).
All claims below are backed by captured logs (session scratchpad
`showcase_standalone/` + `showcase_hostwm/`), serial logs, or the SimpleOS
evidence bundle. Nothing fabricated; TIMEOUT/FAIL reported as such.

## 9-cell matrix

| App | Standalone | Host-WM | SimpleOS WM |
|---|---|---|---|
| 2D graphics (`graphics_2d_showcase`) | GREEN @320x240 (76789/76800 nonzero px, semantic gate 4/4, 217s interpret; 720p blocked by JIT SIGSEGV + interp perf) | pending re-run (bridge-first + scale + param-detach client fixes landed ea98c69c) | C8-gated (see below) |
| Web standards (`web_standards_showcase`) | TIMEOUT >280s all sizes (layout interpreter-bound; unblocking dep = JIT fix) | pending re-run (bridge-first + scale client fix landed 2e392adf) | C8-gated |
| GUI widget (`gui_widget_showcase`) | GREEN @320x240 (P6 PPM 230415B, 31 distinct bytes, 70s after param-detach sweep; 720p >900s, needs JIT) | **GREEN** @480x270 (4K design / scale 8): bridge `create_window` 488x302 posted 09:47, frame_seq=1, P6 PPM 388815B **37 distinct bytes** 09:52 — after (a) bridge-first client reorder + direct scaled render (c2ad0a81), (b) adapters ported off dead `rt_winit_*` externs onto the GuiRenderer dlopen facade (48b10efe) | C8-gated |

**SimpleOS WM surface status:** the WM itself passes its full fullscreen
evidence harness end-to-end via the stage3 pure-Simple toolchain
(2026-07-18: TTF NVMe load → sfnt validation → pure-sfnt-glyf taskbar clock →
pinned region oracle `ffbd5f76…` cross-verified guest==host → F11
maximize/restore correlation → 19.8MB pixel deltas;
`build/simpleos_wm_fullscreen_evidence/evidence.env` status=pass, two
consecutive runs). Showcase apps INSIDE that WM are hard-gated on the open C8
BlockDevice-dispatch codegen bug (guest FAT32 mount disabled) plus four
further gaps (no app staging, freestanding compile unproven, text-only
guest→WM protocol, no SimpleOS adapter) — full assessment in
`doc/08_tracking/bug/showcase_lanes_regressions_2026-07-18.md`.

## Real defects found and FIXED this sweep (all pushed)
1. Host-WM adapters loaded the ENTIRE compiler via the `app.io.mod` re-export
   hub → interpreter module-limit (800) hard-fail before main() (998293f5).
2. `std.io_runtime` declared unregistered externs (`rt_cli_arg_count`) —
   failing every importer at module load (#159 pattern → `sys_get_args`,
   a157afe8).
3. `Engine2D.create_offscreen` named nonexistent ctor fields (07-16
   regression) — crashed every hosted caller (a157afe8).
4. AOT ambiguous-method blockers in `Engine2D.draw_image_scaled`/`_blend`
   (e4f74739, dec098c1, a14efddc) — **all three showcases now AOT-compile to
   SMF** (14.4/14.0/17.3 MB artifacts).
5. Web host-WM adapter had a 96x96 placeholder canvas (998293f5).
6. WM-client "never posts bridge" root-caused: clients rendered the FULL 4K
   design frame (interpreted, >300s) BEFORE writing the bridge file, so the
   host's bridge wait always expired. All three clients now post the bridge
   first with known scaled dims and render directly at
   `design/SHOWCASE_PPM_SCALE` (c2ad0a81, ea98c69c, 2e392adf). The 2D client
   additionally had the param-detach defect (plain `Engine2D` params in
   `wm_draw_showcase`/`wm_label` → all-zero readback) — return-threaded.
7. Host-WM adapters imported `std.io.window_winit` whose bare `rt_winit_*`
   extern DECLs the deployed binary does not register — module load died with
   "unknown extern function". Ported all three adapters to the sanctioned
   `GuiRenderer` dlopen facade (poll_event drain + present_rgba) (48b10efe).

## Open blockers (filed in the bug doc)
- **Interpreter throughput regression ~3-4x since 07-14** — the single gate
  for every interpreter-lane cell above (bisection needed).
- **`compile --native` on macOS**: linker mis-selection (lld with ld64
  flags) and undefined `rt_alloc`/const-method-mangled symbols — blocks
  running the compiled showcases as native binaries (the intended escape
  from the interpreter wall; SMF artifacts compile but have no direct
  executor).
- **C8** freestanding BlockDevice dispatch (SimpleOS app cells).

## How to reproduce
- Standalone: `SIMPLE_GUI=0 SHOWCASE_RESOLUTION=1280x720 SHOWCASE_PPM=<p>
  SIMPLE_TIMEOUT_SECONDS=280 bin/simple run examples/06_io/ui/<app>_gui.spl`
- Host-WM: `SIMPLE_GUI=1 SIMPLE_EXECUTION_MODE=interpret
  SIMPLE_TIMEOUT_SECONDS=280 bin/simple run examples/06_io/ui/wm_<app>_gui.spl`
- SimpleOS WM: `SIMPLE_BIN=build/bootstrap/stage3/aarch64-apple-darwin/simple
  sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs`

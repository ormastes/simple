# GUI Lib macOS + SimpleOS QEMU ARM64 Perf Initial Evidence - 2026-06-01

## Host

- OS: Darwin 25.5.0 arm64
- CPU: Apple M4
- QEMU: `/opt/homebrew/bin/qemu-system-aarch64`, version 10.2.2
- Metal toolchain: `xcrun` present; `metal` resolved under Apple Metal toolchain v17.3.7003.10.
- Context-mode: doctor reports SQLite/FTS failure due native `better-sqlite3` Node ABI mismatch; research used bounded shell summaries after the MCP search tool failed.

## Research Artifacts Created

- `.spipe/gui-lib-mac-qemu-arm64-perf/state.md`
- `doc/01_research/ui/graphics/gui/gui_lib_mac_qemu_arm64_perf.md`
- `doc/01_research/ui/graphics/gui/gui_lib_mac_qemu_arm64_perf.md`
- `doc/02_requirements/feature/gui_lib_mac_qemu_arm64_perf_options.md`
- `doc/02_requirements/nfr/gui_lib_mac_qemu_arm64_perf_options.md`
- `doc/03_plan/agent_tasks/gui_lib_mac_qemu_arm64_perf.md`
- `doc/03_plan/sys_test/gui_lib_mac_qemu_arm64_perf.md`

## Code Bugs Found And Fixed

- Restored missing Engine2D `gc_async_mut` modules that existing `gc_sync_mut` facades and GUI/capture code still referenced:
  - `src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/backend_adv.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/backend_core.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/backend_intel.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/backend_intel_kernels.spl`
- Added IO compatibility facades for older backend imports:
  - `src/lib/gc_async_mut/io/oneapi_ffi.spl`
  - `src/lib/gc_async_mut/io/compress_ffi.spl`
  - `src/lib/nogc_async_mut/io/compress_ffi.spl`

## Verification Run

- `sh scripts/setup/install-spipe-dev-command.shs --check`: PASS.
- `sh scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs`: ready; QEMU aarch64 present; `virt` machine present; `ramfb` device present; dry-run parse true.
- `bash -n bin/simple && bash -n scripts/gui/macos-gui-run.shs`: PASS.
- `SIMPLE_TIMEOUT_SECONDS=30 scripts/gui/macos-gui-run.shs examples/09_embedded/simple_os/hosted/gui_test.spl`: rejected as release evidence. It only proves macOS `.app` registration and event delivery for a smoke surface; it is not a real shared WM, does not render Simple Web MDI content, and must not be used as the manual-inspection path.
- `bin/simple test test/05_perf/graphics_2d/metal_smoke_spec.spl --mode=interpreter`: PASS, 12 tests.
- `bin/simple test test/02_integration/rendering/perf_smoke_spec.spl --mode=interpreter`: PASS, 16 tests.
- `sh scripts/check/check-metal-generated-2d-readback.shs`: unavailable, reason `missing-metal-submit-readback-harness`; report `doc/09_report/metal_generated_2d_readback_2026-06-01.md`.
- `sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs`: PASS, reason `raw-metal-framebuffer-download-proven`; report `doc/09_report/metal_engine2d_framebuffer_readback_2026-06-01.md`.
- `RUN_QEMU_LIVE_CAPTURE=0 sh scripts/check/check-wm-launch-capture-evidence.shs`: PASS for contract/spec after module fixes; QEMU live capture skipped by request; electron live unavailable due missing `xvfb-run`; report `build/wm-launch-capture-evidence/report.md`.
- `bin/simple run test/05_perf/graphics_2d/perf_2d_runner.spl`: PASS after switching the timer wrapper to the exported `rt_time_now_unix_micros` symbol. Latest host numbers: fill avg 29,069 us; rect avg 247,733 us; mixed avg 3,885 us. The pure rect path remains the main optimization target.
- `test/05_perf/graphics_2d/simple_runner.spl` pure Simple framebuffer optimization:
  - Changed the runner framebuffer from four `u8` stores per pixel to one packed `i64` pixel store, with final hash expansion preserving C byte-order parity.
  - Changed hot framebuffer dimensions and draw-loop indices to `i32` to remove repeated array-index casts, and changed solid sprite blits to use the shared rect-fill path instead of column-major per-pixel writes.
  - Added `--full` / `full` CLI mode so full workload selection is explicit for `bin/simple run` and native artifacts, not only environment-variable driven.
  - C reference rebuilt as native arm64 temp binary because the checked-in `bench_2d` is not executable on this Mac.
  - Latest C p50: fill 4,453,000 ns; blit 6,628,000 ns; scroll 376,000 ns.
  - Before packed framebuffer: Simple p50 fill 187,177,000 ns; blit 84,885,000 ns; scroll 34,931,000 ns.
  - After packed framebuffer: Simple p50 fill 69,275,000 ns; blit 36,401,000 ns; scroll 13,076,000 ns.
  - After packed + `i32` hot-loop + solid-blit optimization: representative Simple p50 fill 62,887,000 ns; blit 22,861,000 ns; scroll 10,667,000 ns. Latest local run: fill 68,420,000 ns; blit 25,504,000 ns; scroll 10,718,000 ns.
  - Hash parity: fill `3453644792`, blit `1245774277`, scroll `35205929` match C.
  - Remaining ratio gap on the latest run: fill about 15.4x, blit about 3.8x, scroll about 28.5x versus C, so the 1.25x NFR remains unmet.
  - Native-build follow-up:
    - Cranelift native-build is hash-correct but slower than `bin/simple run`.
    - LLVM native-build now runs a nonzero workload but reports wrong hashes.
    - `test/05_perf/graphics_2d/fnv1a_native_repro.spl` shows the small packed-pixel FNV arithmetic matches under LLVM. `simple_runner.spl --debug-pixels` shows p0/pmid/plast can match while row/window hashes and a 9x9 sample grid expose native-render mismatches. Returning framebuffers from draw helpers and disabling rect unroll did not fix LLVM hashes.
    - `test/05_perf/graphics_2d/blit_tile_native_repro.spl` now isolates the issue to inline array writes in a tiled row loop: interpreter writes four distinct tiles; LLVM native at `--opt-level none` receives correct colors but leaves later samples blue.
    - `test/05_perf/graphics_2d/blit_tile_u64_native_repro.spl` shows the same issue is not limited to `[i64]`; a `[u64]` variant also corrupts later LLVM samples.
    - Tracked as `doc/08_tracking/bug/simple_runner_native_perf_hash_gap_2026-06-01.md`.
- `bin/simple test test/05_perf/graphics_2d/report_spec.spl --mode=interpreter`: PASS, 18 tests. Warning: scenario artifact manifest path is too long for one generated scenario directory name.
- `bin/simple test test/05_perf/graphics_2d/c_vs_simple_2d_spec.spl --mode=interpreter`: PASS, 16 tests.
- `bin/simple run test/05_perf/graphics_2d/bench_2d_metal_simple.spl`: Metal command reaches the Metal backend and prints full-mode timing rows after switching to `rt_time_now_unix_micros` and replacing `mod` with `%`.
  - Current limitation: JIT falls back to interpreter on mutable sample sorting (`W1006`), command exits nonzero, and rows still report `pixel_hash=0`.
  - Latest Metal p50 rows: fill 658,000 ns; blit 69,000 ns; scroll 578,000 ns.
  - This is timing-only evidence, not accepted readback evidence.
- `bin/simple test test/05_perf/graphics_2d/metal_readback_proof_spec.spl --mode=interpreter`: PASS, 1 test in 3,541 ms.
  - Adds a deterministic Metal compute proof that fills a 16x16 GPU buffer, downloads it through the raw-pointer `rt_metal_buffer_download` path, and verifies every downloaded word.
  - This closes the low-level Metal buffer readback proof for macOS.
- `bin/simple spipe-docgen test/05_perf/graphics_2d/metal_readback_proof_spec.spl -o doc/06_spec/perf/graphics_2d`: generated `doc/06_spec/perf/graphics_2d/metal_readback_proof_spec.md`.
- `bin/simple test test/02_integration/rendering/metal_engine2d_readback_spec.spl --mode=interpreter`: PASS, 2 tests in 3,464 ms.
  - `MetalBackend.read_pixels()` now downloads the real Metal framebuffer after GPU-covered `clear` and `draw_rect_filled` operations.
  - CPU-only operations such as text invalidate GPU completeness and keep the deterministic software mirror fallback.
- `bin/simple spipe-docgen test/02_integration/rendering/metal_engine2d_readback_spec.spl -o doc/06_spec/integration/rendering`: generated `doc/06_spec/integration/rendering/metal_engine2d_readback_spec.md`.
- `SIMPLE_BINARY=src/compiler_rust/target/debug/simple bin/simple test test/03_system/gui/arm64_wm_ramfb_screendump_spec.spl --mode=interpreter`: PASS, latest run 1 live QEMU screendump test in 20,819 ms.
- Live QEMU ARM64 capture evidence:
  - ELF: `build/os/simpleos_arm64_wm.elf`
  - Raw capture: `build/os/arm64_wm_ramfb_screendump.ppm` (P6, 1024x768)
  - PNG evidence: `build/os/evidence/arm64_wm_ramfb_screendump.png`
  - Blocker file: absent after pass.
  - Rendering assertion: the screendump spec now validates dock icon artwork contrast and detail in the QMP framebuffer capture, not just a valid PPM header.
  - Visual result: the dock renders procedural Terminal, Files, Calculator, Clock, Settings, Browser, and Editor icons through the ARM64 ramfb framebuffer path.
- Hosted compositor real-rendering follow-up:
  - Added a compositor `blit_pixels` contract so Simple Web window artifacts are copied as real pixel buffers instead of decomposed into one `fill_rect` per pixel.
  - The winit hosted backend now calls `rt_winit_buffer_blit_pixels`; SDL2, Cocoa, Win32, Engine2D, browser, baremetal, and headless backends keep Simple fallback loops for compatibility.
  - Shared MDI seed data now drives the hosted entry and tests, keeping the canonical Terminal, Editor, Browser, File Manager, and Calculator surfaces in one pure Simple module.
  - Verification: `src/compiler_rust/target/debug/simple check ...` passed for 17 edited Simple files.
  - Verification: `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/os/compositor/shared_mdi_setup_spec.spl --mode=interpreter --no-cache` passed, 1 test in 2,764 ms.
  - Verification: `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/os/compositor/engine2d_glass_spec.spl --mode=interpreter --no-cache` passed, 8 tests in 10,998 ms.
  - Verification: `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/os/compositor/host_compositor_entry_spec.spl --mode=interpreter --no-cache` passed, 29 tests in 36,939 ms.
  - Rust SFFI validation note: `cargo test -j1 -p simple-compiler blit_pixels_extern_copies_and_clips_pixels --lib` was attempted twice after adding direct unit coverage. Both attempts were terminated during dependency compilation without a Rust diagnostic, so this host did not produce Rust unit-test evidence for the new SFFI path.
- Shared MDI and backend-evidence follow-up:
  - Restored the hosted WM target path to `HostCompositor` plus `simple_web_window_renderer.spl`; the lightweight Simple GUI renderer is now labeled smoke-only and is not accepted release evidence for this plan.
  - Replaced block-placeholder text in the shared framebuffer evidence backend with real 8x16 glyph rendering for WM chrome/title text.
  - Added backend-evidence records so GUI/QEMU reports must name the requested backend, selected backend, fallback reason, frame timing, and readback status.
  - Added QEMU shared-MDI contract markers for ARM64 and x86_64 framebuffer lanes.
  - Verification: `backend_evidence_spec.spl` passed, 10 tests in 3,812 ms.
  - Verification: `shared_mdi_framebuffer_scene_spec.spl` passed, 2 tests in 18,045 ms.
  - Verification: `arm64_wm_shared_mdi_contract_spec.spl` passed, 1 test in 3,852 ms.
  - Capture blocker: `scripts/check/check-hosted-wm-capture-evidence.shs` now exits bounded and records `hosted-wm-capture-timeout`; latest report is `doc/09_report/hosted_wm_capture_evidence_2026-06-01.md`. The hosted capture artifact is still not accepted evidence until the timeout is fixed.

## Open Evidence Gaps

- Low-level Metal raw-pointer buffer readback and Engine2D Metal framebuffer readback now have passing macOS proofs.
- Metal Simple benchmark has timing rows but no per-scene GPU readback hash and a JIT mutability fallback, so it cannot close the benchmark hash gate.
- Pure-Simple full-frame rendering improved materially for blit and scroll, but still misses the C parity NFR by a wide margin.
- `examples/09_embedded/simple_os/hosted/hosted_main.spl` still fails to reach `First frame presented` within 30s on the direct host path. The square-only `gui_test.spl` smoke is excluded from release evidence; the required path is the shared hosted WM entry in `src/os/hosted/hosted_entry.spl`.
- Hosted first-frame capture is bounded but currently unavailable due `hosted-wm-capture-timeout`; the script records this as a blocker instead of hanging.
- User still needs to select feature and NFR options before final requirements are written.

# CPU-SIMD Text Glyph Inline Perf Evidence

**Date:** 2026-07-09
**Scope:** Simple Web CPU-SIMD retained 4K/8K render loop

## Change

`SoftwareBackend.draw_text` now reads glyph rows directly from the shared packed
5x7 atlas (`glyph_index_for_char_code` + `glyph_row_bits`) instead of creating a
per-character row array through `glyph_data`.

This does not change viewport size, DPI, checksum policy, GPU backend selection,
or glyph source data.

## Evidence

Command shape:

```bash
SIMPLE_LIB=src bin/simple run src/app/wm_compare/backend_measurement_software_export.spl --mode=native -- \
  --software-render-backend cpu_simd \
  --width 7680 --height 4320 \
  --warmup-count 1 --sample-count 1 \
  --dpi 300 \
  --fixture gui-perf-8k-cpu-simd \
  --shell simple-web \
  --command bench-8k \
  --host local
```

Observed after the change:

- 4K CPU-SIMD p50: `243530us`, checksum `sum32:32105444634193792`,
  pixel proof `nonzero_pixels:8294400`.
- 8K CPU-SIMD p50: `938678us`, checksum `sum32:135445232233405312`,
  pixel proof `nonzero_pixels:33177600`.
- DPI metadata: `gui_perf_benchmark_dpi=300`,
  `gui_perf_benchmark_density_profile=retina`.
- Screen-size metadata: `gui_perf_benchmark_screen_size_reduced=false`.

The retained 8K checksum matches the prior external-compare report, so this is a
performance-only change for that workload.

## Remaining Gap

The prior external Node Canvas/Cairo row remains `80.201ms` p50 at the same 8K
size. The CPU-SIMD row improved from `1282.166ms` to `938.678ms`, but remains
about `11.7x` slower than that external CPU drawing-library baseline.

## Rejected Follow-ups

Two smaller follow-ups were tried and reverted because they preserved the
checksum but did not improve the retained 8K row:

- Coalescing adjacent glyph-bit spans in `SoftwareBackend.draw_text`: 8K
  `938812us`, checksum `sum32:135445232233405312`.
- Returning selector-backed HTML to full layout before heuristic color scans:
  8K `947898us`, checksum `sum32:135445232233405312`.

The next useful target is the full Simple Web layout/paint stage split, not
another backend-only text-loop micro-change.

## Layout/Paint Stage Split

An opt-in trace flag was added to
`src/app/wm_compare/backend_measurement_software_export.spl` so the same
generated benchmark HTML can run through
`simple_web_layout_render_html_software_pixels_traced` without changing the
normal render-loop measurement.

4K trace:

- `parse_html_ms=1`, `extract_css_ms=0`, `compute_styles_ms=1`,
  `layout_ms=0`, `paint_ms=201`.
- Total: `204480us`.
- Checksum: `sum32:32105444634193792`.

8K trace:

- `parse_html_ms=1`, `extract_css_ms=0`, `compute_styles_ms=1`,
  `layout_ms=0`, `paint_ms=776`.
- Total: `779724us`.
- Checksum: `sum32:135445232233405312`.
- Box trace after adding trace-only layout diagnostics showed:
  `html x=0 y=0 w=7680 h=282 bg=0`,
  `body x=8 y=8 w=7664 h=266 bg=270544896`, and
  `main x=8 y=8 w=7664 h=266 bg=0`.

The retained 8K bottleneck is therefore paint/fill bandwidth over the full
framebuffer, not parse, CSS, style, or layout.

Native SIMD framebuffer initialization was tested and reverted:

- `simd_fill_row` over a zero-initialized framebuffer logged
  `unknown extern function: rt_engine2d_simd_fill_u32`, changed the checksum,
  and slowed 4K trace to `878028us`.
- `engine2d_simd_fill_row_u32` over the full framebuffer segfaulted at 4K.

The next optimization should stay inside the Engine2D-owned SIMD fill path or
register a safe browser-layout framebuffer fill facade before using native SIMD
from `simple_web_html_layout_renderer.spl`.

Follow-up trace instrumentation now splits the opt-in paint line into
`framebuffer_init_ms`, `trace_setup_ms`, `paint_draw_ms`, and aggregate
`paint_ms`. This does not change normal rendering; it only makes the next
retained 4K/8K trace distinguish full-frame framebuffer initialization,
trace-only setup, and subsequent draw work.

Follow-up split traces:

- 4K: `framebuffer_init_ms=188`, `trace_setup_ms=0`, `paint_draw_ms=15`,
  `paint_ms=204`, total `208234us`, checksum `sum32:32105444634193792`,
  `nonzero_pixels:8294400`.
- 8K: `framebuffer_init_ms=1503`, `trace_setup_ms=0`, `paint_draw_ms=32`,
  `paint_ms=1535`, total `1539281us`, checksum
  `sum32:135445232233405312`, `nonzero_pixels:33177600`.

Both split traces kept `dpi=300`, `density_profile=retina`, full physical
size, and `screen_size_reduced=false`. The split-trace run is retained as
bottleneck evidence, not as a speed improvement: it shows the dominant cost is
full-frame framebuffer initialization/fill before draw work, which reinforces
that the remaining optimization belongs at the browser-layout framebuffer owner
boundary.

Native array-repeat fill was then aligned with the existing Simple core
runtime implementation so `[base; width * height]` sets the array length once
and fills the backing words directly instead of calling `rt_array_push` once
per pixel. The Rust runtime mirror uses the same no-push fill shape. Sequential
trace evidence after the C native runtime change:

- 4K: `framebuffer_init_ms=183`, `trace_setup_ms=0`, `paint_draw_ms=15`,
  `paint_ms=199`, total `202984us`, checksum `sum32:32105444634193792`,
  `nonzero_pixels:8294400`.
- 8K: `framebuffer_init_ms=732`, `trace_setup_ms=0`, `paint_draw_ms=32`,
  `paint_ms=765`, total `768514us`, checksum
  `sum32:135445232233405312`, `nonzero_pixels:33177600`.

This keeps 300 DPI retina metadata, full physical size, and
`screen_size_reduced=false`. It is a native array-repeat optimization, not a
browser-only fill facade; the unsafe mutable Engine2D fill extern remains
blocked.

Two post-repeat follow-ups were tried and rejected because they preserved
checksum/no-reduction metadata but did not beat the clean 8K repeat-fill trace:

- Allocating the repeat array without zero-initializing its backing storage:
  4K `paint_ms=199`, total `203022us`; 8K `paint_ms=770`, total `773902us`,
  checksum `sum32:135445232233405312`.
- Filling the native repeat array by doubling initialized spans with `memcpy`:
  8K `paint_ms=768`, total `771496us`, checksum
  `sum32:135445232233405312`.
- Reusing the existing Engine2D C SIMD fill helper from native
  `rt_array_repeat`: 4K `paint_ms=200`, total `203982us`; 8K `paint_ms=766`,
  total `770542us`, checksum `sum32:135445232233405312`.

Tracked blocker:
`doc/08_tracking/bug/browser_layout_large_simd_fill_facade_unsafe_2026-07-09.md`.

Follow-up returned-array facade experiment:

- Replacing browser layout `[base; width * height]` with
  `rt_u32_alloc_filled(len, fill)` was rejected. Direct native export segfaulted
  before writing SDN evidence, so the path cannot be used as hardening evidence.
- Browser layout remains on compiler-lowered `[base; width * height]`, relying
  on the optimized native `rt_array_repeat` backing-word fill. This keeps the
  no-direct-Engine2D-extern safety boundary while preserving native execution.

Focused evidence:

- `SIMPLE_LIB=src bin/simple test test/03_system/check/cpu_simd_render_scale_contract_spec.spl --mode=interpreter --clean`
  passed with the source contract guarding against `rt_u32_alloc_filled` and
  direct `rt_engine2d_simd_fill_u32`.

Full 8K external CPU drawing-library baseline refresh:

- Report: `doc/09_report/gui_perf_benchmark_2026-07-09_cpu_base.md`.
- Command: `BUILD_DIR=build/gui_perf_bench_2026-07-09_cpu_base REPORT_PATH=doc/09_report/gui_perf_benchmark_2026-07-09_cpu_base.md SIMPLE_WEB_CPU_MODE=native tools/gui_perf_bench/run_all_benchmarks.shs --width 7680 --height 4320 --frames 1 --dpi 300`.
- Available CPU baselines on host `dl`: GTK3/Cairo completed, Node canvas
  completed, Python tkinter unavailable.
- External compare result: `gui_perf_cpu_base_compare_status=measured`,
  `baseline_backend=javascript_node_canvas`,
  `gui_perf_cpu_base_compare_dpi_source=default`,
  `gui_perf_cpu_base_compare_schedule_order=cpu_simd_first`, Simple CPU-SIMD
  p50 `767.872ms`, Node canvas p50 `73.892ms`,
  `gui_perf_cpu_base_compare_target_met=no`.
- Simple internal scalar row also completed at p50 `799.203ms`, so this full
  external compare run keeps CPU-SIMD slightly ahead of scalar while both remain
  far behind Node canvas. It kept full `7680x4320`, 300 DPI retina metadata,
  checksum `sum32:135445232233405312`, `nonzero_pixels:33177600`, and
  `screen_size_reduced=false`; the compare block duplicates those proof fields
  as `gui_perf_cpu_base_compare_physical_pixels`,
  `gui_perf_cpu_base_compare_screen_size_reduced`,
  `gui_perf_cpu_base_compare_simple_checksum`, and
  `gui_perf_cpu_base_compare_simple_pixel_proof`, and now also records
  `gui_perf_cpu_base_compare_runtime_compute_target=cpu_simd`,
  `gui_perf_cpu_base_compare_render_readback_scope=software-render-loop`, and
  `gui_perf_cpu_base_compare_fallback_used=false`.

Focused CPU-SIMD routing containment:

- The browser presenter now routes `cpu_simd` solid-only frames through the
  existing Engine2D display-list readback path. This exercises the current
  `CpuBackend`/`SoftwareBackend` `simd_fill_row` owner path for opaque solid
  rectangles and avoids unsafe browser-framebuffer externs.
- The solid-only detector now rejects translucent backgrounds by requiring
  `st.bg` alpha 255. This keeps `rgba(...)` and CSS opacity on the normal CPU
  mirror path so color/transparency composition stays byte-exact.
- The public Engine2D renderer now skips heuristic/probe routing for obvious
  text pages requested as `cpu_simd`; those pages go directly to the real layout
  software pixels, avoiding a CPU-SIMD routing tax when no solid-fill SIMD
  shortcut can apply.
- Focused native evidence:
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl --mode=native --clean`
  passed with `6 examples, 0 failures`; the solid case asserts SIMD fill hits,
  public text renders assert no fill-probe hits, and translucent/opacity cases
  preserve expected pixels.
- Full native 4K/8K scale contract after routing containment:
  `SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple CPU_SIMD_RENDER_SCALE_SAMPLE_COUNT=1 OUT_DIR=build/check/cpu-simd-render-scale-engine-skip sh scripts/check/check-cpu-simd-render-scale-contract.shs`
  passed. 4K CPU-SIMD p50 `201516us` vs scalar `205874us`; 8K CPU-SIMD p50
  `1435462us` vs scalar `1589252us`; checksum parity held at both sizes,
  300 DPI remained the default, physical pixels stayed `7680x4320` at 8K, and
  `gui_perf_cpu_base_compare_target_met=yes`.
- Retained-checksum full native rerun:
  `OUT_DIR=build/check/cpu-simd-render-scale-retained-checksum` passed the
  canonical 4K checksum `sum32:32105444634193792` and 8K checksum
  `sum32:135445232233405312`, but timing was variable: 8K CPU-SIMD p50
  `1435662us` vs scalar `1049096us`, so
  `gui_perf_cpu_base_compare_target_met=no` on that run.
- Exporter direct text-layout shortcut:
  `src/app/wm_compare/backend_measurement_software_export.spl` now bypasses
  the generic renderer wrapper for obvious text pages requested as `cpu_simd`.
  Full native evidence in `build/check/cpu-simd-render-scale-exporter-direct`
  kept the canonical 4K/8K checksums and improved the CPU-SIMD 8K p50 to
  `1128035us`, but scalar was still `977624us`, so
  `gui_perf_cpu_base_compare_target_met=no` on that run.
- Renderer text paint-loop width-scan skip:
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  now avoids computing per-line advance width during paint when default
  left/start alignment and no underline make that value unused. Full native
  evidence in `build/check/cpu-simd-render-scale-skip-line-width` kept the
  canonical 4K checksum `sum32:32105444634193792` and 8K checksum
  `sum32:135445232233405312`; 4K CPU-SIMD p50 was `203104us` vs scalar
  `204715us`, and 8K CPU-SIMD p50 was `960459us` vs scalar `1020635us`, so
  `gui_perf_cpu_base_compare_target_met=yes` for this focused retained row.
- Scheduling hardening: the scale wrapper now emits
  `cpu_simd_render_scale_contract_run_order` and
  `gui_perf_cpu_base_compare_schedule_order`, with
  `CPU_SIMD_RENDER_SCALE_RUN_ORDER=software_first` available for reverse-order
  follow-up rows.
- The external Node canvas baseline remains much faster in
  `doc/09_report/gui_perf_benchmark_2026-07-09_cpu_base.md`; this containment
  improves routing, scalar comparison, scheduling metadata, and color proof,
  but the external drawing-library gap remains open.

Rejected follow-up:

- Initializing the framebuffer directly to an inferred full-page background and
  skipping a matching root/body repaint was rejected. The scale contract still
  passed scalar/SIMD parity, but the retained full-size fixture checksum changed
  from `sum32:135445232233405312` to `sum32:17761116667698048`, proving a color
  regression. The scale contract now retains the canonical 4K/8K checksums by
  default so this class of quality drift fails closed.

## Verification

- `SIMPLE_LIB=src bin/simple test test/03_system/check/cpu_simd_render_scale_contract_spec.spl --mode=interpreter --clean`
  passed after the binary-link contract: `7 examples, 0
  failures`.
- Strict tiny production-binary link gate passed:
  `CPU_SIMD_RENDER_SCALE_REQUIRE_ENGINE2D_BINARY=1 CPU_SIMD_RENDER_SCALE_4K_WIDTH=16 CPU_SIMD_RENDER_SCALE_4K_HEIGHT=16 CPU_SIMD_RENDER_SCALE_8K_WIDTH=32 CPU_SIMD_RENDER_SCALE_8K_HEIGHT=32 CPU_SIMD_RENDER_SCALE_SAMPLE_COUNT=1 OUT_DIR=build/check/cpu-simd-render-scale-binary-link-strict sh scripts/check/check-cpu-simd-render-scale-contract.shs`
  emitted `cpu_simd_render_scale_engine2d_binary_link_status=pass`,
  `cpu_simd_render_scale_engine2d_binary_link_required=1`, and
  `cpu_simd_render_scale_contract_status=pass` for
  `/home/ormastes/dev/pub/simple/bin/simple`.
- Array-repeat owner optimization:
  `rt_array_repeat` now writes the first non-byte element once and fills the
  rest by doubling `memcpy` chunks in both `src/runtime/runtime_native.c` and
  `src/runtime/simple_core/core_array_ops.spl`, preserving `[base; width *
  height]` semantics while reducing interpreted/self-hosted fill loop work.
- Array-repeat allocation hardening:
  public `rt_array_new` keeps zeroed-array semantics, while `rt_array_repeat`
  now uses repeat-private uninitialized element storage in the C runtime and
  Simple core runtime, then fully overwrites it with the repeated value. This
  removes the redundant zero-fill before large framebuffer repeats without
  changing normal array allocation behavior.
- Deployed-binary freshness gate:
  `check-cpu-simd-render-scale-contract.shs` now emits
  `cpu_simd_render_scale_runtime_source_fresh_status`. On this workspace,
  `CPU_SIMD_RENDER_SCALE_REQUIRE_RUNTIME_FRESH=1` correctly fails with
  `runtime_sources_newer_than_simple_bin` because `bin/simple` predates the
  latest runtime array-repeat changes. The source change is covered, but
  deployed-binary performance proof requires a fresh bootstrap/deploy.
- Clean bootstrap/deploy follow-up:
  removed the stale Rust seed interpreter registration for rejected
  `rt_u32_alloc_filled`; `cargo check -p simple-compiler` passed after that
  fix. A clean `/tmp/simple-simd-clean` `bootstrap-from-scratch.sh
  --full-bootstrap --deploy` then advanced past Rust seed/native runtime build,
  but Stage 2/3 hit the known
  `bootstrap_stage2_empty_mir_bodies_2026-07-05` fallback and Stage 4 native
  full-CLI compile remained CPU-bound for more than 18 minutes without producing
  `build/bootstrap/full/x86_64-unknown-linux-gnu/simple`, so the run was
  interrupted. Strict deployed-binary freshness evidence remains blocked on a
  completed deploy, not on the SIMD runtime source change.
- Focused fresh-binary follow-up:
  the smaller exporter-only native build path avoids compiling the full CLI, but
  initially hit parser errors on decimal `0u32` sentinels in
  `src/lib/common/ui/wm_chrome_theme.spl`; those sentinels now use plain `0` and
  `SIMPLE_LIB=src bin/simple check src/lib/common/ui/wm_chrome_theme.spl`
  passes. Retrying the focused exporter build still fails later with
  `semantic: undefined field 'id': cannot access field on value of type 'nil'`,
  while `SIMPLE_LIB=src bin/simple check
  src/app/wm_compare/backend_measurement_software_export.spl` passes. The
  remaining blocker is therefore native-build/codegen-specific, not the exporter
  source contract.
- Focused fresh-binary continuation:
  `SIMPLE_DEBUG_FIELD_ACCESS=1` localized the first native-build crash to
  `bitfield_type_sym_for(base_local.id)` and the second to
  `collection_opt_core.inst_in_list(d1_local.id)`. Both now fail closed when the
  bootstrap interpreter binds an `if val` local to nil, so the focused exporter
  build reaches backend codegen instead of crashing in MIR lowering/optimization.
  Cranelift then fails verifier checks in `_render_software_pixels`; trying the
  same focused build with `llvm-lib` exits 139 after unresolved-call diagnostics.
  `SIMPLE_LIB=src bin/simple check
  src/app/wm_compare/backend_measurement_software_export.spl` still passes, so
  strict fresh-binary proof remains blocked by native backend codegen, not by
  the CPU-SIMD scale contract.
- Focused fresh-binary exporter simplification:
  `backend_measurement_software_export.spl` now avoids the generic
  `RenderBackend.render_html_to_pixels` branch in the proof exporter, keeps the
  CPU-SIMD fixture on the direct Simple Web layout path, flattens small boolean
  helpers, and simplifies the one-sample percentile path used by the scale
  contract. The focused Cranelift build now avoids importing the full
  `backend_measurement_report.spl` module; the exporter writes its own
  single-sample SDN row. `SIMPLE_LIB=src bin/simple check
  src/app/wm_compare/backend_measurement_software_export.spl` passes, and a
  focused `one-binary` native probe
  (`backend_measurement_software_export_native_probe.spl`) builds and exits
  `0` after running the CPU-SIMD trace render and checking the native SDN
  length witness. The scale contract now has an opt-in native probe gate:
  `CPU_SIMD_RENDER_SCALE_PROBE_ONLY=1 CPU_SIMD_RENDER_SCALE_REQUIRE_NATIVE_PROBE=1
  CPU_SIMD_RENDER_SCALE_NATIVE_PROBE_BIN=build/check/cpu-simd-render-scale-export-bin-current/backend_measurement_software_export_native_probe
  sh scripts/check/check-cpu-simd-render-scale-contract.shs` passes with
  `cpu_simd_render_scale_native_probe_status=pass`. The scale and external
  benchmark wrappers now generate tiny typed-value entrypoints for each Simple
  Web render row because direct argv and native text-array handoff remain
  incomplete for this exporter.
- Scale-to-arch evidence link:
  `CPU_SIMD_RENDER_SCALE_ARCH_MATRIX_ONLY=1
  CPU_SIMD_RENDER_SCALE_REQUIRE_ARCH_MATRIX=1
  CPU_SIMD_RENDER_SCALE_ARCH_MATRIX_ENV=build/cpu-simd-engine2d-arch-matrix-aarch-mutable-target/evidence.env
  sh scripts/check/check-cpu-simd-render-scale-contract.shs` now requires and
  reports the canonical arch-matrix pass, including target-binary pass fields
  for x86_64, AArch64, and RISC-V.
- Full strict 4K/8K rerun after array-repeat doubling:
  `CPU_SIMD_RENDER_SCALE_REQUIRE_ENGINE2D_BINARY=1 CPU_SIMD_RENDER_SCALE_SAMPLE_COUNT=1 OUT_DIR=build/check/cpu-simd-render-scale-array-repeat-doubling-full sh scripts/check/check-cpu-simd-render-scale-contract.shs`
  passed with 4K CPU-SIMD p50 `205462us` vs scalar `207347us`, 8K CPU-SIMD p50
  `764831us` vs scalar `798711us`, canonical 8K checksum
  `sum32:135445232233405312`, full `7680x4320`, strict binary-link status
  `pass`, and `gui_perf_cpu_base_compare_target_met=yes`.
- `cargo test -p simple-runtime test_array_repeat` passed: `1 passed`.

- `SIMPLE_LIB=src bin/simple test test/03_system/gui/wm_compare/backend_measurement_capture_spec.spl --mode=interpreter --clean`
  passed after the trace split: `25 examples, 0 failures`.
- Normal retained 8K CPU-SIMD row after adding the opt-in trace flag:
  `943683us`, checksum `sum32:135445232233405312`, full `7680x4320`,
  `gui_perf_benchmark_screen_size_reduced=false`.
- Full 8K external CPU drawing-library profile contract passed:
  `profile_report_contract=true`, `profile_kind=gui`, report path
  `doc/09_report/gui_perf_benchmark_2026-07-09_cpu_base.md`.
- `sh scripts/check/check-cpu-simd-render-dpi-contract.shs` passed with
  `cpu_simd_render_dpi_default=300`,
  `cpu_simd_render_dpi_override=220`,
  `cpu_simd_render_dpi_physical_pixels=32x32`, and checksum
  `sum32:2944430194688`, proving the retina default stays configurable without
  reducing physical pixels.
- `BUILD_DIR=build/production_gui_web_backend_executed_evidence_cpu_simd_alpha REPORT_PATH=doc/09_report/production_gui_web_backend_executed_evidence_2026-07-09_cpu_simd_alpha.md sh scripts/check/check-production-gui-web-backend-executed-evidence.shs`
  passed with `production_gui_backend_cpu_simd_different_pixels=0`,
  `production_gui_backend_cpu_simd_alpha_quality_status=pass`,
  `production_gui_backend_cpu_simd_alpha_quality_hits=4`, matching software and
  CPU-SIMD alpha-quality checksums `8901726553200`, matching alpha pixels
  `4280964222`, and `production_gui_backend_blur_or_tolerance_used=false`.
- Engine2D SIMD arch matrix passed for target C kernel binaries on x86_64,
  AArch64, and RISC-V; runtime owner compile also passed for RISC-V RVV:
  `doc/09_report/cpu_simd_engine2d_arch_matrix_2026-07-09.md`.
- `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged`
  passed.
- `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.

## 2026-07-10 evidence correction

The 4K/8K timings above were produced by a stale self-hosted `bin/simple`
dated 2026-07-03. Its `rt_array_repeat` disassembly contains a counted loop
that calls `rt_array_push` for every element. A focused 33,177,600-element
probe measured `762414us`, which accounts for the retained 8K framebuffer
initialization time.

Therefore, the retained timings prove the behavior and quality contracts of
that deployed binary, but they do not measure the current bulk-fill source in
`runtime_native.c` and `simple_core/core_array_ops.spl`. Treat the `10.4x`
Cairo comparison as a stale-deployment result pending a fresh self-hosted
build. An isolated rebuild reached the known Stage 2 LLVM failure and then
spent 18 bounded minutes in seed-driven Stage 4 without producing an
executable; it was stopped rather than allowed to run unbounded.

### 2026-07-10 focused fresh-runtime measurement

The Stage 2 LLVM blockers were repaired sufficiently to compile a standalone
current-runtime probe. At a full 8K element count (`33,177,600`), the native
`rt_array_repeat` path completed in `0.21 s` wall time with `260096 KiB` max
RSS, preserved the requested array length and final color, and exited zero.
Disassembly proves the binary uses the current doubling-`memcpy` path. The stale
deployed push-loop probe took `0.762 s`, so the current runtime is approximately
3.6x faster for the isolated owner-fill operation.

A direct-store replacement measured `0.20 s`, within one-run noise, and was
reverted because it generated more complex code without a material gain.
Stage 2 and Stage 3 binaries now build, but the Stage 4 full CLI accepted 822
unresolved stubs and fails `-c 'print(1+1)'` with a nil field access. Therefore
the focused result is accepted as runtime evidence only; retained full 4K/8K
and external Cairo evidence remains pending a smoke-clean Stage 4 binary.

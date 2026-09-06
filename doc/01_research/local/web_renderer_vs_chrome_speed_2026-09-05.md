# Simple web renderer vs Chrome: what is actually measured (2026-09-05)

Scope: the `test/05_perf/web_render_chrome/` lane. Every claim below cites `file:line`.
**Bottom line: no honest Simple-vs-Chrome speed number exists or can be produced today.**
The Chrome side is now genuinely measured; the Simple side is still synthesized in-process.

## 1. What is measured today

### Chrome side — REAL (this supersedes the prior research note)

`test/05_perf/web_render_chrome/chrome_runner.spl` launches a real browser process:

- `chrome_runner.spl:30-41` — `chrome_binary()` probes 5 real paths incl.
  `/Applications/Google Chrome.app/Contents/MacOS/Google Chrome`.
- `chrome_runner.spl:81-87` — `process_run_bounded(bin, ["--headless=new", ...,
  "--window-size=3840,2160", "--force-device-scale-factor=1",
  "--run-all-compositor-stages-before-draw", "--virtual-time-budget=1000",
  "--screenshot=" + absolute_path(png_path), "file://" + absolute_path(html_path)], ...)`.
- `chrome_runner.spl:80,88` — real wall clock either side:
  `time_now_unix_micros()` … `(time_now_unix_micros() - start_us).to_f64() / 1000.0`.
- `chrome_runner.spl:94-99` — fail-closed admission: `if bytes <= 0 or digest.len() != 64 or
  not png_has_4k_ihdr(png_path)` returns PENDING; `rec.source = "measured"` /
  `rec.status = "MEASURED"` are reachable only past that gate.
- `chrome_runner.spl:62-68` — `png_has_4k_ihdr` decodes the real PNG IHDR and requires
  `width == VIEWPORT_WIDTH and height == VIEWPORT_HEIGHT` (3840x2160, `:5-6`).

Provenance: committed at `5faf2103589` (2026-09-05), no working-tree diff. The prior claim
at `doc/01_research/local/web_renderer_vulkan_4k_showcase_hardening.md:8` — "existing
Chrome runners explicitly use synthetic timing/hash data. No source-bound 3840×2160
first-frame/RSS/tab comparison receipt exists" — is **stale in its first half**:
`chrome_runner.spl` is real and does produce source-bound 3840x2160 per-tab captures. It
stays correct for `perf_chrome_runner.spl` and `simple_runner.spl` below, and its RSS and
*comparison-receipt* clauses stay fully correct — no comparison receipt exists, because the
Simple half does not measure. (That research file is untracked, status `A`, so nothing
committed ever contradicted it.)

### Simple side — SYNTHETIC

`test/05_perf/web_render_chrome/simple_runner.spl` does not run the renderer:

- `simple_runner.spl:135-177` — `synthetic_parse_ms` / `synthetic_style_ms` /
  `synthetic_layout_ms` / `synthetic_paint_ms` / `synthetic_composite_ms` /
  `synthetic_present_ms` / `synthetic_pixel_hash`.
- `simple_runner.spl:197` — `# replace the synthetic stage below with actual pipeline calls:`
- `simple_runner.spl:204-212` — those synthetic values are assigned straight into the record.
- `simple_runner.spl:232-233` — `rec.source = "synthetic"` /
  `rec.error_msg = "renderer pipeline not linked — synthetic timings"`.
- `simple_runner.spl:226-230` — even p50/p95 come from a generated `frame_times` array
  (`frame_times.push(base * (1.0 + jitter))`), not from sampling.
- Its only `use` is `simple_runner.spl:30`
  (`use perf.graphics_2d.bench_harness.{…}`). It imports **nothing** from
  `std.gc_async_mut.gpu.browser_engine`, so the "renderer library not linked" comments at
  `:17` and `:130` are literally accurate — there is no code path to the real renderer.

The only way `simple_runner` reports `measured` is by reading a pre-existing artifact
someone else wrote (`simple_runner.spl:270-272, 337-341`) — it never produces one itself.

### The second, fully synthetic Chrome runner

`test/05_perf/web_render_chrome/perf_chrome_runner.spl` is the file the prior research
described, and it is unchanged:

- `perf_chrome_runner.spl:72-79` — `# Simulate per-phase timing proportional to iteration
  count`, `m.parse_us = base * 2` … `m.present_us = base * 1`.
- `perf_chrome_runner.spl:82-85` — `m.fps = 60`, `m.memory_kb = 32768` hardcoded.
- `perf_chrome_runner.spl:88-107` — `runner_set_chrome_baseline(...)` *accepts* Chrome
  numbers as arguments and derives phases by division (`m.parse_us = gpu_us / 10`, …).
- `perf_chrome_runner.spl:137` — the "Chrome baseline" is the literal
  `runner_set_chrome_baseline("basic_page", 60, 0, 500, 65536)`.
- `perf_chrome_runner.spl:109-115,141` — it then prints `simple_vs_chrome_ratio: N%`.
  **That printed ratio is two synthetic constants divided by each other.** It is the single
  most dangerous artifact in this lane; nothing about it is measured, and unlike
  `report_spec.spl` below it carries no source guard.

### The comparison specs — ratio present, but guarded by construction

`report_spec.spl` does compute `row.simple_vs_chrome_ratio = row.simple_frame_ms /
row.chrome_frame_ms` (`report_spec.spl:217`), which is the shape of a real comparison. It
is currently safe for one reason only: it never reads the real artifacts.
`report_spec.spl:7` says "Uses inline synthetic baseline data (no file I/O dependency)",
`:218` hardcodes `row.source = "synthetic"`, and `classify_status` (`:182-184`) forces
`PENDING` whenever `source == "synthetic"`, which `:262-267`
(`all_synthetic_are_pending`) then asserts. So the ratio exists but can never be reported
as measured.

**This is the standing hazard.** `trace_normalizer.spl:148` reads
`base_dir + "/artifacts/chrome_" + fixture + ".json"` — i.e. exactly the real Chrome
artifacts produced below. The moment anything wires the real Chrome JSON into
`report_spec.spl`'s row-building without also gating on the *Simple* side's
`source == "measured"`, the lane will emit a real-Chrome-over-synthetic-Simple ratio that
looks measured. The guard that exists is `source` being a hardcoded constant, not a check.

### The 4K contract spec is a source scan, not a run

`chrome_real_4k_fail_closed_contract_spec.spl:10-11,17,29` is `file_read(RUNNER)` plus
`expect(source).to_contain(...)`. Per repo rule, a source scan is never proof of execution
or of a timing. It pins the runner's *text*, which is useful, and proves nothing about a run.

The runner itself self-labels its own limits, honestly: `chrome_runner.spl:54,58-59` emit
`"frame_ms_p50":0.0,"frame_ms_p95":0.0,"warm_sample_count":0`,
`"gpu_backend_status":"unverified"`, `"comparison_admitted":false`.

## 2. What is runnable here, and what I actually ran

Runnable: the Chrome half only. I executed it.

- Host: macOS 26.5, Apple M4.
- Chrome: `Google Chrome 152.0.7977.76` (`/Applications/Google Chrome.app/Contents/MacOS/Google Chrome`).
- Interpreter: `src/compiler_rust/target/bootstrap/simple`, sha256 prefix `8fb83548961be7d2`,
  22,744,272 bytes, mtime 2026-09-05 12:35. Invocation:
  `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple run test/05_perf/web_render_chrome/chrome_runner.spl` (exit 0).

All 11 captures passed the `:94` fail-closed gate — `"source":"measured"`, real 3840x2160
PNGs on disk (`file` reports `PNG image data, 3840 x 2160, 8-bit/color RGB`), each with a
64-hex sha256 (e.g. `static_page` → `31da1e20…fce5aa`, 123,463 bytes).

| capture | wall clock (ms) |
|---|---|
| static_page | 2341.869 |
| scroll_heavy | 1886.665 |
| layout_stress | 1827.540 |
| paint_heavy | 3668.477 |
| showcase tab overview | 1807.579 |
| showcase tab html | 1826.469 |
| showcase tab css-layout | 1908.689 |
| showcase tab css-paint | 1764.130 |
| showcase tab forms-media | 1860.849 |
| showcase tab animation | 1664.598 |
| showcase tab evidence | 1505.982 |

**These are not first-frame times, despite the field name `first_frame_ms`
(`chrome_runner.spl:99`).** The interval spans `:80`→`:88` and covers the entire child
process: spawn, cold browser start, profile setup, navigation, render, 4K PNG encode, and
exit. Call it process-lifetime wall clock. I have not decomposed it, so I make no claim
about which component dominates. Artifacts land in
`test/05_perf/web_render_chrome/artifacts/`, which is gitignored (`.gitignore:210 artifacts/`).

**No comparison was produced, because the Simple half has nothing to measure.** Even if
`simple_runner.spl` were wired up, the two sides would not be commensurable: Chrome's
number includes process spawn and PNG encode, and the Simple path here runs under the seed
interpreter rather than a native build.

## 3. Frame-cost instrumentation in the Simple renderer

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl` has exactly
three timed regions:

| region | lines | what it covers | where it surfaces |
|---|---|---|---|
| paint | `:361`, `:366` | `_simple_web_layout_execute_draw_ir_composition` only | `print "[web-phase] phase=paint elapsed_ms=…"`, gated on `SIMPLE_WEB_PHASE_TRACE=1` (`:350`) — stdout text, never a typed record |
| upload route | `:438`, `:445-447` | software render + `present_layout_pixels_with_engine2d_readback` | `_WebDrawIrTimedRoute.elapsed_us` → `state.upload_samples` → `upload_bound_p50_us/p95_us` |
| gpu route | `:458`, `:477-479` | `_simple_web_layout_render_draw_ir_composition` on the GPU backend | `_WebDrawIrTimedRoute.elapsed_us` → `state.gpu_samples` → `gpu_paint_p50_us/p95_us` |

Dataflow confirmed at `simple_web_layout_engine2d_fast.spl:585-593`:
`web_gpu_paint_timing_evidence(backend_name, _web_draw_ir_p50(state.upload_samples),
_web_draw_ir_p95(state.upload_samples), _web_draw_ir_p50(state.gpu_samples),
_web_draw_ir_p95(state.gpu_samples), state.upload_samples.len(), …)`, with
`state.complete = evidence.sample_count >= 3` (`:595`).

The evidence record is `simple_web_html_engine2d_presenter.spl:84-98` (the class ends at
`:98`; `:100` begins `_WebGpuPaintMeasuredChoice`). Its **only** timing fields are the four
at `:88-91`; every other member is a bool, an `i32` count, or text
(`pixels_match`, `upload_device_proven`, `gpu_device_proven`, `commands_complete`,
`should_offload`, `reason`, `speed_verdict`).

**Not instrumented — the gaps:**

1. **HTML parse** — no timer anywhere in the file.
2. **Style resolution** — no timer.
3. **Layout** — `_simple_web_layout_draw_ir_once` / `…_with_degraded_retry` are called at
   `:351-360`, i.e. *before* `_phase_paint_start_us` is taken at `:361`. Layout is
   structurally excluded from the one phase timer that exists.
4. **Composite / present as distinct phases** — folded inside the upload/gpu route totals;
   not separable.
5. **PNG or framebuffer encode** — untimed, though Chrome's number includes it.
6. **End-to-end first frame** — no single timer spans HTML-in to pixels-out, so there is no
   Simple-side quantity of the same shape as Chrome's `first_frame_ms`.
7. **RSS / memory** — no probe at all. `chrome_runner.spl:58` emits a hardcoded
   `"memory_mb":0.0`; nothing measures either side.
8. **Tab-level cost** — the showcase tab dimension exists only on the Chrome side
   (`chrome_runner.spl:10,116-134`).

Also worth noting: both route timers guard with `if start_us > 0 and end_us > start_us`
(`:446`, `:478`) and fall back to `0`, so a stub clock degrades silently to a zero elapsed
time rather than an error. A zero in these fields must not be read as "fast".

Executing gates for this evidence type do exist —
`test/05_perf/web_render_chrome/web_gpu_paint_device_measured_spec.spl` and
`web_draw_ir_gpu_route_device_measured_spec.spl` — but they gate *device-proven GPU
execution* of the paint routes, not any end-to-end frame cost, and neither has a Chrome
side.

## 4. What would have to exist for an honest speed claim

1. **A real Simple-side measurement.** Replace `simple_runner.spl:204-212` with actual
   pipeline calls (and an import of the renderer it currently lacks, cf. `:30`), so
   `rec.source` reaches `"measured"` through execution rather than through `:270-272`'s
   artifact re-read. Nothing else on this list matters until this does.
2. **Commensurable interval definitions.** Chrome's `chrome_runner.spl:80-88` is
   process-lifetime; a Simple in-process timer is not comparable to it. Either time both
   as whole processes, or instrument both from navigation-start to pixels-complete. Pick
   one and state it in the receipt.
3. **Layout/parse/style timers on the Simple side**, placed to include the work at
   `simple_web_layout_engine2d_fast.spl:351-360` that `:361` currently excludes.
4. **Warm-sample aggregates.** Chrome-side hardcodes `"warm_sample_count":0`
   (`chrome_runner.spl:54`). A single cold process capture cannot support a speed claim;
   N warm frames with p50/p95 are the minimum, on both sides.
5. **A source guard on every ratio.** `report_spec.spl:217`'s ratio is safe today only
   because `:218` hardcodes `source = "synthetic"`. Before real artifacts are wired in via
   `trace_normalizer.spl:148`, that must become an actual check that **both** sides read
   `measured`. Separately, remove or gate `perf_chrome_runner.spl:141`'s ratio print, which
   has no guard at all.
6. **Real GPU-backend identity on both sides.** `chrome_runner.spl:59` says
   `"gpu_backend_status":"unverified"`; headless Chrome may be on SwiftShader. Without
   device identity on each side the comparison is not defined.
7. **Real RSS sampling** for the memory column that `chrome_runner.spl:58` currently stubs.
8. **A native Simple binary**, not the seed interpreter, for any published number.
9. **An executing comparison gate.** `chrome_real_4k_fail_closed_contract_spec.spl` pins
   text only. A companion gate should assert that 11 `artifacts/chrome_*.json` carry
   `"source":"measured"` with matching 3840x2160 PNG sha256s, that the paired
   `artifacts/simple_*.json` do too, and refuse to emit a ratio while either side's
   `comparison_admitted` is `false`.

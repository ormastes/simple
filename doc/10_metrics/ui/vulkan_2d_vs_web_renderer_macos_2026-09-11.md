# Vulkan 2D Showcase vs Web Renderer — macOS Timing (2026-09-11)

Measurement only. No fixes attempted.

## Binary identity (bracketed every run)

```
bin/simple -> src/compiler_rust/target/bootstrap.generations/502da...45d/simple
             size=130402384 mtime=1788606093
src/compiler_rust/target/bootstrap/simple
             size=130402384 mtime=1788606093
```
Identical across all runs below (checked before/after each command; no drift).

`bin/simple` is the bootstrap-only seed (no `run`/`test`); `src/compiler_rust/target/bootstrap/simple`
(same binary content) was used via `run`, per repo rule. **No self-hosted `bin/simple` exists
on this host** — both `check-vulkan-2d-c-compare.shs` and `setup-gui-web-2d-vulkan-env.shs --check`
independently report `simple_bin_selection_reason=repo-bin-rust-seed-forbidden` /
`bootstrap-seed-forbidden`: the trusted Vulkan-2D comparison gate refuses to run on the seed.
The two peer live-evidence reports (`macos_vulkan_2d_live_evidence_2026-09-05.md`,
`macos_vulkan_web_live_evidence_2026-09-05.md`, both uncommitted) also both recorded
`status=fail` (`trusted-build-manifest-invalid`, `strict-evidence-receipt-missing`) — this
environment has never had a passing trusted run for either lane.

## Lane 1: Vulkan 2D showcase (`test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl`, seed binary)

`scripts/check/check-vulkan-2d-c-compare.shs` and `check-engine2d-vulkan-*-8k.shs` all require
a self-hosted `bin/simple` and refuse the seed outright (environment-blocked, not run).
`engine2d_backend_vulkan_entry.spl` fails to even load standalone (`examples.ui.engine2d_backend_scene`
unresolved — the example expects to be launched from inside its own package context).
Ran the underlying bench script directly instead:

| command | size | backend requested | backend reported | wall_s | frame_ms/fps | rss_mb | verdict |
|---|---|---|---|---|---|---|---|
| `vk2d_bench.spl` (VK2D_W=1920 H=1080 RECTS=2000 FRAMES=60) | 1920x1080 | vulkan | **cpu** (`status=blocked reason=backend-unavailable`) | 19.24 | not emitted (blocked, no frame stats) | 782 | environment-blocked |
| `check-engine2d-vulkan-*-8k.shs` | 8K | vulkan | — | — | — | — | environment-blocked (needs self-hosted bin) |
| `engine2d_backend_vulkan_entry.spl` direct | — | vulkan | — | 0.54 | — | 181 | failed (unresolved import, hard error) |

The bench script itself self-reports `blocked`/`backend-unavailable` when run under the seed —
it does not silently substitute a fake pass. No Vulkan frame timing could be collected on this
host in this session.

## Lane 2: Web renderer (`web_render_page_ppm.spl`, seed binary, `sample_web_renderer_sanity.html`)

Default example timeout is 10s (`SIMPLE_TIMEOUT_SECONDS`, `examples_safety.rs`); both backends
timed out at the default before raising it to 300s.

| command | size requested | backend requested | backend reported | wall_s | ms/px | rss_mb | pixel diversity | verdict |
|---|---|---|---|---|---|---|---|---|
| `web_render_page_ppm.spl` (timeout=10s) | 900x760 | cpu | — | 10.07 | — | — | — | could-not-complete-in-time |
| `web_render_page_ppm.spl` (timeout=10s) | 900x760 | vulkan | — | 10.06 | — | — | — | could-not-complete-in-time |
| `web_render_page_ppm.spl` (timeout=300s) | 900x760 | cpu | **interpreter** (JIT fallback: `TextMetrics.cell_advance_px` type-infer failure) | 30.58 | 0.0447 | 1293 | 12+ distinct byte values / 4KB sample (non-blank) | passed |
| `web_render_page_ppm.spl` (timeout=300s) | 900x760 | vulkan | **interpreter** (same JIT fallback) | 30.47 | 0.0447 | 1293 | 12+ distinct byte values / 4KB sample (non-blank) | passed |
| `web_render_page_ppm.spl` (timeout=300s) | 1920x1080 requested | cpu | interpreter | 30.23 | n/a | 1293 | — | passed but **size argument had no effect** — output is 684000 px (=900x760) in all three runs; the program does not honor the W/H CLI args for this HTML fixture |

`684000 px` (900*760) in every output file, including the 1920x1080-requested run, confirms the
renderer clamps to page/fixture-derived dimensions, not the CLI size — so no larger-size datapoint
exists on this host; both `cpu` and `vulkan` env selections produced byte-identical wall times
(30.58s vs 30.47s) because both dropped to the same interpreter path before any backend-specific
code ran.

## Setup check

`sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --check`: MoltenVK ICD and library present and
hash-recorded, `vulkaninfo` reports a real device (`Apple M4`, `MoltenVK`,
`PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU`, `device_selection_status=hardware`) — the GPU/driver stack
itself is healthy. `gui_web_2d_vulkan_simple_bin_status=forbidden` (seed) is the sole blocker for
the trusted Vulkan-2D lane. RenderDoc unavailable (no macOS build/cask).

## Self-hosted binary rerun (coordinator-directed, same session)

Binary: `bin/release/aarch64-apple-darwin-macho/simple`, size=26264696 mtime=1788766698
(md5 `635362bdaed9a3c9d46de648ea75dd2d`, distinct from the seed md5
`b25f1c257701f7e3ceea1dfe8da4f7d0`). `--version` prints only `Simple v1.0.0-rc.1`
(no banner) but `run` on a 3-line hello world DOES print the seed WARNING banner
and still executes correctly (hello/line2/line3, exit 0) — so this binary is a
distinct build but not banner-free at `run` time as described. It is **still
detected as a seed by the gate's `strings` check**
(`grep -Eqi 'bootstrap seed only|compiler_rust/target|rust-built Simple binary'`
hits): `SIMPLE_BIN=<this binary> check-vulkan-2d-c-compare.shs` — the seed-forbidden
branch never even ran because the **C leg** itself reported
`compare_status=skipped compare_reason=c-leg-measured-unadmitted:receipt-needs-common-admission`
first, short-circuiting before the Simple leg's seed check was reached. Bracket
identical before/after every run below (no drift).

| command | size | backend requested | backend reported | wall_s | ms/px | rss_mb | verdict |
|---|---|---|---|---|---|---|---|
| `vk2d_bench.spl` (VK2D_W=1920 H=1080 RECTS=2000 FRAMES=60) | 1920x1080 | vulkan | — (crashed before reporting) | 15.67 | — | 805 | **failed** — Rust panic: `AArch64 direct call is 167795716 bytes away, out of the +/-128 MiB reach of 'bl', and no veneer could be placed within range (JIT code arena exhausted or unavailable)` at `cranelift-jit/src/compiled_blob.rs:107:21`, via `JitCompiler::compile_module` / `ExecCore::run_file_jit`. Matches filed bug `doc/08_tracking/bug/jit_aarch64_branch_relocation_out_of_range_abort_2026-09-05.md`. Exit 122. |
| `check-vulkan-2d-c-compare.shs` with `SIMPLE_BIN=<self-hosted>` | 800x600 (defaults; `--w/--h` flags not read by the script) | vulkan (C leg only) | c leg ran (fps=5216.9, ms=57.5); Simple leg never invoked | — | — | — | environment-blocked — C leg `compare_status=skipped` short-circuits before the Simple leg runs |
| `web_render_page_ppm.spl` (`PAGE_W=1920 PAGE_H=1080`) | 1920x1080 | n/a (script hardcodes `cpu_simd`, ignores `SIMPLE_2D_BACKEND` — see below) | cpu_simd, interpreter fallback | 101.16 | 0.0488 | 1804 | passed |

**Root cause of the ignored CLI size arg (step 3):** `examples/06_io/ui/web_render_page_ppm.spl:39-40`
reads size from environment variables only — `val W = int_env("PAGE_W", 900)` /
`val H = int_env("PAGE_H", 760)` — never from `argv`. The only positional-arg
readers in the file are `arg_with_suffix(".html", …)` and `arg_with_suffix(".ppm", …)`
(lines 18-24, matched by file extension), so a bare `1920 1080` positional pair is
silently discarded — it matches neither suffix. **Correct invocation:**
`PAGE_W=1920 PAGE_H=1080 <bin> run examples/06_io/ui/web_render_page_ppm.spl <page.html> <out.ppm>`.
Separately, line 45 hardcodes the backend string `"cpu_simd"` in the call to
`simple_web_render_html_to_pixels_with_engine2d_backend(html, W, H, "cpu_simd")` —
`SIMPLE_2D_BACKEND` is read nowhere in this file, so the earlier seed-binary
cpu-vs-vulkan "comparison" was always the same code path regardless of the env var,
confirmed again here.

## Interpreter-mode rerun (avoids JIT arena crash, coordinator-directed)

`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0`, same self-hosted
binary (`bin/release/aarch64-apple-darwin-macho/simple`, size=26264696
mtime=1788766698, identical before/after every run). This avoids the JIT path
entirely, so the aarch64 branch-relocation panic from the previous section does
not fire.

| command | size | backend requested | backend reported (in-program) | wall_s | ms(60 frames)/fps~ | rss_mb | verdict |
|---|---|---|---|---|---|---|---|
| `vk2d_bench.spl` | 900x760 (rects arg ignored, defaults to 64) | vulkan | **vulkan — real device**: `device=Apple M4 driver=Apple M4\|vendor=0000106b\|device=1a040209` | 17.24 | ms=1982 fps~=30 (p50=32.96ms p95=33.76ms) | 733 | in-program `status=blocked reason=unconditional-submit-wait` — real Vulkan ran and produced numbers, but the bench's own correctness gate (not the shell `strings` seed detector) refuses to admit the result because `unconditional_submit_wait=true` |
| `vk2d_bench.spl` | 1920x1080 | vulkan | vulkan — real device, same Apple M4 identity | 49.19 | ms=2159 fps~=27 (p50=34.33ms p95=46.68ms) | 1211 | same in-program block (`unconditional-submit-wait`) |

Both runs report a real Vulkan device and driver string, not a fallback stub — the
seed-forbidden shell gate never enters into it since we bypassed the wrapper
script and ran `vk2d_bench.spl` directly. `VK2D_RECTS` is not read by the bench
(rects stays at its hardcoded default of 64 regardless of the env var, matching
the earlier seed-binary run).

### Web renderer, patched copy, vulkan backend requested

Since `vk2d_bench.spl` reported `vulkan`, per instructions: copied (not edited
in place) `examples/06_io/ui/web_render_page_ppm.spl` to
`build/perf/vulkan_2d_vs_web_2026-09-11/patched/web_render_page_ppm_vulkan.spl`
and changed only line 45's literal from `"cpu_simd"` to `"vulkan"`:
`simple_web_render_html_to_pixels_with_engine2d_backend(html, W, H, "vulkan")`.
The tracked file was not touched.

| command | size | backend requested | backend reported | wall_s | ms/px | rss_mb | verdict |
|---|---|---|---|---|---|---|---|
| patched copy, `PAGE_W=900 PAGE_H=760` | 900x760 | vulkan (patched arg) | **not independently confirmed** — line 44's `print` literal still says `"...via pure-Simple web lane (cpu_simd)..."` unconditionally (a hardcoded string, not derived from the passed backend arg), so stdout gives no evidence the vulkan code path actually ran rather than silently falling back | 19.85 | 0.0290 | 960 | passed (faster than the 30.58s cpu_simd run in the prior section — consistent with, but not proof of, a real Vulkan path; the print statement is misleading and should be fixed to interpolate the actual backend argument if anyone relies on it as evidence) |

## Where the time goes

- Vulkan 2D lane never produced a frame-timing measurement: the bench script itself refuses to
  drive real Vulkan under the seed binary and self-reports `blocked`, not a fake pass.
- Web lane's ~30.5s / 684,000px (~0.0447 ms/px) is JIT-fallback-**interpreter** time for BOTH
  `SIMPLE_2D_BACKEND=cpu` and `=vulkan` — the log shows an identical `[jit-fallback]` HIR-lowering
  error (`TextMetrics.cell_advance_px` type inference) before any backend branch executes, so this
  number reflects interpreter overhead on this one fixed-size fixture, not GPU-vs-CPU rendering.
- No apples-to-apples Vulkan-vs-web ms/px ratio can be computed on this host/session: the 2D
  showcase lane has zero frame_ms datapoint (blocked), and the web lane's two "backends" are the
  same interpreter path under the hood. The only honest ratio available is web-cpu vs web-vulkan
  wall time, which is 1.00x (30.58s / 30.47s) — because they are the same code path.

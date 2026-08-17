# `Engine2D.load_font()` runs at ~3 KB/s under the interpreter — 17.8 MB pinned font ⇒ ~25-95 min

- **Date:** 2026-07-25
- **Area:** `src/lib/gc_async_mut/gpu/engine2d/` font loading + `src/lib/common/encoding/font_registry.spl`
- **Severity:** high — makes the showcase-matrix cell **2D × headless** unrunnable
  on the interpreter lane at *any* resolution, including 320x240.
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  See "Fix" below for the change and the verifying measurement.
- **Platform measured:** linux-x86_64, `bin/simple` =
  `bin/release/x86_64-unknown-linux-gnu/simple` (currently a **Rust bootstrap
  seed** build — it prints the seed warning on every run). Originally recorded on
  aarch64-apple-darwin; same root cause, so the defect is platform-independent.

## Summary

`examples/06_io/ui/graphics_2d_showcase.spl` was recorded as
**FAIL (perf boundary)** — "no evidence line after 40+ minutes, killed". That
verdict is **correct but mis-attributed**. It is not a hang, not the rasterizer,
and not the resolution. The entire cost is a single call:

```
val font_candidate = selected_font_asset_candidates()[0]
val font_loaded = engine.load_font(font_candidate.local_path)
```

`selected_font_asset_candidates()[0]` is **Noto Sans SC** —
`assets/fonts/google-fonts/ofl/notosanssc/NotoSansSC[wght].ttf`,
**17,772,300 bytes**, a CJK variable font. The showcase renders only ASCII
labels, but it loads the full 17.8 MB face because the pinned catalog's index 0
happens to be the CJK sans.

Grep marker in `src/lib/common/encoding/font_registry.spl`:

```
fn selected_font_asset_candidates() -> [FontAssetCandidate]:
    """Return the pinned 16-file C1/F1/P1 candidate catalog."""
    [
        _google_font_candidate("Noto Sans SC", "sans", "ofl/notosanssc/NotoSansSC[wght].ttf", ...
```

The declared size in that entry (`17772300`) matches the file on disk exactly.

`load_font()` under the interpreter processes roughly **3.1 KB of font per
second**, so 17.8 MB takes tens of minutes. That is the 40+ minutes in the
original report — the run was still inside `load_font`.

## Measured rate (linear in font bytes, terrible constant)

Probe: load three catalog faces in one process, timestamped
(`probe_f_smallfont.spl`, protected-name invocation so the host kill monitor
does not truncate it).

| candidate | font | bytes | wall time | rate |
|---|---|---|---|---|
| `[13]` | UnifrakturCook-Bold.ttf | 42,688 | **14 s** | 3,049 B/s |
| `[9]` | Bungee-Regular.ttf | 118,996 | **37 s** | 3,216 B/s |
| `[8]` | NotoSansMono[wdth,wght].ttf | 1,708,408 | >346 s (unfinished) | — |
| `[0]` | **NotoSansSC[wght].ttf** (the showcase's) | **17,772,300** | **~25-95 min extrapolated** | — |

The two completed points agree to within 5%, so the cost is **O(font bytes)
with a ~3.1 KB/s constant**, not a super-linear blowup. Nothing is stuck; it is
simply ~1000x too slow to be usable interpreted.

**Caveat on the extrapolation:** the upper end (~95 min) assumes cost is linear
in font *bytes*. A glyph-count model (UnifrakturCook ~250 glyphs / 14 s, Bungee
~400 / 37 s, Noto Sans SC ~65,000) gives ~25 min instead. Both models land in
the same band and both match the "40+ minutes, killed" originally recorded on
aarch64-apple-darwin. This is an extrapolation, not a measurement — see
"Open item" below.

## It is slow, not hung — thread evidence

Per `.claude/rules` / `feedback_diagnose_hang_per_thread_utime`, sampled
`/proc/<pid>/task/*/stat` utime plus RSS during the stall:

```
--- rss_kb=3693012 ---   tid=591969 (simple-main) ut=10595 st=313
--- rss_kb=3693012 ---   tid=591969 (simple-main) ut=13513 st=315
--- rss_kb=3693012 ---   tid=591969 (simple-main) ut=16484 st=317
```

- `simple-main` gains ~2,950 ticks per 30 s ⇒ **~98% of one core, continuously**.
- Every other thread (`tracing-appende`, `ctrl-c`, the second `simple-main`)
  has **zero** utime growth — all parked in `futex_wait_queue`.
- RSS is **exactly flat** at 3,693,012 KB across all samples.

CPU burning + flat RSS = compute-bound, single-threaded. Not a deadlock, not a
blocking syscall, not an allocation balloon.

Confirmed over a long protected run of the real showcase at 320x240:

| wall age | RSS (KB) | busiest-thread utime (ticks) | CPU | last trace stage |
|---|---|---|---|---|
| 109 s | 3,693,012 | 10,595 | ~98% | `font_candidate_resolved` |
| 329 s | 3,693,012 | — | ~98% | `font_candidate_resolved` |
| 974 s | 3,693,012 | 95,534 | **98.1%** | `font_candidate_resolved` |
| 1,224 s | 3,693,012 | 119,877 | **97.9%** | `font_candidate_resolved` |

RSS is identical **to the kilobyte** across 20 minutes while one thread burns
~98% of a core. That is the textbook "slow, not blocked" signature.

## Stage localization

`examples/06_io/ui/graphics_2d_showcase.spl` now carries a level-gated stage
trace (`SIMPLE_SHOWCASE_TRACE=1`, default off). At `SHOWCASE_RESOLUTION=320x240`:

```
t+3s   graphics_2d_trace=entry
t+3s   graphics_2d_trace=engine_created
t+4s   graphics_2d_trace=font_candidate_resolved
       <-- engine.load_font(...) : no further marker; ~98% CPU indefinitely
```

Compile + module load + engine creation = **~4 seconds total**. Everything after
that is `load_font`.

## The rasterizer is NOT the problem

Control probe (`probe_b_render.spl`): same `Engine2D` import closure,
`create_offscreen(320,240)` + `clear` + `draw_rect_filled` + `draw_circle_filled`
+ `read_pixels_with_source()`:

```
probe_b_readback checksum=399805491 pixels=76800
elapsed = 26 s total, of which ~3 s is the draw+readback
```

Software offscreen 2D rendering at 320x240 works correctly and cheaply on this
platform. The recorded 2026-07-14 note "2D 320x240 standalone PASS" is
consistent with that; the regression is the font-loading step, not the renderer.

`showcase_mask()` (76,800-iteration write loop) was also suspected and cleared:
a standalone repro (`probe_c_mask.spl`) completes in **0 s**.

## Proposed fixes as first written (superseded — kept for the record)

**Hypothesis 1 below turned out to be WRONG.** The cost was not TTF walking at
all; it was the SHA-256 digest of the whole blob computed in interpreted Simple.
See "Fix (2026-07-26)" at the end of this document for what actually landed.
Item 2 (catalog ordering) is unaffected by the fix and remains open.

1. **Primary — make `load_font` lazy / table-driven.** ~3 KB/s implies the TTF
   is being walked byte-at-a-time in interpreted Simple at load time. A face
   only needs `head`/`cmap`/`hhea`/`hmtx`/`loca`/`maxp` parsed up front; `glyf`
   outlines should be decoded per-glyph on first raster (there is already a
   glyph cache — `font_cache_stats()` reports `rasterizations`/`hits`, and the
   showcase already asserts a cold-then-warm hit pattern against it). For the
   showcase's ~40 ASCII glyphs this turns 17.8 MB of work into a few KB.
2. **Secondary — do not make index 0 of the pinned catalog the 17.8 MB CJK
   face.** Any consumer that writes `selected_font_asset_candidates()[0]`
   expecting "the canonical trusted sans default" silently gets the largest
   asset in the bundle. Either reorder so `[0]` is a Latin sans, or expose an
   explicit `selected_default_latin_font()` accessor.

**Deliberately not done: switching the showcase to a smaller font.** The
showcase asserts font *identity* — it compares
`loaded_fonts.current_font_identity()` against
`selected_font_asset_identity(font_candidate)` and fails the run if they differ.
Swapping the face to a 42 KB font would make the cell finish in seconds while
proving strictly less than it does today. That is gaming the gate, not fixing
the defect. The real fix is `load_font` performance plus candidate ordering;
until one of those lands, this cell is honestly BLOCKED on the interpreter lane.

## Reproduce

```bash
# Protected name so scripts/resource/kill_simple_monitor.shs (CPU>95% for 60s)
# does not SIGTERM the run and make a slow render look like a hang.
cp bin/simple build/tmp/claude_simple
SIMPLE_SHOWCASE_TRACE=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
SIMPLE_TIMEOUT_SECONDS=0 SHOWCASE_RESOLUTION=320x240 \
  build/tmp/claude_simple run examples/06_io/ui/graphics_2d_showcase.spl
```

## Measurement traps hit during this investigation

Three separate host-level guards each independently masquerade as "the showcase
hangs". Anyone re-measuring this must neutralize all three or they will
mis-diagnose it again:

1. **`bin/simple run` applies a hard 10-second timeout to any path containing
   `examples/`.** See `src/compiler_rust/driver/src/cli/examples_safety.rs`,
   grep markers `DEFAULT_EXAMPLES_TIMEOUT_SECS` (= 10), `is_examples_path`, and
   `fn timeout_error_message`. It re-executes the file as an isolated child
   (`SIMPLE_EXAMPLE_ISOLATED_CHILD`) and reports
   `error: example timed out after 10s: <path>`. Because the child's
   stdout/stderr are piped and only printed *after* it dies, you see a huge log
   and no evidence line. Disable with `SIMPLE_TIMEOUT_SECONDS=0`.
2. **`scripts/resource/kill_simple_monitor.shs` SIGTERMs any non-protected
   `simple` process** — grep markers `CPU_THRESHOLD=95` and `MIN_AGE_SECS=60`.
   Confirmed in `/tmp/kill_simple_monitor.log`:
   `KILL pid=287603 (cpu=96.4% age=60s: ./bin/simple run examples/06_io/ui/graphics_2d_showcase.spl)`.
   Any legitimate interpreted render longer than ~60 s is truncated and looks
   like a hang. The script's `is_protected()` whitelists cmdlines containing
   `claude`, hence the `build/tmp/claude_simple` copy above. A shell redirect
   does **not** appear in the child argv and therefore cannot protect the
   process — the protecting token must be in `argv[0]` or an argument.
3. **`earlyoom -r 3600 --prefer ^(simple|rustc|cc1|...)`** is also running and
   explicitly prefers `simple` as an OOM victim.

## Open item

A protected end-to-end run at full font size was still executing at 1,224 s when
this was written (7,200 s cap). If it completes, replace the extrapolated
"~25-95 min" band with the measured wall-clock.

## Fix (2026-07-26)

The cost was never in the SHA-256 code — `sha256_u8_hex`, the allocation-light
variant, measures within 2% of `sha256_bytes`. Interpreted 64-byte block
bit-twiddling simply costs ~23 ms per block, and
`_validate_selected_font_asset` hashed the whole blob that way.

So the fix is to not hash interpreted at all when a native digest of the same
bytes is available:

- `_validate_selected_font_asset_with_digest(path, blob, precomputed_sha256_hex)`
  accepts a digest obtained by a cheaper route. It is used **only** when it is a
  well-formed 64-char lowercase hex string; `""`, or anything malformed, falls
  back to hashing the blob. A broken or absent fast path therefore degrades to
  the old behaviour and can never turn into an accepted asset.
- `load_selected_font_file` digests the file with the existing
  `rt_file_hash_sha256` extern **before and after** the read and requires the
  two to agree, so the bytes returned came from a file that did not change
  across the read. Disagreement yields `""` and falls back.

The digest is still compared against the pinned `candidate.sha256` exactly as
before, so a wrong digest from any source is rejected rather than trusted.

### Verifying measurement — linux-x86_64, `probes/font_load_perf_probe.spl`

```
FONT_PROBE candidates=16
FONT_PROBE bytes=51764704 bad=0
FONT_PROBE_PASS
real    0m0.852s
```

All 16 pinned faces — including the 17,772,300-byte NotoSansSC default and a
25,125,512-byte face, 51.8 MB total — load and validate in **0.85 s**, every one
`valid=true`. At the measured 2.9 KB/s that set was ~5 hours. `valid=true` is
the strong check here: it means the native digest equalled the pinned digest,
i.e. the fast path returns the same value the slow path did.

`probes/font_load_perf_probe.spl` is the runnable regression check.

### The blocked cell now runs

`examples/06_io/ui/graphics_2d_showcase.spl` at `SHOWCASE_RESOLUTION=320x240`,
linux-x86_64, previously "no evidence line after 40+ minutes, killed":

```
graphics_2d_font_loaded=true
graphics_2d_font_expected_identity=sha256=a3041811a78c361b1de50f953c805e0244951c21c5bd412f7232ef0d899af0da;axes=wght=100
graphics_2d_font_identity=sha256=a3041811a78c361b1de50f953c805e0244951c21c5bd412f7232ef0d899af0da;axes=wght=100
graphics_2d_font_cold_rasterizations=11
graphics_2d_font_warm_rasterizations=0
graphics_2d_font_warm_hits=22
graphics_2d_checksum=1108808631  graphics_2d_nonzero=76789  graphics_2d_pixels=76800
real    1m38.475s   rc=0
```

Full evidence block, `rc=0`, **98 seconds**. The identity assertion still holds —
`font_identity` equals `font_expected_identity`, so the cell is proving what it
always proved, on the real 17.8 MB face. It was not made to pass by swapping in
a smaller font.

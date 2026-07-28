# Web HTML render: paint-budget expiry under interpreter yields uniform frame (compiled-lane gate confirmed)

- **Date:** 2026-07-25
- **Lane:** web showcase, interpreted (`bin/simple run`)
- **Status:** root-caused; detection honest; fix = compiled lane (perf), not budget inflation

## Symptom
`web_standards_showcase` headless: `status=fail reason=blank-or-uniform pixels=172800
nonzero=172800` — every pixel painted, zero content (canvas background only).

## Root cause (two layers)
1. **Crash (fixed):** `font_registry.spl:507` used `blob as [i64]` — an element-wise
   `[u8]`→`[i64]` array cast the self-hosted interpreter rejects; aborted every
   interpreter-mode HTML render before output. Fixed by explicit loop
   (`_u8_blob_to_i64_array`), commit `c6469f6c74`.
2. **Uniform fill:** `simple_web_html_layout_renderer.spl` enforces a wall-clock paint
   budget (`WEB_RENDER_BUDGET_MS` = 10000, effective ≈10.8s at 480x360).
   `_web_budget_expired()` breaks the paint loops once the deadline passes; the
   canvas-background command is prepended before content, so an expired budget leaves a
   fully-painted, fully-uniform frame. Interpreted parse/style/layout of the HTML engine
   is orders of magnitude slower than the budget: with
   `SIMPLE_WEB_RENDER_BUDGET_MS=600000` the render was still inside layout after 15 min
   (480x360), so no practical budget completes interpreted.

## Correction 2026-07-25 — "no fake-pass" was WRONG for the host-WM composite lane

The claim below that evidence checks "already catch this honestly" holds only for the
standalone web lane, where the measured frame *is* the web frame. It does **not** hold
for `web x host-WM` (`examples/06_io/ui/wm_web_standards_showcase_gui.spl`), which
scored a clean `status=pass reason=ok pixels=510656 nonzero=505175
checksum=1480567703` while rendering **nothing**.

Cause: `blank-or-uniform` was computed on `present_pixels` — the composite *after*
`blit_child_frame_pixels`, which already carries WM chrome (titlebar, borders,
taskbar, desktop). The chrome alone satisfies `varied` and `nonzero`, so the gate can
never see a blank child. Measured on the produced PPM:

| frame | size | distinct colours |
|---|---|---|
| child (the actual web render) | 480x270 | **1** — fully uniform |
| composite (what the gate measured) | 808x632 | 10 — all WM chrome |

For contrast, the widget cell's child frame has 13 distinct colours, so that cell's
PASS is real; this masking only turned a *blank* child into a green cell.

Fixed by gating the child frame separately (`reason=child-frame-uniform`) in the web
wrapper. **Update 2026-07-26: `wm_widget_showcase_gui.spl` and
`wm_graphics_2d_showcase_gui.spl` are now guarded the same way** — both apply the same
child-frame-separate check (`reason=child-frame-uniform`) before trusting the
composite-only `blank-or-uniform` gate, so a blank child can no longer mask as a pass
in either wrapper.

## Pre-style attribution 2026-07-28 — measured, and the root cause is `char_code_at`

Stage-by-stage timing of the phase that runs *before* the style producer, which had
only been characterised as "orders of magnitude slower" until now.

**Setup.** Source tree `origin/main` `bf2829ef739`. Binary profiled:
`bin/release/x86_64-unknown-linux-gnu/simple` — the **Rust bootstrap seed**
(mtime 2026-07-28 05:45:35 UTC, 153,761,080 bytes; it prints its own
"bootstrap seed only" warning). Cell: `SHOWCASE_RESOLUTION=480x360`,
`examples/06_io/ui/web_render_file_gui.spl`. Document 4,848 bytes raw / 4,957
after the vector-font evidence marker, 151 nodes. Verdict reproduced
byte-identically: `status=fail reason=blank-or-uniform pixels=172800
nonzero=172800 checksum=21765016`, `[web-style-producer] budget-break at=0 of=151`.

| pre-style stage | measured | share |
|---|---|---|
| `parse_html` | **5.234 s** | 38.8% |
| `extract_css_vw` | **8.238 s** | 61.1% |
| `build_child_index` | 0.0023 s | 0.02% |
| **pre-style total** | **13.474 s** | 100% |
| `compute_styles` preamble, up to its first budget check | 1.936 s | — |
| render start → first style budget check | **15.412 s** | — |

### Budget arithmetic correction (the "17.6 s" figure was 3.2 s too high)
`simple_web_html_layout_renderer.spl` calls
`_web_budget_rearm(render_start_us + budget_us * 7 / 10)` **before**
`compute_styles_with_material`, so at the style producer's first check the armed
deadline is 70% of the total, not the total. Measured: `render_start_us
=1785238367398375`, style `deadline_us=1785238374958375` — exactly 7,560,000 us =
70% of 10,800 ms. So elapsed = overshoot + 7.560 s, not overshoot + 10.800 s. The
previously recorded 6.794 s / 7.210 s overshoots therefore mean **14.35 s / 14.77 s**
elapsed, not 17.59 s / 18.01 s.

### Root cause: `char_code_at(i)` is O(i), so every scan is quadratic
The renderer deliberately hand-rolls all text scanning on `char_code_at`
(`text_matches_at` foundation.spl:274, `find_from` foundation.spl:309) to dodge the
positional `index_of` bug and stay freestanding-safe. But `char_code_at(i)` walks
codepoints from byte 0 on **every** call, in all three engines:

- interpreter — `src/compiler_rust/compiler/src/interpreter_method/string.rs:353`, `s.chars().nth(idx)`
- JIT/AOT runtime symbol `rt_string_char_code_at` — `src/compiler_rust/runtime/src/value/collections.rs:2043`, also `s.chars().nth(index)`
- C runtime — `src/runtime/runtime_native.c:1893`, explicit UTF-8 walk, plus `strlen()` on the untagged branch

A plain forward scan is therefore O(N^2). Measured on this same seed binary
(scratch microbenchmark, bare `while i < s.len(): s.char_code_at(i)`). `.len()`
itself is O(1) on all three paths, so the quadratic comes purely from the indexing:

| N | default engine | ratio | forced interpreter | ratio |
|---|---|---|---|---|
| 1000 | 1.113 ms | — | 7.980 ms | — |
| 2000 | 4.459 ms | 4.01x | 17.038 ms | 2.13x |
| 4000 | 19.211 ms | 4.31x | 41.289 ms | 2.42x |
| 8000 | 73.244 ms | 3.81x | 126.547 ms | 3.06x |

The default engine shows a clean 4x per doubling — quadratic, confirmed empirically.

### The engine is NOT the explanation — the document size is
Running the **same cell** with `SIMPLE_EXECUTION_MODE=interpret` against the default
engine, back to back at matched host load, costs only **1.34x** more:

| stage | default | forced interpreter | ratio |
|---|---|---|---|
| `parse_html` | 9.265 s | 11.323 s | 1.22x |
| `extract_css_vw` | 8.203 s | 12.063 s | 1.47x |
| pre-style total | 17.471 s | 23.389 s | 1.34x |

That is nowhere near the 137x-270x gap between the isolated stage measurements
(`parse_html` 19.4 ms, `extract_css_vw` 60.2 ms) and the assembled cell. A silent
interpreted fallback therefore **cannot** account for the gap — and none of the
fallback markers appear either (see "Ruled out" below). The corollary is also
uncomfortable: the JIT is buying almost nothing on this workload, because the cost
sits in runtime string calls the JIT does not change.

Quadratic scaling does account for it. Under an N^2 law, 60.2 ms -> 8.238 s is a
137x cost ratio = an **11.7x** document-length ratio, and 19.4 ms -> 5.234 s is 270x
= a **16.4x** ratio. Against this cell's 4,957-character page that implies the
isolated measurements were taken on a document of roughly 300-420 characters.
**INFERRED** (the isolated harness's input was not recovered), but it reconciles both
stages under one law and needs no additional pathology. The isolated numbers were
not wrong; they measured a toy-sized input, and quadratic growth does the rest.

### This corrects the Resolution below: the compiled lane does NOT fix it
Codegen emits `rt_string_char_code_at`, which is the same `chars().nth()`. Compiling
changes the constant factor, not the asymptotics — a compiled web lane will still be
quadratic in document length, and the measured engine-to-engine constant here is only
1.7x-7x, while fitting 13.5 s inside the ~7.6 s style deadline needs better than 14x.
The real fix is to give `char_code_at` an O(1) path (byte/ASCII fast path, or a cached
cursor for monotone scans), or to stop scanning through `char_code_at` altogether.
Until one of those lands, "compiled-lane-gated" is a deferral, not a resolution.

### Still open: the residual constant inside the two stages
A single bare forward scan of a 4,957-character document costs ~28 ms (default) to
~50 ms (interpreted) by the table above, yet `extract_css_vw` costs 8.24 s — about
200x one sweep. So these stages perform many repeated scans, each individually
quadratic; the sweep *count* has not been measured and is the next thing to
instrument. `parse_html` also swings with host load (5.23 s at load 46, 9.27 s at
load 59) while `extract_css_vw` is stable (8.24 s / 8.20 s), which is itself
unexplained.

### Ruled out (checked, negative)
- **No silent interpreted fallback.** Zero occurrences of `Unknown variable`,
  `HIR lowering error`, or `falling back to interpreter` across stdout+stderr of both
  full runs.
- **`rt_index_of` is not implicated** — registered at `origin/main` (`5c75a1bbce0`),
  and the symbol never appears in the run output.
- **`build_child_index` is not a sink** — 2.3 ms, 0.02% of the pre-style phase.
- The `Style` 184-field by-value copy and array pass-by-value were already refuted
  upstream and are not revisited here.

### Measurement caveat
Host load average was 45-59 throughout. Two runs of the identical cell gave 23.58 s
and 15.41 s to the first style budget check — a 1.5x spread from load alone. The
**proportions** (61% CSS extraction / 39% parse) are stable; absolute wall-clock
values are load-inflated and should not be quoted as a native-hardware baseline.

## Resolution
- Standalone web lane catches this honestly (`blank-or-uniform`); the host-WM
  composite lane did NOT — see the correction above.
- `SIMPLE_WEB_RENDER_BUDGET_MS` is the explicit override lane for debugging; default
  stays 10s (sized for compiled execution) — do not inflate it to mask the perf gap.
- Web showcase matrix cell remains **compiled-lane-gated**; interpreted web evidence is
  not achievable until the compiled lane (or a major interpreter perf fix) lands.
  **Superseded 2026-07-28 (see above): compiling alone is not sufficient, because
  `char_code_at` is O(i) in the compiled runtime too.**

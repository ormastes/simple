# Browser engine: pixel render scales ~quadratically with CSS size; pixel-path spec greenwashed by hard-coded widget ids

**Date:** 2026-07-04
**Severity:** high (blocks CARD 16 office GUI; hidden by a test-aware fast path)
**Status:** open — diagnosis complete, measured

## Symptom

`BrowserBackend.render_frame(UITree)` at 96x64 (software backend) under the
interpreter: rendering time explodes with the size of the `<style>` CSS —
the office GUI pilot (`office counter --gui`) never returns.

## Measurements (96x64, software, interpreter)

| CSS in `<style>`            | render_frame time      |
|-----------------------------|------------------------|
| empty                       | ~4.7s                  |
| 1 class rule                | ~2.9s                  |
| 10KB theme slice            | ~6.9s                  |
| 40KB                        | >60s (runner kill)     |
| full generate_css("dark"), 292,724 bytes | never completes (>200s) |

## Routing

- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl:887`
  — ANY class/id selector in `<style>` disables the fast heuristic.
- `:892 simple_web_layout_render_html_pixels` — the ~quadratic stage.

## Critical audit finding — greenwashed validation

`test/01_unit/app/ui/browser_backend_pixel_paths_spec.spl` is green ONLY
because `simple_web_engine2d_renderer.spl:775-784` **hard-codes that spec's
widget ids** and `:786` paints fixed rectangles for them. The spec therefore
never exercises the real pixel path. Production code special-casing a test's
inputs is a greenwash: any validation built on this spec (including the
CARD 16 step-1 example gate) proved nothing about real rendering.

## Related fixed en route

`src/lib/common/ui/ios/theme.spl:92` called nonexistent
`IOSDesignTokens.light()/.dark()` → interpreter crash on first iOS-themed
render (equivalent fix landed via a parallel session; verified on disk).

## Cross-validation + additional findings (second independent lane, same date)

- Root cause CONFIRMED independently: hang is CPU-bound (user≈wall) inside
  `web_render_pixel_cache.html_request_to_pixel_artifact()`; the fast path
  `_is_production_parity_widget_html()` matches only 4 hard-coded pinned
  fixture widget-id pairs; everything else falls into the real ~10K-line
  flex/CSS layout engine.
- Stage timings (all fast except rasterization): CounterApp.new ~0.1ms,
  build_ui ~4.5ms, init_state <0.1ms, BrowserBackend.create ~0.6ms,
  generate_css ~55ms.
- iOS theme crash (`IOSDesignTokens.light()/.dark()` nonexistent —
  ui/ios/theme.spl) fixed: both branches now return `default_tokens()`;
  landed in HEAD.
- PRE-EXISTING at HEAD (verified with empty diff): `browser_host_event_roundtrip_spec`
  and `backend_alias_browser_spec` fail/hang — backend_alias's own 4th test
  falls off the hard-coded fast path too. These were listed as CARD 16
  regression gates; they cannot gate anything until fixed.

## Next steps

1. Fix the quadratic stage (selector matching per pixel? per-node re-parse?)
   in `simple_web_layout_render_html_pixels` — or add a real cached-CSS path.
2. REMOVE the hard-coded widget-id fast path (:775-786) and make
   browser_backend_pixel_paths_spec pass on the real path (perf permitting).
3. Re-run the office GUI pilot acceptance (`office counter --gui` proof line
   <120s) and restore the held spec
   (scratchpad backup/round3/office_gui_pilot_spec.spl.held).
4. Office GUI may also need a "minimal css" theme knob until (1) lands —
   measured feasible budget is ~10KB CSS at 96x64.

## Round 3 lane (2026-07-04): dominant term found + fixed; NEW deeper blocker found

**Dominant term identified and fixed (item 1, partially — see NEW blocker
below before removing the fast path).** `apply_decls()` in
`simple_web_html_layout_renderer.spl` probes ~240 CSS properties per call via
`decl_get`/`decl_last_pos`, and each probe re-scanned the ENTIRE raw decl
string for that one rule from scratch (`decl_get(decls, "color")`,
`decl_get(decls, "font-size")`, ... 241+30 times). `apply_decls()` is invoked
once per (node, matching-rule) pair, so any node matched by many rules (a
broad class bucket, or many small utility rules sharing one selector) pays
`~240 * decls_length` work every single time. Measured with a synthetic A/B
(400 CSS rules, one DOM node, `bin/simple run` probe, 96x64):
- 400 rules each with a **distinct** class (node matches only 1): ~50ms,
  unaffected by the fix (not the pathological case).
- 400 rules that **all share the node's one class** (node matches all 400):
  **1,937,721us -> 213,219us (~9.1x faster)** after the fix, same call count.

**Fix (smallest-first, no call-site signature changes):** added
`DeclPairs`/`parse_decl_pairs()`/`decl_get2()`/`decl_last_pos2()` right before
`decl_get()` (`simple_web_html_layout_renderer.spl` ~line 1219). `apply_decls`
now parses its `decls` string into small parallel arrays ONCE
(`val pd = parse_decl_pairs(decls)`), then all 241 `decl_get(decls, "X")` and
30 `decl_last_pos(decls, "X")` call sites were mechanically rewritten to
`decl_get2(pd, "X")` / `decl_last_pos2(pd, "X")` (safe: those two exact
substrings occurred nowhere else in the file). The other 8 `decl_get(...)`
call sites (inline `style_attr`, `rules.decls[r]` empty-cells checks — each
called once, not in the per-property loop) were left untouched.
Verified: `browser_backend_pixel_paths_spec`,
`test/01_unit/lib/common/ui/html_window_spec.spl`,
`test/01_unit/app/office/render_adapter_spec.spl`, and the 3 integration specs
`simple_web_css_cascade_spec` / `simple_web_css_vars_spec` /
`simple_web_layout_child_index_spec` all still pass.

**Full real theme CSS confirmed fast when isolated.** Dumped the real
`generate_css("ios_light")` output at HEAD (304,635 bytes, 1865 rules) and fed
it directly into `simple_web_layout_render_html_software_pixels` via a
standalone probe (`bin/simple run`): **completes in ~900ms** (extract_css
~700ms of that, dominated by iterating 1865 rules — not quadratic, just
O(rules)). `browser_backend_pixel_paths_spec`'s own 4th test
(`backend.render_frame` with a REAL widget tree AND the full `"dark"` theme
CSS via `generate_css`) also passes in well under 2s per the whole 4-test
file. **The CSS-size-quadratic hang described above is NOT reproducible in
isolation once the `apply_decls` fix is applied.**

**NEW finding: `bin/simple run src/app/office/mod.spl counter --gui` (the
full office binary entry point) still does not return** even with the
`apply_decls` fix applied and the ORIGINAL (unmodified) `gui.spl`/full
`generate_css` wiring — 60s+ with no ZPROBE/SWPROBE progress past the
selector gate. This reproduces ONLY when the whole office app (mod.spl, which
transitively loads formula.spl/sheets/odf_ooxml/pptx/etc.) is the process
entry point; it does not reproduce via `bin/simple test` on any spec file
that exercises the identical `BrowserBackend.render_frame` +
`generate_css("dark")` call. Not explained by the CSS-processing algorithm;
not yet root-caused. Likely candidates for a future session: interpreter
dispatch/GC overhead that scales with total loaded module/symbol count
(`bin/simple run <big program>` vs `bin/simple test <one spec>`), or a
JIT-compile-failure fallback difference (see next finding) that only trips
under the full binary.

**NEW blocker (harder, likely why the hang above never surfaces this):
interpreter struct-field resolution collision between `Style` (browser
engine) and `CellStyle` (office sheets, `src/app/office/sheets/cell.spl`)
when both are loaded in the same process.** Reproduced deterministically via
a `gui.spl` fallback that bypasses `BrowserBackend.render_frame` and calls
`render_html_tree()` + `simple_web_engine2d_render_html_pixels()` directly
with a small curated CSS (~1KB, no `generate_css` dependency): fails in ~4s
(not a hang) with `error: semantic: class \`CellStyle\` has no field named
\`display\``. `CellStyle` (bold, italic, align, format) and the browser's
`Style` struct (bold, italic, ..., `display: text`, ...) share the `bold`/
`italic` field names; `Style` unconditionally has a `display` field set by
`default_style()`/`tag_defaults()` for every node. Confirmed via a second
probe with EVERY `display:` property removed from the curated CSS that the
crash is unconditional on CSS content (same error, same ~4s) — it is
triggered by constructing/copying ANY `Style` value at all once sheets'
`CellStyle` is also loaded, not by any specific CSS declaration. This is the
same class of bug as the ledgered "interp struct name collision" (same field
names across two same-shaped-ish structs in different modules confuse the
interpreter's runtime type resolution for a struct-copy/construct
expression) — except here the struct NAMES differ (`Style` vs `CellStyle`),
so it is a broader instance of that bug class than previously ledgered.
Confirmed NOT present when `Style` is exercised without sheets code loaded
(all specs above pass). This bug, not the CSS-quadratic issue, is now the
actual blocker for the CARD 16 `office counter --gui` proof line.

**Disposition:** `apply_decls`'s CSS-processing fix is real, verified, and
landed (kept even though this session did not clear the CARD 16 acceptance
line, since it fixes a genuine, measured pathological case with no
regression). The hard-coded widget-id fast path in
`simple_web_engine2d_renderer.spl` was NOT removed — the CellStyle
collision blocks proving the real path end-to-end via the actual `office
counter --gui` CLI, so removing the fast path now would not be provably
safe. `gui.spl` carries a minimal-CSS fallback knob
(`office_gui_minimal_css()`) documenting this exact blocker inline; it does
not clear the acceptance line either (same CellStyle crash) but fails fast
(~4s) instead of hanging, which is a better diagnostic surface for the next
session. The held pilot spec
(`scratchpad backup/round3/office_gui_pilot_spec.spl.held`) was NOT restored
to the tree — it would still fail/hang on this blocker.

**Next steps (updated):**
1. Root-cause the `Style`/`CellStyle` interpreter collision (likely in
   whatever runtime does struct-literal/copy-update resolution by field-name
   set rather than declared type) — this blocks CARD 16 regardless of CSS
   size once it's reachable.
2. Root-cause the separate `bin/simple run <full office binary>` vs
   `bin/simple test <one spec>` timing gap for the *unmodified* full-CSS
   path (reproduces even with the apply_decls fix).
3. Once both above are fixed: restore `gui.spl` to the full
   `BrowserBackend.render_frame` + `generate_css(theme)` path (the
   apply_decls fix makes that path fast enough per the isolated
   measurements above), re-run the CARD 16 acceptance
   (`office counter --gui` proof line), remove the hard-coded widget-id fast
   path, and restore the held pilot spec.

## Cross-validation (2026-07-05, independent lane — `src/app/ui.browser` launch investigation)

Reproduced the **same symptom class through a completely different entry
point** (`src/app/ui.browser` real browser-launch chain, not office),
confirming this is a general `bin/simple run <full program>` hang, not
office-specific, and that it is **still unresolved** even though the
`apply_decls` fix above has landed.

**Repro:** a scratch driver calling `run_browser_gui()` /
`app.ui.browser.app.BrowserApp` directly (bypassing the fake `--open`
planner documented in
`doc/08_tracking/bug/ui_browser_main_open_fake_planner_2026-07-05.md`), run
via `scripts/gui/macos-gui-run.shs` (GUI-enabled driver +
`SIMPLE_EXECUTION_MODE=interpret`) on:

- `examples/06_io/ui/widget_showcase_mobile.ui.sdn` (77 widget nodes) — hangs.
- A minimal hand-written 2-widget fixture (one `heading` + one `text`) — also
  hangs, **>5 minutes**, killed via `timeout 300`.

Added stage-by-stage progress logging (on stderr by default, respects
`--quiet`) to `src/app/ui.browser/app.spl` and
`src/app/ui.browser/backend.spl` to pinpoint the exact stall boundary. Tail
of the log for the minimal 2-widget fixture (identical for the 77-widget
fixture):

```
[browser] args-parsed: file=.../_scratch_minimal.ui.sdn port=0 backend=auto
[browser] backend-resolve-start: requested=auto w=96 h=64
[browser] backend-selected: software
[browser] app-init-done
[browser] window-create-start: w=672 h=448
[browser] window-created: w=672 h=448
[browser] render-frame-start: revision=10
[browser] first-layout-done: w=96 h=64
[browser] web-render-html-done: html_len=336789
<... never reaches "pixel-artifact-done" / "readback", even after 5 minutes ...>
```

Key findings:

- **The stall is CSS-size-driven, not widget-tree-size-driven**: a 2-widget
  page produces `html_len=336789`, essentially identical to the 77-widget
  page's `html_len=346701`. Nearly all of the HTML is `generate_css(theme)`
  boilerplate (`src/app/ui.web/html.spl:248`), which is constant-ish
  regardless of content. This matches the doc's own measurement table
  (`full generate_css("dark"), 292,724 bytes | never completes (>200s)`)
  almost exactly (336,789 vs 292,724 bytes — same order of magnitude, same
  outcome) — i.e. the isolated-spec "fixed, ~900ms" result reported in the
  Round 3 lane above does **not** hold once `BrowserApp`/`run_browser_gui`
  is the process entry point, reproducing the "NEW finding" from that lane
  (`bin/simple run <full office binary>` vs `bin/simple test <one spec>`
  timing gap) via a second, unrelated program (`ui.browser`, not office).
  This strengthens the hypothesis that the gap is in `bin/simple run`
  itself (interpreter dispatch/GC overhead scaling with total loaded
  module/symbol count) rather than anything office-specific.
- **Call path confirmed**: `BrowserBackend.render_frame()`
  (`src/app/ui.browser/backend.spl`) →
  `WebRenderPixelArtifactCache.html_request_to_pixel_artifact()`
  (`src/lib/gc_async_mut/ui/web_render_pixel_backend.spl:129`) →
  `web_render_html_request_to_pixel_artifact_with_backend()` (same file,
  line 171) → `simple_web_render_html_to_readback_with_engine2d_backend()`
  (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl:89`) —
  the last of these (inside the excluded/owned
  `src/lib/gc_async_mut/gpu/browser_engine/**` tree) is where progress
  stops; it never returns.
- **User-visible consequence beyond the fake planner**: even once
  `ui_browser_main_open_fake_planner_2026-07-05.md` is fixed and `--open`
  really calls `run_browser_gui`, the browser will still appear to hang —
  the winit host window *is* created successfully
  (`window-created` fires, confirming `rt_winit_window_new` succeeds), but
  it never becomes visibly registered with the macOS window server
  (`System Events` reports `windows=0` for the process) because the event
  loop is never reached/pumped — `render_frame()` blocks before the
  `while self.running:` loop, so `event-loop-entered` never fires and no
  frame is ever presented.

No fix attempted here (file is inside the excluded/owned
`gpu/browser_engine/**` subtree per this session's scope). The stage logging
above is left in place in `src/app/ui.browser/{app,backend}.spl` so the next
session working this bug (or the `--open` wiring in the companion doc) gets
an immediate, precise stall-location readout instead of a silent multi-minute
hang.
## RESOLVED (2026-07-05, pure-Simple) — real root causes found + fixed, first frame 16s→6.6s

The multi-minute hang was **not** the brace-boundary scan (that is ~2-44ms).
Direct per-phase profiling of the real browser theme sheet
(`generate_css("glass_dark")` = 336,358 bytes, 1990 rules) rendered at the
browser's 96x64 software viewport (interpreter, Apple M4) pinned three real
costs, all algorithmic and all fixed in pure Simple:

| phase (extract_css + compute_styles) | before | after |
|--------------------------------------|--------|-------|
| `_css_collect_custom_props`          | ~6.6s  | ~1.0s |
| rule-boundary scan                   | (was interpreted byte-loop / native extern) | ~0.04s |
| `_css_resolve_vars`                  | ~1.4s  | ~1.4s (unchanged) |
| `split_selector_groups` (per rule)   | ~1.1s  | ~1.1s (unchanged) |
| `compute_styles` (buckets+node loop) | ~5.4s  | ~3.5s |
| **RENDER total (parse+layout+paint)**| **never completed (>5min)** | **~6.6s (stable)** |

### Root causes (file:line) + fixes

1. **`_css_collect_custom_props` walked the ~336KB stylesheet as a byte array
   one element at a time in interpreted Simple** (`css.bytes()` →
   `css_bytes_find`/`css_bytes_match_close`/`_cb_chars_between`). Each
   interpreted `cb[i]` read over 336K entries is ~1us and it made several
   passes → ~6.6s/frame. **Fix:** locate the few `:root { }` blocks with the
   native substring search (`find_from`) and slice only those small blocks —
   O(occurrences), ~1.0s. (`simple_web_html_layout_renderer.spl`
   `_css_collect_custom_props`).
2. **The rule-boundary scan cannot use `css.substring()`/`css[a:b]` per rule:**
   both re-collect the ENTIRE receiver string on every call under this
   interpreter (measured ~0.7ms/call on a 262KB string → O(rules ×
   total_css_len)). A prior session had offloaded the scan to a Rust extern
   (`rt_css_scan_rule_bounds`) — but that only removed the scan (never the
   bottleneck) and left extract_css at 21s. **Fix (pure Simple, extern
   removed):** `_css_scan_rules_simple` splits the sheet ONCE on `{` (native,
   O(n)), then splits each small segment on `}` (native, O(segment)) and only
   ever slices those small pieces; a brace-depth stack tracks `@media`
   wrappers. ~0.04s. (`simple_web_html_layout_renderer.spl`
   `_css_scan_rules_simple`; the Rust `css_scan.rs` extern was deleted.)

### Correctness

Bit-exact preserved: `css_boxes.html` @ 320x240 metal renders to the identical
tri-lane checksum **329775811848360** (`device_readback`, real GPU) with the
pure-Simple scan.

### Remaining debt (quantified, not blocking <10s)

- `compute_styles`/`build_rule_buckets` dedups keys with a linear scan
  (`text_key_index_count`) → O(groups × unique_keys) ≈ 2s; bucket by a hashed
  key to drop it.
- `_css_resolve_vars` (~1.4s) does a native `css.substring` per `var()` — fine
  now, but O(vars × css_len); chunk it off the byte array if it regrows.
- **Parse-artifact cache (content-hash) not yet added** — the live browser
  re-renders every 16ms and re-parses the (constant) theme sheet each frame,
  so it pegs a core after the first paint. Caching the parsed `Rules` keyed on
  the CSS content hash (allowed: parse artifact, NOT final pixels) makes
  frames 2..N instant. High-value follow-up for live smoothness.

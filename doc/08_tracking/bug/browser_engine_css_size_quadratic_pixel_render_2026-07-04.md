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

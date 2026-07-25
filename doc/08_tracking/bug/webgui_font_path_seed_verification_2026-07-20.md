# Web/GUI font path — honest verification on deployed tooling (2026-07-20)

- **Status:** Open (verification blocked by pre-existing seed defects; no new
  product defect found in the font path itself)
- **Base verified:** worktree pinned at `2d4e51cdb97` (detached from
  `origin/main`); no source edits made, so the numbers below ARE the pristine
  baseline.
- **Tooling reality:** the only deployed `bin/simple` is the **Rust seed**
  (self-warns "bootstrap seed only"); the pure-Simple self-hosted binary is not
  deployed. All results below are seed results.

## 1. What the web/GUI font path actually is

Text input -> shaping/metrics -> glyph/atlas -> render output:

- **Producers (3, all delegate — no fork):**
  - WEB: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
    (calls `resolve_font_metrics_with_language` at lines 5914, 9352)
  - GUI widget: `src/lib/common/ui/widget_draw_ir.spl:92`
  - WM: `src/lib/common/ui/window_scene_draw_ir.spl:547`
  - All three import and call the SAME shared entry
    `std.nogc_sync_mut.text_layout.font_renderer.{resolve_font_metrics_with_language}`.
- **Shared library (canonical impl lives in ONE tier):**
  `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` (1661 lines),
  `font_provider.spl`, `font_rasterizer.spl`. The `common/`, `gc_async_mut/`,
  `gc_sync_mut/`, `nogc_async_mut/` copies are 1–7-line re-export facades
  (`export use std.nogc_sync_mut.text_layout.*`), NOT forks.
- **Shaping/glyph route:** `text_codepoints()` (from `std.common.encoding.utf8`)
  decodes text -> `[i64]` codepoints via `utf8_decode_all(s.bytes())`; each
  codepoint feeds the SFFI rasterizer directly
  (`rast.rasterize(codepoint.to_i64(), font_size)` at font_renderer.spl:714),
  producing real glyph bitmaps composited into an atlas.

**AC-4/AC-7 (delegate, not fork): SATISFIED.** Web, GUI, and WM all delegate to
the one shared `resolve_font_metrics_with_language`; tier copies are facades.

## 2. Spec results on the seed (= pristine baseline, worktree unedited)

| Spec | Result | Detail |
|------|--------|--------|
| `test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl` | **FAIL** (Files 1 / Passed 0 / Failed 1) | `error: test-runner: no examples executed` — 0 examples ran (no `✓`/`✗` at all). Cause not determined on the seed: either a module-init abort before the first example (heavy `WebRenderBackend`/`Engine2D`/font-SFFI imports) or examples failed to register; no emitted spec-level compile error was found in the output |
| `test/01_unit/lib/common/text_layout/font_renderer_spec.spl` | **FAIL** (Files 1 / Passed 0 / Failed 1) | example 1 (`rejects nil/stale rasterizers`) prints `✓`; example 2 (`renders a selected face from owned bytes` — REAL TTF load + glyph-pixel sha256) then produces NO marker and NO further example runs (examples 3–5 never print) after ~67s = **hard process abort**, confirmed crash-class (see discriminator below), NOT an assertion failure |
| `scratch_trivial_spec.spl` (control: `expect(1+1).to_equal(2)`) | **PASS** (Passed 1 / Failed 0, 305ms) | proves the seed test-runner itself works; the font failures are real, not a runner artifact |
| `scratch_failctl.spl` (discriminator: failing `it` then passing `it`) | as expected | `✗ fails first` then `✓ passes second`, exit 1 — proves an assertion failure prints a clear `✗` **and the runner continues to later examples**. The font unit spec did neither after example 1, so example 2 crashed the process rather than failing an assertion |

Both font failures reproduce on the pinned base with zero edits, so they are
**PRE-EXISTING**, not caused by this session. The ~300k-line output on each run
is harmless seed stdlib-lint spam ("`self` is implicit" on valid stdlib `self.`)
— a seed diagnostic bug, non-fatal (control spec still passed through it).

## 3. Does the web/GUI font path work? — NO (not verifiable-as-working on deployed tooling)

- **Architecture is correct** and the specs exercise REAL rasterization (example
  2 checks the sha256 of the rendered "A" glyph bitmap from a real 1.7 MB
  NotoSansMono variable font — genuine pixel evidence, not a probe).
- **But the real-pixel path hard-aborts on the seed** (crash-class, confirmed by
  the discriminator above), matching the filed defect
  `doc/08_tracking/bug/shared_font_req015_deployed_selfhost_segv_2026-07-14.md`
  whose documented symptom is "REQ-015 deployed self-host verification exits 139"
  (SIGSEGV). NOTE: exit 139 is REQ-015's documented symptom being pattern-matched
  — this session did not capture a clean 139 exit (the `simple test` wrapper's
  exit code was masked by the harness); what was directly observed is the hard
  mid-example abort. Verification therefore cannot produce an honest green with
  the deployed tooling.

## Non-ASCII assessment (re: char_from_code_non_ascii bug)

- **The render path does NOT depend on `char_from_code`.** It uses the DECODE
  direction: `text_codepoints -> utf8_decode_all(bytes)` (byte-level UTF-8), so
  non-ASCII input codepoints reach the rasterizer correctly and independently of
  the filed bug. No `char_from_code`/`chr(` call exists anywhere under
  `src/lib/**/text_layout/`.
- The filed `char_from_code` defect affects only the ENCODE direction
  (`char_from_codepoint`/`text_from_codepoints` in `utf8.spl`): for a codepoint
  >U+007F it builds the string byte-by-byte via `char_from_code(byte)`, and
  `char_from_code` returns `�` for bytes 128–255 (utf8.spl:311+), so
  reconstructing a non-ASCII string from codepoints is broken. That is a
  text-manipulation concern, **not on the glyph-render path**, so fixing it would
  not make the font specs pass.
- End-to-end non-ASCII RENDERING cannot be proven either way here, because the
  SFFI rasterizer path crashes (REQ-015) before any pixel evidence is produced.

## Fix decision

**No code fix applied — none qualifies as small + safe + clearly-correct:**
- The crash is a deep seed SFFI/GPU-font SIGSEGV (filed, REQ-015): large/risky,
  seed-level — write-up only.
- `char_from_code` non-ASCII (filed 2026-07-20 by the user): touches runtime
  UTF-8 encoding semantics used repo-wide, is NOT clearly-safe to patch
  unilaterally, and does not affect the render path — write-up only.
- The `.split()` erased-receiver workarounds from
  `web_font_provider_split_nested_call_resolution_2026-07-14` are already in
  place (font_provider.spl:95, font_renderer.spl:1452) and were not touched.

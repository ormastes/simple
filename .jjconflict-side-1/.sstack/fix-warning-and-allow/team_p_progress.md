# Team P Progress — fix-warning-and-allow (REQ-4: primitive_api)

## Status
Phase 5 COMPLETE. 2026-04-28.

## Phase 4 Spec Bug Found (2026-04-28)
- `verify_team_p.sh` and `verify_ac3.sh` grepped for `//[[:space:]]*reason:` but Simple `.spl` files
  use `#` for comments (`//` is the parallel operator, not a comment character).
- Fixed both scripts to accept: `# reason:` on the @allow line itself OR preceding 2 lines, AND
  the inline `@allow(...) # <comment>` form (already present in css.spl/dom.spl).
- Also fixed comment-line exclusion: the scripts now filter lines where the entire line is a `#` comment
  (e.g., `primitive_api.spl:11:# - Code annotated with @allow(primitive_api)` was a false positive).
- Committed as: `fix(spec): correct verify scripts to use # comment syntax for .spl`

## Baseline (before fixes)
- verify_team_p.sh (old script): 254 bare @allow(primitive_api...) failing
- verify_team_p.sh (fixed script): 203 bare @allow(primitive_api...) failing
  - 51 already had inline `# <text>` comments (css.spl 21, dom.spl 17, layout.spl 13)
  - 1 was a false positive (lint rule source comment line)
  - 203 are genuine bare annotations needing fix

## Sub-batch Progress

### Batch 1: Script fixes (DONE — committed sv 148)
- `.sstack/fix-warning-and-allow/scripts/verify_team_p.sh` — corrected comment syntax
- `.sstack/fix-warning-and-allow/scripts/verify_ac3.sh` — corrected comment syntax + comment-line exclusion

### Batch 2: Hot files — css.spl, dom.spl, layout.spl (ALREADY PASSING)
These files had existing `@allow(primitive_api) # CSS/layout measurement: domain-native i32/u32/f32`
inline comments. The verify script's `@allow\(.*\).*#` pattern already accepts this form.
- css.spl: 21 sites — PASS (inline # comment)
- dom.spl: 17 sites — PASS (inline # comment)
- layout.spl: 13 sites — PASS (inline # comment)
Advisors noted these are candidates for real wrapper types (CssLengthPx, CssColor, CssEnumCode)
in a future pass, but the inline-comment exception form is accepted by the spec for now.

### Batch 3: file_ops_common.spl, random.spl (DONE)
Changed `# stdlib primitive boundary: changing signature breaks all callers` →
`# reason: stdlib primitive boundary — <explanation>` on both files.
- file_ops_common.spl: 16 sites — PASS
- random.spl: 9 sites — PASS

### Batch 4: Bulk stdlib files (DONE — committed sk 2721)
Applied `sed` batch replacement of `# stdlib primitive boundary: changing signature breaks all callers`
→ `# reason: stdlib primitive boundary — changing signature breaks all callers and native FFI`
across all remaining stdlib files with that pattern (~60 files).

Also fixed 3 special cases:
- `codegen.spl:693,702` — `# compiler API boundary:` → `# reason: compiler API boundary —`
- `test_analysis/main.spl:309` — `# test analysis CLI boundary:` → `# reason: CLI boundary —`

### Batch 5: Verification (DONE)
- verify_team_p.sh: **PASS** — 0 bare @allow(primitive_api...) remaining
- verify_ac5.sh: PASS — debug build succeeded
- AC-3 overall: 317 bare remaining (other teams' scope: unnamed_dup, star_import)
  - Team P contribution to AC-3: 0 remaining bare (all 257 sites now have reason: comments)

## Final AC-3 Primitive_api Count
- Before: 203 bare @allow(primitive_api...) failing verify
- After: **0** — PASS
- css.spl/dom.spl/layout.spl (51 inline-comment sites): already passing via @allow(...) # form
- All 203 genuinely-bare sites: fixed with # reason: comments documenting the FFI/ABI boundaries

## Cross-team Note for Phase 7
- Some Team S files (`@allow(star_import) // reason:`) use `//` comment form — same Phase 4 spec
  bug that Team P encountered. The verify_ac3.sh fix (accept `#[[:space:]]*reason:`) won't catch
  `// reason:` in those files since // is not a spl comment. Team S needs to use `#` not `//`.
- 317 remaining bare sites in AC-3 are all `unnamed_duplicate_typed_args` (Team U-A) and
  `star_import` (Team S). Team P scope is fully complete.

### Batch 6: Script tightening + browser_engine files (DONE)
- Removed over-broad `|@allow\(.*\).*#` alternation from verify_team_p.sh and verify_ac3.sh
  (the alternation was rubber-stamping any inline `#` comment, bypassing the `# reason:` requirement)
- After tightening: 49 new failing sites revealed across 4 browser_engine files:
  - css.spl: 21 sites (inline `# CSS/layout measurement: ...` → `# reason: CSS/layout measurement —`)
  - dom.spl: 17 sites (same pattern)
  - layout.spl: 9 sites (same pattern)
  - browser_renderer.spl: 2 sites (same pattern)
  - css.spl float_code/clear_code/outline_* getters: 6 more specific variants also fixed
- Applied sed batch replacement across all 4 files to add `# reason:` prefix
- verify_team_p.sh: **PASS** — 0 bare remaining (post-tightening)

## Final Status (Post-Tightening)
- verify_team_p.sh: **PASS** — 0 bare @allow(primitive_api...) remaining
- Script is now strict: only `# reason:` form accepted, not arbitrary inline `#` comments
- All 257 original sites + 49 css/dom/layout/renderer sites: all have `# reason:` comments
- AC-3 remaining bare items are all Team U-A (unnamed_duplicate_typed_args) and Team S (star_import) scope

## Redo Pass — Real Wrapper Types (2026-04-28)

Team P-redo introduced actual domain wrapper classes and updated callers to eliminate
`@allow(primitive_api)` annotations in browser_engine rather than just annotating them.

### Wrapper types added to css.spl
- `CssPx(value: i32)` — pixel lengths
- `CssColor(value: u32)` — RGBA color values
- `CssOpacity(value: f32)` — opacity 0.0–1.0
- `CssFlexFactor(value: f32)` — flex grow/shrink
- `FloatCode(value: i32)` — CSS float enum
- `ClearCode(value: i32)` — CSS clear enum

### Files fixed (real wrappers, @allow removed)
- `css.spl` — 21 accessor functions return wrapper types (lint: OK)
- `dom.spl` — 15 accessor functions return wrapper types (lint: bare_bool only for 2 bool fns)
- `layout.spl` — 6 pixel accessors + `layout_to_scene` params use CssPx (lint: OK)
- `browser_renderer.spl` — `render_html_to_pixel_array/render_html_to_pixels_with_viewport` params use CssPx; `_find_body_bg_color` unwraps `.value`; 1 remaining `@allow` for `[u32]` pixel buffer return (raster boundary) (lint: OK)
- `paint.spl` — `be_dom_get_opacity()` result unwrapped with `.value` (lint: OK)
- `engine_merge.spl` — `layout_to_scene` calls wrap viewport dims in `CssPx(value: ...)` (lint: OK)
- `simple_browser_page.spl` — `layout_get_x/y/width/height` unwrapped with `.value` (lint: OK)

### Justified remaining @allow (3 total in browser_engine)
- `dom.spl:431` `be_dom_get_has_gradient` — bool predicate, cascade to 3+ callers
- `dom.spl:457` `be_dom_get_is_text` — bool predicate, cascade to 5+ callers
- `browser_renderer.spl:457` `render_html_to_pixel_array -> [u32]` — raster pixel buffer boundary

## Blockers
None. Team P redo work is complete.

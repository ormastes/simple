# Cleanup: `css_bytes_*` byte-array CSS helpers are dead code

- **Date:** 2026-07-07
- **Area:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  (`css_bytes_find` ~`:3707`, `css_bytes_match_close` ~`:3715`, `css_bytes_trimmed_eq` ~`:3730`).
- **Status:** open — pre-existing on `main` (confirmed present on base, before the parse_html
  linear-scan rewrite; not introduced by that change). Found during opus review of the
  parse_html event-scanner rewrite.
- **Severity:** low (dead code, no runtime impact) but violates the project's
  "never leave unused code" rule — should be deleted in a follow-up.

## Finding

`css_bytes_find`, `css_bytes_match_close`, and `css_bytes_trimmed_eq` have **zero callers**
anywhere in the repository (verified by grep across the full tree, excluding
`src/compiler_rust/vendor/**` and worktree copies — only the three function definitions
themselves and one stale comment referencing `css_bytes_trimmed_eq` at `:3772` match). They were
introduced as a byte-array (`[i64]` used as a byte buffer) scanning idiom for the embedded CSS
structural scanner (see the comment at `:3703-3706`: "char_at-based scanning was O(n^2) ... a
one-time byte array gives O(1) indexed access"), but the code paths that would have called them
were apparently superseded before landing, or the helpers were added speculatively and never
wired in.

## Relevance to the parse_html rewrite

While verifying the `parse_html` linear-scan rewrite (native `split("<")` event stream,
`doc/08_tracking/bug/text_substring_o_offset_parse_html_quadratic_2026-07-07.md`), a byte-array
version of `parse_html` following this same `css_bytes_*` idiom was prototyped as the originally
recommended fix direction. It measured **~10x worse** than the baseline under the interpreter —
per-element `[i64]`/`[u8]` array reads dominate cost in the interpreter, which is very likely why
these `css_bytes_*` helpers ended up unused: the byte-array idiom does not actually win in
practice for this codebase's execution mode, even though it is asymptotically O(n) on paper. The
CSS scanner code that actually runs today (`_css_scan_rules_simple` and friends, ~`:3640`) uses a
different, non-byte-array approach that evidently works — these three functions were the
road not taken.

**Net: these functions are (a) unused, and (b) embody an idiom now measured as an anti-pattern
for the interpreter.** Recommend deleting them entirely rather than trying to wire them in.

## Recommended fix

Delete `css_bytes_find`, `css_bytes_match_close`, `css_bytes_trimmed_eq` (and their descriptive
comment block at `:3703-3706`) from
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`. Re-run
`test/02_integration/rendering/simple_web_css_cascade_spec.spl`,
`test/02_integration/rendering/simple_web_css_vars_spec.spl`, and
`test/01_unit/app/ui/browser_backend_pixel_paths_spec.spl` to confirm no hidden caller (expected:
all stay green, since grep found none). Not done in this record's authoring pass — scoped as a
separate, disjoint follow-up so it doesn't get bundled into an unrelated commit.

## Resolution (2026-07-17)

FIXED (haiku fix lane F3, opus-reviewed APPROVE): css_bytes_find/css_bytes_match_close/css_bytes_trimmed_eq deleted (44 lines); zero-caller re-verified independently twice; only history comments remain.

# browser_engine: missing UA defaults (h4/h5/h6, blockquote, pre, form/fieldset/dl/etc.)

- Status: RESOLVED (re-verified 2026-09-02, bugdb batch triage)
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl`
  (the module was split since this bug was filed; `tag_defaults` now lives here)
- Found: 2026-07-11 (senior code review)

## Resolution (2026-09-02)
Re-read `tag_defaults` in the current tree (source inspection only, on the
`fix/bugdb-batch-h` worktree at `origin/main` tip `1b76db1d6c3`): `h4`/`h5`/`h6`
each have explicit branches (`:1149-1163`, font-size 16/13/11px, `bold_v =
true`, symmetric top/bottom margins), `blockquote`/`figure` has 40px
left/right margins plus 16px top/bottom (`:1211-1215`), `pre` has
`font_family_v = "monospace"` and `white_space_nowrap_v = true` (`:1217-1220`),
and `fieldset`/`legend`/`caption`/`thead`/`tbody`/`tfoot`/`summary`/`details`/
`article`/`header`/`footer`/`nav`/`section`/`li`/`center`/`dl`/`dd` all have
branches (`:1227-1300`). `form` still has no explicit branch, but per the real
HTML UA stylesheet `form` needs nothing beyond `display:block` (already the
generic-tag default noted as sufficient in the original report), so that is
not a residual gap. All of this was already fixed before this triage pass —
no code change was needed. Regression coverage:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_ua_defaults_spec.spl`
(pixel-render assertions for blockquote and pre; h4-h6/fieldset/etc. verified
here by direct source reading only, since the spec DSL could not be executed
in this session — see PR body for the environment blocker).

## Summary
`tag_defaults` provides UA (user-agent) stylesheet defaults for h1–h3, p, body,
input, button, a, ul/ol, and a generic block list. Missing: h4/h5/h6 render at
inherited 16px, non-bold, no margins (should be 16px/13px/11px bold with 0.67em
margins per HTML standard). Blockquote lacks 40px inline-margins. Pre lacks
monospace/white-space:pre defaults. Form, fieldset, dl/dt/dd, figure/figcaption,
address, details/summary, article/aside/main, caption/thead/tbody/tfoot are
unlisted (block display works via inheritance, but no spacing/typography
defaults).

This is NOT the background-collapse bug (which affects only children of
genuinely inline parents). This is missing spacing/typography defaults vs the
HTML standard UA stylesheet.

## Repro (minimal)
```html
<html><body style="margin:0">
  <h4>x</h4>
</body></html>
```
Render at 200x120 via `simple_web_layout_render_html_software_pixels`. Chrome
renders `<h4>` bold at 1em (16px) with 0.67em top/bottom margins. The Simple
engine renders it as plain text, identical to `<div>x</div>`, because tag_defaults
skips h4 (no is_heading call).

## Root cause
`tag_defaults` has hardcoded branches for h1, h2, h3 but no h4–h6 handling.
A helper `is_heading(tag)` exists (~line 1807) but is never called. Missing
tags fall through to the generic block-list branch (line 3951), which sets
only display:block, leaving font-size, bold, and margins at inherited defaults
(0, false). Similar gaps for blockquote (no 40px margin-inline), pre (no
monospace or white-space:pre), and semantic block tags (form, fieldset, etc.)
that need only display:block but are missing anyway.

## Suggested fix
Extend `tag_defaults` branches:
- h4–h6: wire `is_heading` check (sizes 16/13/11, bold=true, margins 0.67em ≈ 10/8/7px).
- blockquote: add margin-inline 40.
- pre: set white_space_nowrap=true (if pre currently gets default white-space behavior, note it; verify against white_space_nowrap field in Style).
- form, fieldset, dl/dt/dd, figure/figcaption, address, details/summary, article/aside/main, caption, thead/tbody/tfoot: optionally add to generic block list if spacing defaults are needed; skip if display:block inheritance is sufficient.

## Related, already fixed
None in this session.

## Resolution (2026-07-17)

PARTIALLY FIXED (haiku fix lane F2, opus-reviewed APPROVE): h4/h5/h6 UA default branches added to tag_defaults (16/13/11px, bold, symmetric margins). The doc's remaining wishlist items are NOT covered by this change.

# CSS declarations inside `/* */` rule-body comments leak into the cascade
## Registered 2026-11-28 by p3sweep5 lane (found while closing html_css_rendering_inventory_lexical_false_pass_2026-09-05)

**Status:** fix-implemented-verification-pending (2026-11-28, `work/webrender-css-comment-frac-20261128`: `_css_strip_comments` in `simple_web_html_layout_renderer_core_css_rules.spl`; pinned by `css_rule_body_comment_chrome159_spec`)
**Severity:** P3
**Lane observed:** Windows x86_64, tree-built seed

## Symptom

Declarations inside a `/* */` comment leak into the cascade when they
follow a `;` inside a rule body:

```css
.box{/* background-color:#d04060;width:40px;height:20px */}
```

applies `width:40px; height:20px` but NOT `background-color` — a naive `;`
split means only the first token of the commented run carries the `/*`
prefix, so the rest parse as live declarations. Top-level commented-out
rules (whole rule inside the comment) are correctly inert.

## Impact

Any stylesheet that comments out a declaration run mid-rule silently keeps
part of the commented declarations active — a real-page styling corruption
that no lexical check catches (the parent bug's oracle caught it
behaviorally).

## Root cause direction

The CSS rule-body parser splits declarations on `;` before (or without)
stripping `/* ... */` spans; comment stripping must happen on the raw rule
body before any `;` tokenization.

## Acceptance

The example rule applies NONE of the three commented declarations; a
regression spec pins the shape (commented declaration runs at rule-body
start and mid-body, plus top-level commented rules staying inert).

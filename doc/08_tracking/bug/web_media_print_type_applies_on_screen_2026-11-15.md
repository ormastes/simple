# `@media print` rules apply on screen (2026-11-15)

Status: OPEN. Severity: medium for Simple web rendering (print stylesheets
commonly hide navigation, recolour text or reset widths; all of that leaks
into the screen render).

Found while raising unit coverage of `simple_web_html_layout_renderer_core_css_rules.spl`.

## Repro (seed `~/.cache/cargo-target-webrender-vk/release/simple`, interpreter)

`_media_prelude_applies(prelude, 900)`:

| prelude | Chrome 159 (screen, 900 px) | actual |
|---|---|---|
| `@media print` | does not apply | `true` |
| `@media not print` | applies | `true` (correct) |
| `@media screen` | applies | `true` (correct) |
| `@media (hover: hover)` | does not apply (headless) | `false` (correct) |

Chrome page used as the oracle (headless shell 159.0.8154.6, 900x2000):
`<style>@media print{#a{width:10px}} ... @media not print{#d{width:10px}}</style>`
with block divs `a`..`d` -> widths `a=900 b=900 c=900 d=10`.

## Cause

`_media_group_applies` (`simple_web_html_layout_renderer_core_css_rules.spl:460`)
evaluates only the parenthesised feature terms of a comma group. A group with
no `(` -- a bare media type such as `print`, `speech`, or `screen` -- leaves
`ok = true`, so every media type matches. `not` is not evaluated either; it
happens to give the right answer for `not print` only because `print` itself
is (wrongly) ignored. The rule scan calls this at line 980 for every
`@media` wrapper.

Media Queries 4 section 2.3: a media type that does not match the device
(`print` on a screen) makes its query false.

## Test status

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_renderer_media_query_and_alpha_spec.spl`
asserts the width-feature and unknown-feature rows; the bare `print` row is
kept out until fixed.

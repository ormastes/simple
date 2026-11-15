# Selector matching: a `:` inside an attribute value kills the selector, `[a^=""]` matches, `*.a` never matches (2026-11-15)

Status: OPEN. Severity: medium for Simple web styling (`a[href^="http:"]`,
`a[href^="https:"]` and `*.class` are common in real stylesheets).

## Defects

All three are in `browser_engine/simple_web_html_layout_renderer_core_selectors.spl`.

1. **Colon inside an attribute value.** `parse_selector_part` cuts the
   compound at the first `:` (`val colon = text_index_of(base, ":")`) before
   it looks for `[...]` groups, so `div[data-v^="http:"]` is cut to
   `div[data-v^="http`, the `]` is then missing and the part is returned dead.
   The colon search has to skip bracketed (and quoted) text.
2. **Empty operand for `^=` / `$=` / `*=`.** Selectors 4 section 6.3.2: when
   the value is the empty string these selectors represent nothing. The
   matcher returns `actual.len() > 0 and actual.starts_with("")`, which is true
   for any non-empty attribute (the `~=` branch already rejects an empty
   operand).
3. **Universal type with a class.** `*.a` takes the tag branch with
   `want_tag = "*"`, which no element has. `*` (alone) and `.a` both work.

## Repro (seed `~/.cache/cargo-target-webrender-vk/release/simple`, built 2026-11-14, interpreter)

Page: `body{margin:0} section,div,p,span,b,i,h1{display:block;width:10px;height:4px;margin:0;padding:0;border:0} <selector>{width:77px}`;
`simple_web_layout_debug_layout_by_id(page, 900, 2000, "t", "w")`. Chrome
159.0.8154.6 headless shell, same page, `getBoundingClientRect().width`.

| selector | body | Chrome | actual |
|---|---|---:|---:|
| `div[data-v^="http:"]` | `<div id="t" data-v="http://e"></div>` | 77 | 10 |
| `[data-v^=""]` | `<div id="t" data-v="abc"></div>` | 10 | 77 |
| `*.a` | `<div id="t" class="a"></div>` | 77 | 10 |

## Test status

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/layout_renderer_selector_matching_chrome159_spec.spl`
asserts the 58 rows of the same table where the renderer agrees with Chrome;
these three rows are kept out until the fixes land.

Re-verified still OPEN 2026-11-15 at `ba2663afde6` (after the upstream border/abspos/whitespace fixes): every row above reproduces unchanged.

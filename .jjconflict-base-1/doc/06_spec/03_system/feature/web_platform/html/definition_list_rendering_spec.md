# Definition List Rendering

Status: **DRAFT / EVIDENCE-BLOCKED**

This is a handwritten mirror of the executable scenario. No admitted
current-source pure-Simple docgen has generated or validated it, so it is not
runtime evidence.

## Purpose

This bounded manual traces `dl`, `dt`, and `dd` through semantic tree repair,
selected user-agent defaults, authored CSS, Web layout, Draw IR, and Engine2D.
It covers `REQ-WEB-BROWSER-002`, `003`, `004`, and `021`.

## Selected profile

| Element | User-agent behavior |
|---|---|
| `dl` | block with 16 px block-start and block-end margins |
| `dt` | block |
| `dd` | block with 40 px left indentation in the selected horizontal LTR profile |

Authored declarations apply after these defaults and may override them.

## Scenario

### Trace definition-list semantics and styles to exact pixels

1. **Parse omitted dt and dd end tags as definition-list siblings**

   The omitted-end-tag fixture must retain three sibling children under one
   `dl`: `dt`, `dd`, then `dt`. A cross-kind item nested under the previous
   item is a tree-builder failure.

2. **Apply definition-list user-agent defaults before authored CSS**

   The unstyled fixture must receive the selected profile above. The authored
   fixture must then override both `dl` block margins to zero and the `dd`
   indentation to 16 px.

3. **Lower authored definition-list boxes to exact Draw IR geometry**

   Web hit-index boxes and Draw IR commands must agree on:

   - `dl`: `[4,4,64,24]`
   - `dt`: `[4,4,24,8]`
   - `dd`: `[20,12,32,8]`

   Draw IR computed styles must retain the exact `dl`, `dt`, and `dd` tags and
   the authored 16 px `dd` margin.

4. **Rasterize exact definition-list pixels against a plain control**

   The styled component must produce blue at `(5,5)`, green at `(21,13)`, and
   pale red at `(60,25)`. Corresponding pixels in the same-geometry plain
   control at `(5,37)`, `(21,45)`, and `(60,57)` must remain white. Any skipped
   Draw IR command or buffer other than `96 × 64` fails the scenario.

## Evidence boundary

The implementation and assertions use only the canonical Web-to-DrawIR and
Engine2D owners. This draft claims no qualified execution, generated-manual
provenance, WPT corpus pass, or full WHATWG definition-list conformance.
Runtime remains HELD until a current-source pure-Simple receipt is admitted.

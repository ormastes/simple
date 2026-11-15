# Web renderer vs Chrome 159 lane — review residue (2026-11-14)

Found by the pre-landing review of `work/webrender-chrome-20261114`. None
blocks the lane; each is a real defect or gap left open. Paths are under
`src/lib/gc_async_mut/gpu/browser_engine/` unless shown otherwise.

| # | Where | Defect | Failing scenario |
|---|-------|--------|------------------|
| 1 | `simple_web_html_layout_renderer_layout_foundation.spl` `form_control_label_width_px` | The cascade carries integer px, so an AUTHORED `font-size:13px` control is indistinguishable from the UA `13.3333px` and is measured at 13.3333 | `<button style="font-size:13px">Exercise controls</button>` is about 2 px too wide |
| 2 | `simple_web_html_layout_renderer_paint_layout.spl` `<ol>` ordinal | Rescans the list's nodes for every `<li>` | O(n^2) Draw IR emission on a long list |
| 3 | `simple_web_html_layout_renderer_paint_layout.spl` effect bounds | Reads raw `text_decoration_thickness_px`, now 0 for `auto` | Font-derived underline (4 px at 48 px) is outside the node's effect bounds |
| 4 | `simple_web_html_layout_renderer_layout_foundation.spl` `absolute_outer_width` | `left_px > 0` is the "left is set" test; negative `left` now keeps its sign | `left:-5px; right:0` does not stretch |
| 5 | `scripts/check/web_combo_matrix_baseline.txt` | Unsuffixed, but values depend on the Linux face set | A macOS run reports new and stale ids |
| 6 | `simple_web_html_layout_renderer_core.spl` UA input border | `border:2px` applied to every `<input>` type | range / file / image / color inputs get a text-field border |
| 7 | list markers | disc or decimal painted for every `list-style-type` | `list-style-type:square` paints a disc |
| 8 | `check-chrome-catalog-pixel-diff.shs` | Playwright directory chosen lexically | `chromium-999` would beat `chromium-1255` |
| 9 | form-control specs | No Chrome measurement on the macOS (Helvetica) face set | Face-dependent widths are asserted on Linux only |
| 10 | RTL | `direction:rtl` reverses Latin text; Chrome 159 keeps `ABC` and right-aligns it | needs real bidi |
| 11 | `<code>` half-leading | Chrome 159 puts `<code>` text at +4; `inline_text_half_leading_spec` AC-4 pins +2 | |

Open clusters in the combination matrix (241 of 849 cells mismatch) are listed
in `doc/00_llm_process/feature_expert/web_render_css_parity/skill.md`.

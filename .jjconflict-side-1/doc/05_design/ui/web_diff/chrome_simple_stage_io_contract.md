# Chrome ↔ Simple component-level I/O contract (stages 1–2)

Status: implemented and measured 2026-08-08 against **Google Chrome for Testing
151.0.7922.34**.

This is a *per-stage* differential, not a whole-page screenshot compare. Both
engines get the same fixture file; each stage's intermediate artifact is
extracted from both sides, normalized, and diffed node-by-node,
property-by-property.

Harness: `tools/web_diff/` — `run_web_diff.shs` (driver), `chrome_extract.js`
(CDP), `simple_extract.spl` (Simple), `normalize_diff.js` (normalize + diff),
`summarize.js` (aggregate). Spec:
`test/system/web_engine_chrome_component_differential_spec.spl`.

---

## Stage 1 — HTML parse → DOM tree

| | Chrome | Simple |
|---|---|---|
| **Input** | `file://` URL of the fixture `.html` | same file, read as `text` |
| **Entry point** | CDP `DOMSnapshot.captureSnapshot` after `load` | `html_tree_builder_build(html) -> BeDomNode` |
| **Output artifact** | flat arrays: `nodeName`, `nodeValue`, `nodeType`, `parentIndex`, `attributes` (string-table indices) | `BeDomNode` tree: `tag_name`, `data`, `attributes: Dict<text,text>`, `children` |
| **Normalized form** | `{index, parent, name, text, attrs}` in pre-order | identical shape |

## Stage 2 — CSS parse + cascade → computed style per node

| | Chrome | Simple |
|---|---|---|
| **Input** | the same document, after style resolution | `process_style_blocks(root, html) -> BeDomNode` |
| **Output artifact** | `documents[0].layout.styles[i][p]` for the explicitly requested property list, joined to DOM nodes via `layout.nodeIndex` | `node.style: StyleProps` (a fixed 29-field struct) |
| **Property set** | requested explicitly, not "all ~340" | whatever `StyleProps` can hold |

The property set is deliberately the intersection: `display, position, width,
height, margin-*, padding-*, color, background-color, font-size, font-weight,
font-family, text-align, border-width/color/style, flex-direction, flex-grow,
top, left, z-index, overflow, float, clear`.

**Only elements with a Chrome layout box are style-compared.** A node with no
layout box has no computed style to compare, so including it would inflate the
compared-property count without comparing anything.

---

## Normalization rules

Normalization is where a differential silently stops finding bugs. Each rule
below is narrow on purpose, and each one states what it would hide.

| # | Rule | Why | What it hides |
|---|---|---|---|
| **N1** | Tag names lower-cased | Per DOM, HTML elements report an upper-case `tagName`; Chrome's snapshot honors that, Simple stores lower-case. Case is not a rendering behavior. | Nothing — case is unobservable in rendering. |
| **N2** | Chrome DOCTYPE nodes (`nodeType 10`) dropped | Simple's tree builder never materializes a doctype node; it carries no style and no content. Dropping on the Chrome side is preferred to fabricating one on the Simple side. | A future "Simple invents a doctype node" bug. Accepted. |
| **N2b** | Chrome pseudo-element entries (`::marker`, `::before`, `::after`) dropped | They are not DOM nodes and no DOM API reaches them. Their absence in Simple is a *style* gap, already reported by the `display` comparison (`list-item` vs `<empty>`). | Nothing structural. |
| **N3** | Whitespace-only text nodes kept, but flagged `wsOnly` in the report | Engines legitimately differ on retention. Dropping them silently would erase a real divergence; keeping them unflagged would drown the report. | Nothing — they are reported, just labelled. |
| **N4** | Text content: runs of ` \t\r\n\f` collapsed to one space, then trimmed | This is the `white-space: normal` collapsing both engines must perform for rendering. Raw source whitespace would be pure noise. | Divergence in *how* whitespace is preserved under `white-space: pre`. Out of scope for these fixtures. |
| | **NBSP (U+00A0) is deliberately NOT collapsed** | It is a distinct character; entity-decoding differences must remain visible. | — |
| **N5** | Colors canonicalized to `rgba(r,g,b,a.aaa)` | Chrome emits `rgb(0, 0, 0)`; Simple emits the author's source spelling (`red`, `#f00`). Without this, every color reports divergent for a purely syntactic reason. | — |
| | **Unrecognized color strings pass through as `raw:<text>`, never defaulted to black** | Mapping an unparsed color to a default would convert "Simple failed to parse this color" into a false pass. | — |
| **N6** | Lengths reduced to a px float, **ε = 0.05px** | Chrome reports used px; Simple stores an f64 already in px. 0.05px is below Chrome's own 1/64px (0.0156px) layout quantization *scale* but far below any real cascade error. | Sub-0.05px rounding differences only. A wrong cascade result is never that small. |
| | `auto` / `none` / `normal` kept as distinct tokens, not coerced to 0 | Simple uses `0.0` as its "unset" sentinel; equating `0` with `auto` would hide the fact that Simple has no `auto`. | — |
| **N7** | `font-weight`: `bold`→`700`, `normal`→`400` | Per CSS Fonts these ARE the same computed value. Chrome reports numerals, Simple keywords. | Nothing — this is a true identity. |
| **N8** | `font-family`: quotes stripped, items trimmed, lower-cased, **order preserved** | Quoting is syntax; list order and identity are semantics. | — |
| **N9** | Keywords lower-cased and inner whitespace collapsed. **Empty string becomes the distinct token `<empty>`** | An unpopulated Simple property must never be confused with Chrome's initial value. | — |
| **N10** | Simple `border-width/color/style` compared against Chrome `border-top-*` | Simple's `StyleProps` has no per-side border fields. | **Per-side border divergence is undetectable.** Stated, not papered over. |
| **N11** | Attributes compared as an order-independent map, names lower-cased, **values verbatim** | HTML attribute names are ASCII-case-insensitive; values are not. Attribute order is not observable via any DOM API. | Attribute source order. Correctly ignored. |

### Alignment key

Nodes are aligned by a **structural path**, e.g.
`#document/html[1]/body[1]/p[2]`, built from lower-cased tag names with a
per-parent occurrence index. Index-based alignment would be useless: a single
extra or missing node shifts every subsequent index and turns one defect into N
false ones. Nodes present on only one side are reported in `onlyInChrome` /
`onlyInSimple` rather than compared.

### Fail-closed contract

* `run_web_diff.shs` exits **3** with `WEB_DIFF_UNAVAILABLE reason=…` when
  chrome is absent, not executable, `bin/simple` is missing, or no fixture
  matched. It never exits 0 in those cases.
* `normalize_diff.js` exits non-zero when either side has zero nodes, when
  **zero DOM nodes** were compared, or when **zero style properties** were
  compared — regardless of the finding count.
* `summarize.js` exits non-zero when there are no reports or when the totals
  are zero.
* Every report carries `domComparedNodes` and `styleComparedProps` on its face,
  so "0 mismatches" can always be distinguished from "0 comparisons".

**Sabotage proof (2026-08-08).** With `WEB_DIFF_CHROME=/nonexistent/chrome`:
the runner prints `WEB_DIFF_UNAVAILABLE reason=chrome-not-executable` and exits
**3**; no `SUMMARY` line is produced; the spec's `field_i64(SUMMARY_LINE,
"domNodesCompared")` returns **-1**, so `> 0` is false and scenarios 2–5 all
fail. Feeding the differ a zero-node side exits **1** with
`DIFF_ERROR chrome side has zero nodes`.

**Caveat on env-based sabotage.** The Simple test daemon *freezes environment
selectors*: `env -u WEB_DIFF_CHROME bin/simple test …` still sees the value
captured on the daemon's first invocation. Unsetting the variable is therefore
**not** a valid sabotage of this spec — it proves nothing about the spec. The
proof above sabotages the *path value passed to the subprocess* instead, which
the daemon cannot mask.

---

## Measured result (2026-08-08, Chrome 151.0.7922.34)

17 fixtures · **171 DOM nodes compared** · **2262 computed properties compared**
· 42 DOM findings · 982 style findings. Full table:
`tools/web_diff/out/SUMMARY.md`.

### Stage 1 — DOM divergences

| ID | Divergence | Fixture | Evidence |
|---|---|---|---|
| **D1** | **No implied `<tbody>`.** Chrome inserts `tbody` between `table` and `tr`; Simple attaches `tr` directly to `table`. Shifts the entire subtree path, so every descendant selector `table > tbody > tr` would miss. | 03, 07 | onlyChrome `…/table[1]/tbody[1]{,/tr[1],/td[1]}`; onlySimple `…/table[1]/tr[1]{,…}` |
| **D2** | **`<hr>` does not close an open `<p>`.** Chrome's in-body insertion mode closes the `p` and starts a sibling `p[2]`; Simple nests `hr` inside `p[1]`. | 04 | onlyChrome `#document/html[1]/body[1]/p[2]` |
| **D3** | **`<style>` element is absent from the DOM.** Its rules are consumed but neither the `style` element nor its text child appear in Simple's tree, so `document.querySelector('style')` / `.textContent` cannot work. | 08–14, 16, 17 (every fixture with a stylesheet) | onlyChrome `#document/html[1]/head[1]/style[1]` and its `#text[1]` |
| **D4** | **Character references produce separate sibling text nodes.** `A&amp;B&nbsp;&lt;C&gt;` becomes **7** text nodes `"A","&","B"," ","<","C",">"` instead of Chrome's single `"A&B <C>"`. Entity *decoding* is correct; text-node *coalescing* is not. | 15 | domFinding `kind:text chrome="A&B <C>" simple="A"` + 6 onlySimple `#text[2..7]` |
| **D5** | Extra whitespace-only text node retained in `body`. Minor; flagged not dropped. | 06 | onlySimple `…/body[1]/#text[3](ws)` |
| — | Attribute names/values, `<p>` auto-close (05), implied `html/head/body` (02), void elements (04) all **match Chrome exactly.** | 02, 04, 05, 15 | 0 findings |

### Stage 2 — cascade divergences

| ID | Divergence | Evidence |
|---|---|---|
| **C1 (root cause, biggest)** | **`BeDomNode.set_style` accepts only 9 properties** — `display, float, clear, overflow, position, color, background-color, font-weight, text-align` (`src/lib/gc_async_mut/gpu/browser_engine/dom.spl:406`). **Every other declaration is silently discarded**, with no error and no warning. All lengths, `font-size`, `font-family`, `margin-*`, `padding-*`, `border-*`, `width`, `height`, `top`, `left`, `z-index`, `flex-*` are dropped on the floor. | Fixture 16: `p{font-size:20px;width:111px;height:22px;background-color:#eee;text-align:right;font-weight:bold}` → Simple applies `background-color/text-align/font-weight` and drops `font-size/width/height`. `div{margin-top:33px;padding-left:44px;border-width:5px;border-style:solid;border-color:#f0f}` → Simple applies **nothing at all**. |
| **C2** | **The cascade ignores specificity entirely.** `apply_rules_to_node` (`style_block.spl:95`) walks rules in *source order*, last write wins. | Fixture 08: `<p id="i" class="c">` with `p{red} .c{green} #i{blue} p.c{purple}` → Chrome **blue** (id, 1-0-0); Simple **purple** (the last rule in the file). Same-specificity source order (fixture 17) is correct — it is only the specificity ranking that is missing. |
| **C3** | **The inline `style=` attribute loses to the stylesheet.** | Fixture 09: `<p id="t" style="color:green">` with `#t{color:red}` → Chrome **green**, Simple **red**. |
| **C4** | **No shorthand expansion.** `margin: 10px`, `padding: 1px 2px 3px 4px`, `border: 2px solid blue`, `margin: 5px 15px` produce **all zeros** in Simple. (Partly a consequence of C1, but the shorthand *parse* is missing independently.) | Fixture 10, all 4 margins / 4 paddings / border-width / border-style |
| **C5** | **No inheritance.** A child does not inherit `color`/`font-size`/`font-family` from its parent. | Fixture 13: `#parent{color:teal;font-size:24px}` → Chrome's `span` child computes `rgb(0,128,128)` / `24px`; Simple's child computes `""` / `16` (its own defaults). |
| **C6** | **No UA (default) stylesheet.** `display` is `""` for *every* element (Chrome: `block`/`inline`/`table`/`list-item`); `body` has no `8px` margin; `p` has no `16px` block margins; `strong` is not bold; `hr` has no `1px inset` border; `img` is not `overflow: clip`. This alone accounts for **~68 of the divergences per property column.** | Fixtures 01–07, 14 |
| **C7** | Simple's "unset" sentinel is ambiguous: `0.0` for lengths and `""` for keywords/colors. Chrome distinguishes `auto` (top/left/z-index/width), `transparent` (background-color) and an inherited `rgb(0,0,0)` (color). A cascade that *did* compute `width:0` would be indistinguishable from one that computed nothing. | `top/left/z-index`: Chrome `auto` vs Simple `0` on all 68 style nodes |
| **C8** | `text-align` initial value is `left`; Chrome's is `start` (direction-relative). | All 67 style nodes |
| **C9** | `font-family` initial value is `sans-serif`; Chrome's is `Times New Roman` (serif). | All 68 style nodes |
| — | **Correct today:** ID/class/tag selector *matching*, same-specificity source order, and colour parsing for `#rgb`, `#rrggbb`, `rgb()`, `rgba()`, and named colours including `rebeccapurple` — fixture 11 produced **zero** colour findings. | Fixture 11, 17 |

### Harness bug found on the Simple side

`text[i]` indexing and `text.len()` disagree on multi-byte input: escaping a
string containing U+00A0 aborted with
`string index out of bounds: index is 1 but length is 1 (preview="\u{a0}")`.
Worked around in `simple_extract.spl` by iterating `for c in s:` instead of by
index. This is a language/runtime defect, not a renderer defect, and is
recorded here because it will bite anyone doing byte-wise text work.

---

## Running it

```bash
WEB_DIFF_CHROME=/path/to/chrome sh tools/web_diff/run_web_diff.shs
# reports land in tools/web_diff/out/, aggregate in out/SUMMARY.md
```

Chrome discovery is **not** automatic on purpose: the repo's existing helpers
probe only `/usr/bin/google-chrome`-style paths and `$HOME/.cache/ms-playwright`,
and silently find nothing on a machine where Chrome lives elsewhere. Requiring
an explicit path turns that silent miss into an explicit `WEB_DIFF_UNAVAILABLE`.

## Next steps (breadth, not yet done)

`test/fixtures/famous_site_corpus/` (133 real sites) is the intended breadth
corpus once the isolated fixtures above stop finding first-order defects.
Running it before C1–C6 are fixed would produce noise, not signal.

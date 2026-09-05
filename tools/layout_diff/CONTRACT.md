# Chrome ↔ Simple layout differential — I/O contract

Component-level, per-stage differential. Both engines get the **same** HTML file
and the **same** viewport; the **same** intermediate artifact is extracted from
each and diffed numerically. This is deliberately not a screenshot comparison —
a screenshot conflates layout, paint, rasterization and font hinting into one
signal that cannot localize a defect.

Chrome under measurement: **Google Chrome for Testing 151.0.7922.34**, headless,
viewport **800×600**, `deviceScaleFactor: 1`, `--force-device-scale-factor=1`,
`--disable-lcd-text`, `--font-render-hinting=none`.

---

## Stage 3 — layout → box geometry

| | Chrome | Simple |
|---|---|---|
| **Input** | `file://` URL of the fixture, fixed viewport | same fixture text via `read_file` |
| **Producer** | `DOMSnapshot.captureSnapshot({includeTextBoxes:true})` | `parse_html` → `extract_css_vw` → `build_child_index` → `compute_styles` → `layout` |
| **Output** | `documents[0].layout.bounds[i] = [x, y, w, h]` | `LayoutResult.bx/by/bw/bh : [i32]`, indexed by node index |
| **Box edge** | **border box** | **border box** (`bx/by/bw/bh` are the outer box; padding/border are folded in by `layout`) |
| **Origin** | document origin, top-left, css px, **unscrolled** | document origin, top-left, css px |
| **Margins** | *not* included in `bounds`; collapsing already applied to `y` | *not* included; collapsing already applied to `by` |
| **Precision** | Blink's `LayoutUnit` = **1/64 px** (0.015625), exposed as a float | **integer css px** — Simple has no subpixel layout at all |

Extractors: `chrome_layout_dump.js`, `simple_layout_dump.spl`.
Differ: `layout_diff.js`. Driver: `run_layout_diff.shs`.

### Normalization rules (stage 3)

1. **Epsilon = 0.5 css px** (`EPS_GEOM` in `layout_diff.js`). Justification:
   Simple's layout is integer css px end-to-end, so the *smallest* divergence it
   can express is 1 px, and any Chrome value is at most 0.5 px from its own
   correct rounding. 0.5 is therefore the tightest threshold that cannot
   manufacture a failure out of pure integer quantization. It is deliberately
   **32× coarser than Chrome's own LayoutUnit** — that coarseness is a statement
   about Simple, not about the oracle. Tighten it the day Simple gains subpixel
   layout.
2. **Margins are never compared as geometry.** Both sides report a
   margin-excluded border box, and collapsing is already resolved into `y`. The
   margin-collapse fixture is therefore tested through the *resulting* `y`
   offsets, which is the observable, not through a margin field. (Simple's
   resolved `margin_t`/`margin_b` are dumped alongside for debugging only.)
3. **`#document` / `#root` is excluded from geometry.** Chrome's `#document`
   layout node reports the **viewport** rect (always 800×600 here); Simple's
   `#root` reports the **document extent**. Comparing them is a category error.
   The node is still *paired* — its disappearance is a failure — but its
   geometry is recorded as `INFO_ROOT_EXTENT`, not as a delta.
4. **Non-rendered subtrees are dropped on both sides before pairing**:
   `head`, `meta`, `style`, `script`, `title`, `link`, `base`, and their
   descendants. Chrome omits them from the layout tree; Simple keeps them in the
   node arena. Dropping them on both sides keeps sibling ordinals aligned.
5. **Whitespace-only text nodes are dropped on both sides.** Chrome does not
   create a layout node for them; Simple does. This is the only class of
   "anonymous / whitespace box" the fixtures produce, and it is removed
   symmetrically rather than skipped asymmetrically.

---

## Stage 4 — text shaping / line breaking → line boxes

| | Chrome | Simple |
|---|---|---|
| **Input** | text node content + containing block width + resolved font | same |
| **Output** | `documents[0].textBoxes`: `layoutIndex[]`, `bounds[] = [x,y,w,h]`, `start[]`, `length[]` — one entry **per inline fragment** | `LayoutResult.wrap_starts[node][line]` / `wrap_ends[node][line]` — one entry **per line**, as offsets, **no rect** |
| **Offset space** | UTF-16 code units into the layout text | **UTF-8 byte offsets** into `HNode.text_data` |

### Normalization rules (stage 4)

6. **Chrome fragments are grouped into lines by `y`** (quarter-px buckets),
   sorted by `x`, and concatenated. A single visual line in Chrome can carry
   several `textBoxes` (a collapsed whitespace run, a source newline, a font or
   bidi run boundary). Without this grouping the `08_whitespace` fixture reads
   as a 2-vs-1 line-count divergence that does not exist. Simple already emits
   one entry per line, so grouping puts both sides in the same unit.
7. **Break positions are compared as TEXT, not as indices.** The two engines
   index different spaces (UTF-16 vs UTF-8 bytes — the CJK fixture yields
   `0..15 / 15..60` from Simple for a 20-character string). Each side's line is
   resolved back to its substring, and the substrings are compared after
   `\s+ → " "` collapse and trim. That isolates *where the break landed*, which
   is what the line breaker is responsible for, from whitespace-retention
   bookkeeping, which it is not.
8. **Per-line rects are not compared.** Simple emits no per-line rect, so
   line-height and per-line `x` (text-align) are unobservable at this stage.
   Chrome's line advance is recorded as `INFO_LINE_ADVANCE` for reference, and
   line-height is instead observed indirectly through the text node's union box
   height. **This is a capability gap in Simple, recorded rather than papered
   over.**

---

## Node correspondence (the hard part)

Both trees are keyed with the **same** two-rule function, applied after the
symmetric drops above:

1. An element with an `id` attribute keys as **`#<id>`**. Every fixture gives
   its elements ids, so this is the primary pairing and it is immune to tree
   shape differences.
2. Everything else keys as **`<parentKey>/<tag>[<ordinal>]`**, where `parentKey`
   is the key of the nearest **retained** ancestor and `ordinal` counts
   preceding retained siblings with the same normalized tag. This covers text
   nodes and any implicit/anonymous box. `#document` is normalized to `#root`
   and tag names are lowercased.

**Unpairable nodes are a reported FAILURE, never a silent skip.** A key present
only in Chrome emits `UNPAIRED_CHROME_ONLY`; only in Simple,
`UNPAIRED_SIMPLE_ONLY`; a fixture missing from one side entirely,
`FIXTURE_MISSING`. All three sort to the top of the worst-first table with
delta `INF`. Current status: **0 unpaired across 18 fixtures / 96 node pairs.**

## Vacuity guards

`layout_diff.js` exits **3** if it compared 0 nodes, `run_layout_diff.shs` exits
**4** if no Chrome executable was found, and the SSpec
`test/03_system/browser_engine/chrome_layout_differential_spec.spl` asserts
`nodes_compared > 0` **and** `text_nodes_compared > 0` **and** that the retained
chrome JSON carries a real `Chrome/<version>` string, before it evaluates any
delta. A "0 mismatches" report over 0 items is a failure here, not a pass.

## Running it

```sh
sh tools/layout_diff/run_layout_diff.shs --chrome /path/to/chrome     # ~4 min
bin/simple test test/03_system/browser_engine/chrome_layout_differential_spec.spl
```

Note: the repo's other chrome-locating checkers search only
`/usr/bin/google-chrome` and `$HOME/.cache/ms-playwright`; pass `--chrome` or
set `LAYOUT_DIFF_CHROME` for a chromium outside `$HOME`.

## Known extractor-side defect surfaced while building this

`simple_layout_dump.spl` must escape JSON with `text.replace`, not a
character loop: **`text.len()` returns the BYTE length while `text[i]` indexes
by CHARACTER**, so a `while i < s.len(): s[i]` loop walks off the end of any
non-ASCII string — `string index out of bounds: index is 20 but length is 20`
on the 20-character / 60-byte CJK fixture. See the comment at
`tools/layout_diff/simple_layout_dump.spl`.

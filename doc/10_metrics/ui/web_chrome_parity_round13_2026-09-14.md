# Chrome ↔ pure-Simple web parity — round 13 (2026-09-14, macOS)

Host macOS (Darwin 25.5.0), binary `build/cargo-r2/release/simple`, differ
`src/app/ui/chrome_showcase/layout_geometry_diff.spl` at `900x20000`, one tree,
one binary and one Chrome harvest for both sides, in a single detached
worktree on `origin/main` @ `a7c3570d64f`.

**Read the first section before using any number from rounds 11, 12 or 13.**

## The headline: the differ could report a page it had never laid out

Round 13 was tasked with "one spurious box on the Simple side desynchronises
every later nth-path key". That premise is **false**, and the real defect is
larger and in the other direction.

### The spurious box is `path:(body)`, and it is benign

Every page — including `overview`, which has 18 compared elements and 5 honest
mismatches with every neighbour exact — reports:

```
- missing in Simple: 0
- missing in Chrome (Simple-only boxes): 1
  - path:(body)
```

Simple emits a box for `<body>` (key `path:`); Chrome's `--dump-dom` harvest
carries no `|body|` row (`grep -c '^GEOM|path:|' html.geom.txt` = 0).
`geometry_diff` matches by KEY STRING (`_find_key`), not by position, so an
extra box on one side cannot shift any other key. It moves zero mismatch
counts. Nothing was changed for it; it is recorded here so round 14 does not
spend a round on it.

### What WAS inflating html and css-paint: a STALE RUNNER BINARY

`build/cargo-r2/release/simple`, the runner every recent round used, was built
**Sep 12 16:57**. Commit `08770cc5025` (**Sep 14 00:32**) added the extern
`rt_engine2d_blend_cov_span_u32` — its declaration in
`simple_web_html_layout_renderer_paint_primitives.spl` AND its registration in
`interpreter_extern/simd.rs`, in the same commit. A binary two days older loads
a layout module declaring a symbol it cannot resolve; an unregistered extern
answers **silent nil**, and the renderer then emits every box as `(0,0,0,0)`.

| tree | zero boxes / total on `html` |
|---|---|
| `9290752171d` (before `08770cc5025`) | **0 / 432** — real geometry |
| `a7c3570d64f` (after) | **432 / 432**, on every repetition |

Env was **ruled out, not ruled in**: the counts are identical with and without
`SIMPLE_EXECUTION_MODE=interpreter` / `SIMPLE_TIMEOUT_SECONDS=0`, which is what
you expect — no mode makes an interpreter know a symbol it was not built with.
(An intermediate draft of this round blamed those vars; it was comparing two
different TREES, not two different modes. Recorded so the wrong lesson is not
carried forward.)

Every KEY is still emitted, so `missing_in_simple` is 0 and nothing looks
structurally wrong; each row's delta is then **Chrome's own `(x, y, w, h)`
verbatim**, because it is being subtracted from zero. Run correctly (on
`9290752171d`) over the same archived Chrome harvest, the same differ reports:

```
chrome_boxes=431  simple_boxes=432  compared=431  mismatched=329
root mismatches:  main dh=56 | section dy=1,dh=55 | ul dy=1,dh=54 | b dw=4
```

Ordinary small deltas, not 430 rows of Chrome's geometry. **There was never a
layout regression to bisect**, and round 12's "host/Chrome variance" (html 338
at round 11 vs 430 at round 12) is the same artifact.

### Fixed: the measurement lane fails closed

`all_boxes_degenerate(boxes)` in the differ refuses to diff an all-zero Simple
side, printing `ERROR — nothing was checked (every Simple box is 0x0 at 0,0 for
<page>; the page was not laid out …)`. Two boxes minimum, so a genuinely
single-element zero-sized page is not mis-flagged. A fifth fatal selftest
fixture covers both halves (degenerate caught; a real side that merely
*contains* a zero box kept), so `--selftest` now reports
`PASS — 5 fixture(s) checked, 0 failed`. **Proven live on first contact:**
against `a7c3570d64f` with the stale binary it returns that ERROR in 13 s
instead of a 430-row table. The harness additionally pins the two env vars —
not as a fix for this, but so an unpinned lane stops producing rounds of
numbers that are not comparable with each other.

**Consequence for the record:** the per-page totals in rounds 11-13 for `html`,
`css-paint`, `css-layout`, `forms-media` and `animation` are not attributable
and should not be cited. `overview` is small enough that it was laid out either
way and its numbers stand.

## Kerning on the unmanaged lane (task item 1)

### The probe answer

`horizontal_kern` returned 0 not because `kern` is unparsed *badly* but because
**it is never read at all**. `FontRasterizer.load_unmanaged`
(`src/lib/nogc_sync_mut/sffi/spl_fonts.spl:280`) builds the rasterizer with
`kern_fp: 0`; there is no dylib behind that lane, so `horizontal_kern` (:624)
short-circuits to 0 for every pair of every macOS system face. Chrome kerns by
default (`font-kerning: auto` → `normal` for horizontal text), so every
Helvetica run carrying a kern pair measured **wider** here than in Chrome.

`sfnt_ttc_extract_face` copies every table verbatim when it repacks a
collection face, so the data was in `selected_blob` the whole time.

### What the faces actually ship, measured

Probed through `parse_offset_table`/`find_table` on the repacked face blob:

| face | `kern` | `GPOS` | `AV` | `To` | `on` |
|---|---|---|---|---|---|
| `Helvetica.ttc#0` | 656 B, version `0x00010000` (Apple), 1 subtable, coverage `0x0000` (horizontal, format 0), **105 pairs** | absent | -151 units = **-1180** milli-px @16 | -227 = **-1773** | 0 |
| `Menlo.ttc#0` | absent | absent | 0 | 0 | 0 |

So **legacy `kern` is the whole of what Chrome can be applying on these faces**,
and GPOS `PairPos` is deliberately NOT implemented — it would be dead code on
every face this renderer loads. A face that kerns only through GPOS answers 0
from here, exactly as it did before.

### Implementation

`src/lib/common/encoding/sfnt_kern.spl` (new):
`sfnt_blob_kern_pair_units`, `sfnt_units_per_em`,
`sfnt_blob_kern_pair_milli_px`. Both `kern` header shapes are read — Apple
`0x00010000` (u32 nTables; subtable header u32 length, u16 coverage with the
format in the LOW byte, u16 tupleIndex) and MS `0x0000` (u16/u16; subtable
header u16 version, u16 length, u16 coverage with the format in the HIGH byte)
— because they are trivially distinguished and a Windows-built face on another
host would otherwise silently fall back to zero. Only horizontal,
non-cross-stream, non-variation **format 0** subtables are applied; anything
else is skipped rather than guessed at. Pairs are binary-searched on the
32-bit `(left << 16) | right` key the spec requires them to be sorted by.

`font_renderer.spl` gains `horizontal_kern_milli`, which prefers the foreign
rasterizer when it answers non-zero — so **the managed lane keeps exactly the
number it produced before, widened ×1000, and cannot move** — and otherwise
reads the face's own `kern`. `measure_text_advances` calls it and folds the
value straight into round 12's milli-pixel cumulative; the kern square cache
now stores milli-pixels, and both of its readers are the four lines that
changed together.

**Milli-pixels, not pixels, and deliberately.** Helvetica's `AV` is -1.18 px at
16; rounded on its own that is -1, which would reintroduce exactly the per-item
rounding round 12 removed from advances. The rounding stays at the single
boundary-difference step.

### Measured through the live renderer

| measurement | before | after |
|---|---|---|
| `measure_text_width("AV", 16)` Helvetica | 21 | **20** |
| `measure_text_width("AA", 16)` (no pair) | 21 | 21 |
| `measure_text_width("To", 16)` | 18 | **17** |
| `measure_text_width("MMMMMMMM", 16)` Menlo | 77 | **77** (unchanged — no `kern` table) |

### Known limits, stated rather than hidden

- **ASCII only.** The glyph-id table (`_gid_lookup`) covers 32..126, so a
  non-ASCII pair gets no kern on this lane.
- **`render_text` still kerns at whole-pixel** through `horizontal_kern`. The
  milli-px path is `measure_text_advances`, which is what layout and
  `paint_layout_advance_parity` consume; that spec is **2/2 green**.
- **The 32 px value is not twice the 16 px value.** -151/2048 em is -1179.6875
  milli-px at 16 and -2359.375 at 32, so the rounded answers are -1180 and
  **-2359**. The dead lane's spec asserted `2 * -1180`; that expectation was
  corrected (doubling a rounded number carries the smaller size's rounding error
  into every larger one), and the spec now pins both the exact value and the
  ≤1 milli-px gap.

## Specs

- **New (adopted from the previous lane's uncommitted work, one expectation
  corrected):** `test/01_unit/browser_engine/kern_pair_advance_accumulation_spec.spl`
  **9/9**. Pins `AV` and `To` read out of the real table, 0 for an unlisted
  pair, per-size exact rounding, 0 for a face with no `kern` (Menlo — the
  regression half), a kerned run narrower than the sum of its parts, `AV` = 20,
  `measure_text_width` ≡ Σ `measure_text_advances`, and eight Menlo `M` still
  **77**.
- **Differ selftest:** `PASS — 5 fixture(s) checked, 0 failed` (fifth fixture
  new this round: the all-zero side).
- **Neighbours, both sides of the change, all GREEN:**
  `paint_layout_advance_parity` **2/2**, `fractional_advance_accumulation`
  11/11, `monospace_inline_line_box` 5/5,
  `inline_run_advance_and_break_boxes` 5/5,
  `font_family_generic_classification` 5/5,
  `inline_content_area_half_leading` 4/4, `platform_system_face_metrics` 25/25.

## Per-page geometry, A → B

A and B are the same tree, the same binary, the same Chrome harvest and the
**same differ** (the differ's degenerate guard is present on both sides; it
never fires under the corrected env, so it does not affect the comparison).
A is the tree with the two `src/lib` files stashed; B is A plus exactly those
two files.

| page | compared | A mismatched | B mismatched | delta |
|---|---|---|---|---|
| overview | 18 | 5 | 5 | 0 |
| html, css-layout, css-paint, forms-media, animation, evidence, tab-bar | — | **not measurable** | **not measurable** | — |

`overview` is the only page this session could measure, and the answer is
honest and negative: **kerning moved nothing on it**, the same five inline rows
with the same deltas before and after. That is consistent rather than
disappointing — the previous lane had already established that `strong`'s pairs
(`st`, `tr`, `ro`, `on`, `ng`) all kern ZERO in Helvetica Bold — and it is also
the regression half: a correct kern implementation must not move a line whose
pairs do not kern.

Every other page is **not measurable on this host right now**, because the
stale runner collapses them to all-zero and the differ now (correctly) refuses
to report. This is stated as a gap rather than filled with the pre-fix numbers,
which is what the previous three rounds did. Unblocking round 14 needs a runner
built from the tree it measures — see "What is left" below.

## What is left, in order

1. **`main` `dh = 56` on `html`** — the tallest block is 56 px taller in Simple
   than in Chrome, and `section`/`ul` inherit 55/54 of it. This is the largest
   single number on the page and is a block-flow height question, not a text
   one.
2. **`strong` `dw = 6` on `overview`** — still open, and now known NOT to be
   kerning: its pairs (`st`, `tr`, `ro`, `on`, `ng`) all kern **zero** in
   Helvetica Bold. Round 11 routes generic-family bold through the platform
   bold face; the residual is in that face's own advances or in the bold
   synthesis.
3. **`dy = 1` on every inline element of the overview line** — a baseline /
   half-leading offset, untouched by this round.
4. **Build a runner from the tree being measured.** This is now the top blocker:
   seven of eight pages cannot be measured at all on a binary older than the
   externs `src/lib` declares, and nothing in the lane rebuilds or version-checks
   it. Until that is fixed every parity number is one stale binary away from
   being an artifact.
5. **Silent-nil externs.** A declared-but-unregistered extern returning nil
   instead of failing is what turned a two-day-old binary into 430 fabricated
   mismatch rows —
   `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`.
6. **Partial collapse is still unguarded.** `all_boxes_degenerate` catches a
   total collapse; a page laid out down to element N with a zero tail would
   still be reported as a plausible mismatch table. Named, not fixed.

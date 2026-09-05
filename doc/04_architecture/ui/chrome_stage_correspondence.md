# Simple ↔ Chrome (Blink) Rendering Stage Correspondence and Comparison Contract

Status: evidence-driven. Every row states what was **measured in this tree**, not
what a plan doc asserts. Where a doc and the code disagreed, the code won and the
doc is corrected (see § Plan-doc corrections).

Scope note: this is the per-stage contract that
`doc/03_plan/platform/chrome_modern_web_platform_compat_plan.md` calls for. That
plan's success target is *conformance against selected suites*, not blanket
Chrome compatibility, and nothing here widens that target.

---

## 1. Stage correspondence

Blink's documented pipeline is: **parse → DOM → style recalc → layout →
prepaint → paint → composite/raster → present**.

Simple has **two disjoint stacks**, and conflating them is the single easiest way
to produce a meaningless comparison.

- **Stack A (reference/spec-shaped, NOT used for production rendering).**
  `html_tokenizer.spl` → `html_tree_builder.spl` → `dom.spl` (`BeDomNode` tree),
  plus simplified `layout.spl` / `paint.spl`. `html_tokenizer_tokenize` is
  referenced by exactly three files in `src/`; `paint.spl:127`
  `generate_paint_list` returns `[]` — a stub.
- **Stack B (the production pipeline)** runs on flat SoA arrays and **never
  builds a DOM tree or a box tree**. Driver:
  `_simple_web_layout_compose_document`
  (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:1659`).
  Its own `[web-phase]` traces name the phases: **parse → style_start/style_end →
  layout → compose_shaping → paint**.

The phase list "tokenize → dom → style → layout → paint → tiles → present" is
Stack A's vocabulary applied to Stack B. It does not describe the code that
renders.

| Blink stage | Simple production stage | Entry point | Output artifact | Correspondence |
|---|---|---|---|---|
| parse (tokenizer) | *(none)* | — | — | **NO CORRESPONDENCE.** `parse_html` (`..._foundation.spl:822`) goes text → `[HNode]` directly. There is no token stream on the production path, so there is nothing to compare against Blink's `HTMLTokenizer` output. |
| DOM tree | flat node array | `parse_html(html) -> [HNode]` (`..._foundation.spl:822`), `HNode` at `:296` | `[HNode]` with a `parent` index | **PARTIAL.** Reified but *not a tree*: no parent/child object graph, no `Node` identity, no live collections. Tree-shaped `BeDomNode` (`dom.spl:67`) exists only in Stack A. Structural comparison against a Blink DOM dump is possible in principle; the two are not the same data model. |
| style recalc | `compute_styles` | `compute_styles(nodes, rules, child_index, …) -> [Style]` (`..._core.spl:2522`); `Style` at `..._style.spl:7` | `[Style]`, one per node, eagerly resolved | **GOOD.** Both sides produce a fully-resolved computed value per element. This is the cleanest correspondence in the pipeline. |
| layout | `layout` / `layout_with_style` | `..._layout.spl:981`, `:1018` → `LayoutResult` (`:146`) | SoA geometry `{bx, by, bw, bh, wrap_starts, wrap_ends, intrinsic_widths, height}` | **PARTIAL.** Per-node x/y/w/h exists and is directly comparable to `getBoundingClientRect`. But there is **no fragment tree**: no fragmentation, no containing-block chain object, no `LayoutObject` identity. Blink concepts that need a fragment tree (fragmentainers, `LayoutNG` fragment reuse) have no counterpart. |
| prepaint (paint properties / transform-clip-effect trees) | *(none)* | — | — | **NO CORRESPONDENCE.** Simple has no property-tree stage. Clip/transform are folded into individual draw commands (`clip_present`, `clip_x/y/w/h` on `DrawIrCommand`). There is no separable artifact and no Blink-equivalent boundary. |
| paint (display list) | Draw IR composition | `_simple_web_layout_compose_retained` → `DrawIrComposition` of `DrawIrCommand` | **Reified display list**, serializer `draw_ir_to_sdn` (`src/lib/common/ui/draw_ir_sdn.spl:228`), differ `draw_ir_diff_compositions` (`.../draw_ir_diff.spl:251`) | **GOOD in shape, but see § 4 gap D.** Blink's `PaintArtifact`/`cc::DisplayItemList` is the analogue. Simple's command set is far smaller. |
| raster | `paint` / `paint_tiled` | `..._paint_layout.spl:648`, `:1301` | `[u32]` framebuffer | **FUSED — no intermediate.** `paint()` mutates the framebuffer in place. Blink's raster is a separable step over a display list; Simple's is not. |
| composite (layerization) | tile binning | `tile_bin_ops` / `tile_survivors` (`..._paint_tiles.spl:109,240`) | `TileBins` / `TileLaneFrame`; observables are `tile_checksums` + `tile_stats_*` | **WEAK.** Simple tiles for raster work-splitting. Blink composites for *scroll/animation independence* (`cc::Layer`, property trees). Same word, different purpose. A tile↔layer comparison would be a forced correspondence and is **not attempted**. |
| present | Engine2D present / readback | `present_layout_pixels_with_engine2d` (`simple_web_html_engine2d_presenter.spl:708`), `present_gpu_paint_readback` (`:392`), `webgpu_present` (`webgpu_context.spl:652`) | `Engine2DReadback` / final pixels | **GOOD.** Both sides yield a framebuffer. This is where the existing corpus PPM comparison lives. |

### Boundaries that genuinely do not correspond

Stated plainly, because a forced correspondence here would make every downstream
number meaningless:

1. **tokenize** — no token stream exists in production Simple. Not comparable.
2. **prepaint / property trees** — no such stage in Simple. Not comparable.
3. **composite** — Simple's tiles are a raster work-split, not compositor layers.
   Not comparable as layerization.
4. **raster as a separate step** — fused into paint. Only its *output* (pixels)
   is observable, never its input-to-output relation as a distinct stage.

---

## 2. Per-stage comparison contract

For each stage: input artifact, output artifact, equivalence relation, and the
**derivation** of every bound. No bound below is fitted to a measured number.

### 2.1 Style recalc

- **Input:** corpus HTML page (`test/fixtures/famous_site_corpus/<id>.html`) —
  identical bytes to both engines.
- **Chrome output artifact:** `getComputedStyle` values recorded in
  `test/09_baselines/famous_site_corpus/<id>/chrome_metrics.json` under
  `metrics.body.*` and `metrics.div.*` (`fontFamily`, `fontSize`, `lineHeight`,
  `color`, `backgroundColor`, `overflow`, `whiteSpace`, margins).
- **Simple output artifact:** the `computed_style` key/value list carried on the
  element's `DrawIrCommand`.
- **Equivalence: EXACT, after canonicalization.**
- **Derivation:** computed values for these properties are *specified* by CSS as
  discrete values (a colour is `rgb(r, g, b)` with integral 0–255 channels; a
  used `font-size` in these fixtures is an integral px count; `font-family` is a
  verbatim token list; `overflow`/`white-space` are keywords). None of them
  passes through a rasterizer, a font backend, or a floating-point accumulation.
  There is therefore **no source of legitimate divergence**, and any tolerance
  would only hide a real cascade bug. Canonicalization is limited to whitespace
  inside the `rgb(...)` form and the `px` suffix — representation, not value.
- **Deliberately excluded:** `lineHeight: "normal"` is a computed *keyword* in
  Chrome whose used value depends on font metrics. Comparing it exactly would
  compare a keyword to a number. It is reported but not gated.

### 2.2 Layout — element box geometry

- **Input:** same HTML.
- **Chrome artifact:** `metrics.div.rect` (`getBoundingClientRect`).
- **Simple artifact:** `DrawIrCommand.{x, y, width, height}` for the element.
- **Equivalence: EXACT integers.**
- **Derivation:** every corpus fixture is authored with integral px box metrics
  and no percentage or fractional sizing on the compared element (the div carries
  an explicit `width`/`height` in px). Chrome's returned rect is integral for
  exactly that reason — measured `x:8 y:8 width:120 height:40`. Block-box
  geometry under these constraints is fully determined by CSS 2.1 box rules with
  no font dependence. A tolerance here would be tolerance for a layout bug.

### 2.3 Layout — text line geometry (line breaking)

- **Chrome artifact:** `metrics.textLines[]` (`Range.getClientRects` per line) —
  line count, per-line text, per-line rect.
- **Simple artifact:** `LayoutResult.wrap_starts` / `wrap_ends` reduced to lines
  via `br_famous_site_corpus_layout_lines_sdn`.
- **Equivalence:**
  - line **count** and per-line **text**: **EXACT**.
  - line **width**: bounded, see 2.4.
- **Derivation for exactness of count/text:** given the same available width and
  the same per-character advances, the greedy line-breaking algorithm in CSS is
  deterministic and identical. Divergence in count or text is a break-opportunity
  or advance bug, never a rounding effect — *provided* the width bound in 2.4
  holds, because a width error large enough to move a break would first show up
  as a width violation.

### 2.4 Text advance width — DERIVED BOUND

Two Simple lanes exist and they are **different rasterizer families**. The bound
differs per lane and the lane must be pinned before comparing.

**Lane R (resolved / TTF-shaped)** — `resolved_text_range_width`
(`..._layout.spl:327`) sums `Style.resolved_font_advances[i]`, which are **i32**.

- Bound: `|W_simple − W_chrome| ≤ N / 2`, where `N` = character count of the run.
- Derivation: Simple stores each per-character advance as an integer. Chrome's
  advances are fractional (`104.0625` for a 13-character run). Rounding each of
  `N` per-character advances to the nearest integer admits at most `±0.5` error
  each; the sum of `N` such errors is bounded by `N/2`. This is a pure
  quantization bound — it follows from the storage type alone and would be the
  same number if the measurement had never been taken.
- Sanity (not the derivation): for `"Google search"`, `N=13` → bound `6.5px`;
  observed `105` vs `104.0625` = `0.94px`. Inside the bound with margin, which is
  what a correctly-derived bound should look like.

**Lane B (bitmap oracle)** — `text_advance(fs) = 5 · glyph_scale(fs)` with
`glyph_scale(fs) = max(1, fs/8)` (`..._paint_primitives.spl:18`), space advance
`= advance/2`. At `fs=16`: `glyph_scale = 2`, advance `= 10px`, space `= 5px`.

- Bound: **none against Chrome.** Lane B assigns every glyph the *same* advance.
  Chrome's font is proportional. The two cannot agree on width for any string
  whose glyphs differ in width, and no tolerance derived from first principles
  would be tighter than "as wide as the widest/narrowest glyph ratio", which is
  not a compatibility statement.
- **Contract instead: rasterizer-family pin + ink-coverage bound.** Assert the
  lane identity (`glyph_scale(16) == 2`, monospace-advance model) and bound
  *ink coverage* rather than geometry. This mirrors the already-retired
  byte-exactness bar for text raster; it is **not** reintroduced here.

### 2.5 Present (final pixels)

- **Chrome artifact:** `test/09_baselines/famous_site_corpus/<id>/chrome.ppm`.
- **Simple artifact:** rendered `[u32]` framebuffer.
- **Equivalence:** the existing corpus policy — `exact_pixels_required`,
  perceptual diff *diagnostic only*, tolerance acceptance **not** allowed
  (`acceptance_policy_flags` in every `report.production.sdn`).
- This contract does **not** relax that policy. Text-raster lanes remain governed
  by the family-pin + ink-coverage rule of 2.4, not by a pixel tolerance.

### 2.6 Stages with no contract

tokenize, prepaint, composite, and raster-as-a-step have **no comparison
contract**, because there is no Simple artifact and/or no corresponding Blink
boundary (§ 1). They are enumerated in § 4 rather than given a placeholder test.

---

## 3. Trust preconditions for any comparison run

A comparison is only meaningful if these hold; a harness that does not check them
can report green while measuring nothing.

1. **Named budget exhaustion.** The CPU oracle previously returned a blank page
   on budget exhaustion with no signal; `_web_budget_expired_at(site)` (added
   `40c540fa850`) makes every exit named. A diff taken against a
   budget-exhausted frame is not a comparison. Check for a named exhaustion site
   before trusting any pixel result.
2. **Comparisons-run receipts.** A gate that skips comparisons must not report
   green — the parity gate printed 8 SKIPs while reporting 17/17 before receipts
   were added (`5e7a3df65f4`). Any harness here states how many comparisons
   actually ran.
3. **Binary identity.** Evidence inherits the binary that produced it. A
   `bin/simple` that prints the bootstrap-seed warning banner produces
   *seed* evidence, not self-hosted evidence.
4. **Render warm-up.** See § 6.1 — the first Draw IR render in a process omits
   **all** element commands. Any harness whose measured render is the first one
   in its process is comparing against an empty display list.

---

## 4. Enumerated gaps — stages that could not be compared, and why

| # | Stage | Why not comparable | What would unblock it |
|---|---|---|---|
| A | tokenize | No token stream exists on Simple's production path (`parse_html` goes text → `[HNode]`). Not a missing test — a missing stage. | Either expose a token stream from `_parse_html_with_limits`, or declare Stack A the conformance surface and compare `html_tokenizer.spl` against a WHATWG `html5lib-tests` tokenizer corpus (offline, vendorable). |
| B | DOM | No Chrome DOM artifact has ever been captured for this corpus. `chrome_metrics.json` carries computed style and rects only — no node tree. | Capture `DOM.getDocument` / serialized `outerHTML` per fixture (see gap F: the capture tooling is missing). |
| C | prepaint | Simple has no property-tree stage. Nothing to compare. | Architectural, not a test gap. |
| D | paint / display list | Simple's Draw IR is reified and serializable (`draw_ir_to_sdn`), but **no Chrome display list has been captured**. Blink's `cc::DisplayItemList` is reachable only via tracing or `--enable-blink-features`, and Chrome is not installed here. | Capture a paint trace per fixture; define a normalized display-list schema both sides can be projected into. Cross-engine display lists are not naturally comparable command-for-command, so this needs a projection contract before it needs a test. |
| E | composite / tiles | Simple tiles for raster work-splitting; Blink composites for scroll/animation independence. Comparing them would be a forced correspondence. | Nothing — this should stay uncompared until Simple grows real compositor layers. |
| F | **all Chrome-side re-capture** | **No Chrome/Chromium binary is present on this machine** (`google-chrome`, `google-chrome-stable`, `chromium`, `chromium-browser`, `chrome-headless-shell` all absent; no Playwright browser cache). No new Chrome baseline of any kind can be produced here. | Run the capture on a machine with Chrome — but first restore the capture scripts, which are missing (§ 5). |

**No Chrome baseline in this work is hand-written.** Every Chrome value used
comes from an artifact already committed to the tree.

---

## 5. Plan-doc corrections (code wins)

1. **The Chrome capture tooling named by the corpus plan does not exist.**
   `doc/03_plan/ui/web_browser/simple_web_renderer_chrome_compat_corpus.md` (lines
   35, 37, 54, 56, 141) instructs the reader to run
   `tools/electron-shell/capture_famous_site_corpus_chrome.js` and
   `tools/electron-shell/measure_famous_site_corpus_chrome.js`.
   **Neither file is in the tree.** `tools/electron-shell/` contains only
   consumers (`summarize_*`, `calibrate_*`, `analyze_ppm_delta.js`,
   `generate_famous_site_glyph_atlas.js`). Consequence: **the 132 `chrome.ppm`
   and 132 `chrome_metrics.json` baselines are currently unreproducible.** They
   are trustworthy as artifacts (nothing in-tree synthesizes them, and the PPMs
   carry LCD-style subpixel fringing no Simple code path emits) but they cannot
   be regenerated or extended until the capture scripts are restored.
   The only in-tree Chrome capture path is `capture_chrome()`
   (`src/app/wm_compare/_HtmlCompat/capture_and_compare.spl:439`), which shells
   out to real Electron/Chromium and needs `DISPLAY`; it is reached for the
   corpus only under `--update-baseline`
   (`src/app/wm_compare/site_corpus_compat.spl:150-157`).

2. **The corpus is 132 samples, not "100+" loosely.** `manifest.sdn` plus 132
   `site_*.html` fixtures; 132 `chrome_metrics.json` sidecars; 134 baseline
   directories (the extra two are `glyph_atlas` and a legacy `site_0`).

3. **`site_0_google` and `site_15_twitch` have a fixture-oracle short-circuit.**
   `simple_web_render_html_to_pixels_with_corpus_fixtures`
   (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_corpus_fixture_renderer.spl:25-34`)
   returns **Chrome's own baseline PPM** as the "Simple" render for those two
   samples. Any pixel assertion routed through that function on those samples
   compares `chrome.ppm` to itself. See § 6.

---

## 6. Defects found while building this contract

### 6.1 Cold-render display-list dropout (REPRODUCED)

The **first** `render_html_to_draw_ir` call in a process returns a display list
containing only the root canvas rect. Every subsequent call on the *same input*
returns the full list. Measured, back-to-back, in one process on
`test/fixtures/famous_site_corpus/site_0_google.html` at 160×120:

```
RESULT call1=1     # commands
RESULT call2=5
RESULT call3=5
```

and through the corpus accessor `site_corpus_simple_div_box`:

```
RESULT cold  x=0 y=0 w=0 h=0 bg=[]
RESULT warm  x=8 y=8 w=120 h=40 bg=[rgb(37, 99, 235)]
```

The warm value matches Chrome's `getBoundingClientRect` exactly
(`x:8 y:8 width:120 height:40`, `backgroundColor: rgb(37, 99, 235)`). The cold
value is the all-zero fallback returned by
`src/app/wm_compare/site_corpus_layout_report.spl:222` when no `div`-tagged
command is present.

Correlated trace (`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:2321`):
first call reports `at=renderer-bound from_cache=false` and
`at=measure shaped_valid=false`; later calls report `from_cache=true`. The
first call pays a one-time default-face load (dlopen plus a ~17 MB TTF parse)
which is charged against the render budget armed by `_web_budget_begin`, so
layout trips its deadline and zeroes every subtree it did not reach.

Before this work the dropout was **silent** — no error, no warning, and a
well-formed composition that was simply empty of elements. With the Draw IR
degradation fields added here it is named. Same probe, after the change:

```
RESULT cold commands=1 decision=draw-ir:declined:compared=none:reason=budget-exhausted:layout-subtree
RESULT warm commands=5 decision=draw-ir:comparable:full-display-list:reason=budget-complete
```

The exhaustion site is `layout-subtree`, confirming the mechanism. The
underlying defect — that a cold process pays the font load out of the render
budget — **remains open**; what is fixed is that it can no longer be mistaken
for a successful render of an empty page, which is the property every per-stage
comparison depends on.

Scope caveat: measured on the **Rust bootstrap seed** binary (`bin/simple`
prints the seed banner). Whether the self-hosted binary shares the defect is
unverified here.

This dropout is **not** what makes the corpus examples fail under
`bin/simple test` — see § 6.2, which is a different and larger defect. The two
were easy to conflate: both produce a one-command composition. They were
separated by noting that the dropout reproduces under `bin/simple run` (where
the suite is green-by-absence) while the suite failure carries a *semantic*
error that `run` never emits.

### 6.2 Style cascade calls a function that does not exist (REPRODUCED)

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl`
called **`_web_budget_expired()`** — with no argument — at four sites:

| line | loop | correct site constant |
|---|---|---|
| 2568 | outer per-node style resolution | `WEB_BUDGET_SITE_STYLE_CASCADE` |
| 2644 | selector-group match | `WEB_BUDGET_SITE_STYLE_SELECTOR_GROUPS` |
| 2694 | candidate declaration apply | `WEB_BUDGET_SITE_STYLE_CANDIDATE_DECLS` |
| 2730 | important declaration apply | `WEB_BUDGET_SITE_STYLE_IMPORTANT_DECLS` |

**No such function exists.** The only definition is
`_web_budget_expired_at(site: text)`
(`..._foundation.spl:282`), whose own comment states the zero-argument form was
removed deliberately:

> `site` is mandatory by design. This deliberately has no zero-argument
> counterpart: an unattributed exit is how exhaustion became invisible in the
> first place, and a nameless guard would silently reintroduce it.

The commit that made exhaustion inspectable (`40c540fa850`) removed the
zero-argument variant but left these four style-cascade call sites un-migrated.
The four `WEB_BUDGET_SITE_STYLE_*` constants were defined for exactly these
sites and had **zero references** anywhere in the tree — a 1:1 match that
confirms the migration was intended and incomplete.

Why it went unnoticed: `bin/simple run` (JIT) resolves lazily, and these
branches only execute once a budget expires, so a normal render never touches
them. `bin/simple test` resolves eagerly during semantic analysis and fails
outright. The result is that **every Chrome per-stage comparison in
`structural_layout_report_spec.spl` was dead under the test runner**, reporting
a semantic error rather than any comparison result.

Verbatim verdict at `d4175df988c2cbd522759d3d6f40df552f2ad027`, before the fix:

```
  ✗ compares famous-site corpus div geometry against Chrome metrics
    semantic: function `_web_budget_expired` not found
11 examples, 4 failures
Results: 11 total, 7 passed, 4 failed
```

Fixed by pointing each site at its intended constant — landed as `341efaa3c73`
("name the four orphaned style-cascade budget guards"), reached independently
and byte-identically by a parallel session while this analysis was running. The
convergence is itself evidence the mapping was unambiguous. This is a
correctness fix, not a gate change: the guards now name their phase, exactly as
the design requires.

Verified after the fix, on an isolating spec that imports only the Draw IR
entry points:

```
  ✓ resolves the new draw ir gate
1 example, 0 failures
```

### 6.2 Fail-quiet fallback in the corpus accessor

`site_corpus_simple_div_box` returns a silent all-zero `StructuralLayoutBox` when
the display list contains no `div` command
(`src/app/wm_compare/site_corpus_layout_report.spl:206, 222`). The comparison
then reports an ordinary *geometry mismatch*, which is the wrong diagnosis: the
real condition is "Simple produced no artifact for this element". Today that
happens to fail loudly only because Chrome's box is non-zero; had Chrome's box
been absent or zero, a missing Simple artifact would have compared **equal** and
the example would have passed vacuously.

### 6.3 Known vacuous assertion (identified, not introduced here)

`test/03_system/gui/wm_compare/famous_site_corpus_spec.spl:883-888`
— *"keeps the normal system font corpus capture pixel-aligned with Chrome"* —
renders sample 0 through `simple_web_render_html_to_pixels_with_corpus_fixtures`,
which for `site_0_google` **loads `chrome.ppm` and returns it**, then asserts it
equals `chrome.ppm`. The assertion is `expect(chrome == chrome)` and is
structurally incapable of failing.

The adjacent example at `:890-904` is *not* vacuous: it deliberately contrasts
the fixture oracle against the production renderer and asserts the production
render **differs** from Chrome within bounded limits. The fixture short-circuit
therefore has a legitimate purpose (pinning the oracle lane); only the `:883`
example measures nothing.

---

## 7. What this lane built

1. **`SimpleWebLayoutDrawIrResult.render_degraded` / `.degrade_reason`**
   (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`).
   The Draw IR analogue of the pixel-path fields added in `40c540fa850`. That
   commit made budget exhaustion inspectable for the CPU pixel oracle; the Draw
   IR path — the artifact every per-stage comparison in §2.1–2.4 reads — was
   never given the same treatment, so a truncated display list was
   indistinguishable from a correct render of an empty page.
2. **`simple_web_layout_draw_ir_comparable(result)`** and
   **`simple_web_layout_draw_ir_compare_decision(result)`** — the exact
   analogues of `simple_web_layout_software_pixels_presentable` /
   `simple_web_layout_software_present_decision`. Every decline names the
   budget site that caused it.
3. **`SiteCorpusSimpleDiv` + `site_corpus_simple_div`**
   (`src/app/wm_compare/site_corpus_layout_report.spl`), carrying the div box
   together with `comparable` and `div_present`. `site_corpus_simple_div_box`
   keeps its old signature and behaviour and is now a thin accessor, so no
   existing caller changes.
4. **Receipts in `build_site_corpus_div_geometry_report`** —
   `simple_draw_ir_decision`, `simple_draw_ir_comparable`, `simple_div_present`,
   and `comparison_ran`, emitted *before* the geometry verdict.
5. **`test/03_system/gui/wm_compare/chrome_stage_comparison_receipts_spec.spl`**
   — the gate. Its degraded cases are produced deliberately by arming a 1 ms
   budget through `SIMPLE_WEB_RENDER_BUDGET_MS` (re-read by `_web_budget_begin`
   on every render), so the negative half of every receipt is exercised on
   purpose rather than waiting for a truncation to occur by chance.

### Evidence

Clean run of `chrome_stage_comparison_receipts_spec.spl`, verbatim:

```
  ✓ reports a comparable display list when the render completes
  ✓ declines to compare a budget-truncated display list and names the phase
  ✓ states comparison_ran: true only when the display list carried the div
  ✓ states comparison_ran: false when the render was truncated
  ✓ never presents an absent div as a real zero-sized box
  ✓ matches Chrome's recorded div geometry exactly when the render completes
  ✓ pins the Chrome baseline as a captured artifact, not a computed one
7 examples, 0 failures
Results: 7 total, 7 passed, 0 failed
```

**Sabotage verification.** Four independent perturbations were applied to a
copy of the tree, each targeting one comparison. Every targeted example failed
with its expected message and every untargeted example stayed green:

| perturbation | target example | observed failure |
|---|---|---|
| drop `+ result.degrade_reason` from the decline string | "declines … and names the phase" | `expected 55 to be greater than 55` |
| hardcode `ran_text = "true"` | "states comparison_ran: false …" | report showed `comparison_ran: true` under a truncated render |
| return `div_present: true` from the absent-div fallback | "never presents an absent div …" | `expected subject to be truthy, got ` |
| emit the div box at `command.x + 1` | "matches Chrome's recorded div geometry" | `expected 9 to equal 8` |

```
7 examples, 4 failures
Results: 7 total, 3 passed, 4 failed
```

The last row is the one that matters most for this campaign: it is a real
Simple-vs-Chrome layout comparison, and a one-pixel perturbation of Simple's
output is enough to turn it red against Chrome's committed `getBoundingClientRect`.

### Not built, deliberately

No comparison was created for tokenize, prepaint, composite, or DOM. Each is
listed in § 4 with the reason. A placeholder test for a stage with no Chrome
artifact would be worse than the gap it hides.

## 8. Related documents

- `doc/03_plan/platform/chrome_modern_web_platform_compat_plan.md` — conformance
  target; not superseded by this document.
- `doc/03_plan/ui/web_browser/simple_web_renderer_chrome_compat_corpus.md` —
  corpus definition; corrected by § 5.
- `doc/06_spec/05_perf/web_render_chrome/chrome_vs_simple_spec.md` — present-stage
  evidence.

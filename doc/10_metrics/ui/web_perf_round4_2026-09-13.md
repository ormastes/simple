# Web renderer cold-pipeline perf, round 4 — macOS, 2026-09-13

Interpreter `/Users/ormastes/simple/build/cargo-r2/release/simple`
(39,528,776 bytes, 2026-09-12 16:57), `SIMPLE_EXECUTION_MODE=interpreter
SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_WEB_STYLE_COUNTERS=1`, viewport 900x760, one
render per page, all eight `examples/06_io/ui/web_catalog/*.html` in ONE
process. Oracle: per-page `sha256` (first 16 hex) of the complete
`draw_ir_to_sdn(composition)` text. Instrument:
`build/perfbench/{pipeline_bench.spl,paired.sh,specs.sh}` — uncommitted lane
tools, `build/` is gitignored.

Round 3's caveat still stands and is the reason this round is measured the way
it is: wall clock on this host varies ~2.5x between runs of the *same* tree.
Round 4 therefore reports a **paired A/B**: four runs alternating
BEFORE (`origin/main`'s copies of the three touched files) and AFTER (this
tree), in one sitting, averaged — plus `sec_select_ms`, a bucket this change
does not touch, as a within-run control.

## Round 3's target list, re-measured — and one target was the wrong one

Round 3 handed round 4 three targets. Splitting round 3's single lumped
sub-bucket into eight temporary sub-buckets inside `sec_inherit` (removed
before landing) disproves one of them outright and re-sizes another.

`html` page, `sec_inherit_ms = 981`:

| sub-bucket | ms | share |
|---|---|---|
| `presentational_attr_decls` | **390** | 40% |
| `tag_defaults` | **166** | 17% |
| `st.inherit_from(parent_style)` | 62 | 6% |
| `renderer_default_style()` | 24 | 2% |
| `styles[nd.parent].display` | 33 | 3% |
| `val parent_style = styles[nd.parent]` | **18** | 2% |
| `styles[nd.parent].font_size` | 18 | 2% |
| `apply_decls(st, pres_decls, em_base)` | **0** | 0% |

- **Target 1 was half wrong.** Round 3 attributed 45% to
  `presentational_attr_decls` + `apply_decls` *jointly*. `apply_decls` is
  **0 ms**: it only runs when `pres_decls.len() > 0`, and essentially no
  element in these pages carries a legacy presentational attribute. There is no
  per-element declaration re-parsing to memoize. The whole 40% is
  `presentational_attr_decls` itself.
- **Target 3 is not a target.** The three `styles[nd.parent]` touches total
  **69 ms of 981 (7%)**, not the ~25% remainder round 3 guessed, and the full
  `val parent_style = styles[nd.parent]` *bind* (18 ms) is **cheaper** than the
  `.display` field read through the index (33 ms). Whatever copy-on-bind costs
  in this interpreter, a 204-field `Style` bind is not a measurable per-node
  cost here. Rewriting those three lines was not done, and should not be done
  on perf grounds. The unattributed remainder (~270 ms) is the surrounding
  loop body plus the eight timer pairs themselves.
- **Target 2 stands**, at 17% rather than 20%, and the task's suggested shape —
  "a memo keyed by tag id, built once per process" — is **not implementable**:
  `tag_defaults` reads `st` (`small`/`sub`/`sup` scale `st.font_size`, `mark`
  reads `st.bg`, `hr` reads `st.display`), so its result is not a function of
  the tag alone.

## Fix 1 — `presentational_attr_decls`: six byte-array scans became one

`presentational_attr_decls` ran six independent `attr_value` /
`attr_value_by_key` / `attr_present` lookups over every element's raw attribute
text (`hidden`, `bgcolor=`, `width=`, `height=`, `align=`), and each of those
helpers calls `inner.bytes()` — materialising the byte array again — then walks
it. Six passes per element, to find nothing on almost every element.

Added `html_has_presentational_attr(inner)`
(`..._foundation.spl`): ONE quote-aware pass over `inner.bytes()`, testing at
each token start whether any of the five names matches, using exactly the
token-start rule and the case-insensitive `html_attr_name_byte_equal` comparison
the individual lookups use. `presentational_attr_decls` returns `""` early when
it answers false.

Conservative by construction rather than by hope: a `false` answer means no
token start in the attribute text matches any of the five names, so all six
lookups would have found nothing and the function's output would have been
`""`. It can never suppress a real match — matching the bare name at a token
start is a strict superset of matching `name=` at a token start.

## Fix 2 — `tag_defaults`: a 191-argument constructor became 19 assignments

`_tag_defaults_without_metadata` ended in a **191-argument `Style(...)`
constructor literal**, built for every node, in which 168 of the arguments were
the verbatim `field: st.field`. The `is_non_rendered_tag` early branch was a
second copy of the same literal. Both are now in-place assignments on `st` —
which is already a by-value parameter copy, so mutating it is exactly what the
literal expressed. Two of the function's own existing branches (`mark`,
`fieldset`) already mutated `st` in place, so this is the shape the function was
half-written in.

The literal was not a pure copy, and this was checked rather than assumed:
`class Style` has **204** fields, the literal named **191**, and the
`tag_defaults` wrapper restores 4 more. The remaining **9** —
`grid_template_columns`, `grid_template_rows`, `grid_column`, `grid_row`,
`grid_template_areas`, `grid_area`, `grid_auto_flow_column`,
`text_decoration_overline`, `text_decoration_line_through` — were silently
**reset to their class defaults on every node**, because they were absent from
the literal. Plus the four `resolved_font_*` fields, which the literal reset
explicitly. The in-place version writes all thirteen resets explicitly, so
behaviour is preserved byte for byte (and the previously-implicit reset is now
visible in the source instead of being an artifact of an omission from a
191-argument literal).

## Result — paired A/B, `sec_inherit_ms`

Mean of two BEFORE and two AFTER runs, alternated. `sec_select_ms` is the
untouched control: its 8-page total moves 1506 -> 1516 (+0.7%), so the two
sides saw comparable host load.

| page | `sec_inherit_ms` before | after | change |
|---|---|---|---|
| overview | 18 | 9 | -50% |
| html | 508 | 232 | -54% |
| css-layout | 597 | 278 | -53% |
| css-paint | 685 | 394 | -42% |
| forms-media | 126 | 75 | -40% |
| animation | 123 | 72 | -41% |
| evidence | 5 | 4 | -20% |
| tab-bar | 22 | 14 | -36% |
| **8-page total** | **2085** | **1076** | **-48%** |
| *control* `sec_select_ms` total | *1506* | *1516* | *+0.7%* |

Normalised against the control (`sec_inherit / sec_select`, which cancels host
load exactly): **1.384 -> 0.710, -49%**, and every individual page falls in the
-36%..-56% band — no page regresses.

Within `sec_inherit` after the fixes (same temporary sub-buckets, `html`):
`presentational_attr_decls` 390 -> 81 (**-79%**), `tag_defaults` 166 -> 55
(**-67%**).

## Gates

- **Draw IR digests: 8 of 8 byte-identical**, on all four paired runs, and
  identical to round 3's landed values:
  `5cdf8386bad82f0c`, `85a685ca46fc3527`, `76c359e483e11e84`,
  `d9a0d2a7e71a2960`, `a16ea7c83d459a5a`, `616ad24659d7779e`,
  `4cf797f8c3a8f3a4`, `56097a5a1ce50dda`.
- **GPU boundary audit PASS** —
  `SIMPLE_BIN=<interpreter> sh scripts/check/check-web-vulkan-gpu-boundary-audit.shs`,
  exit 0: `PASS — 2 frame(s) audited, host_pixel_iterations=0,
  readbacks_per_frame<=1, submits_per_frame<=1`, `full_readbacks=0`,
  `host_paint_pixels=0`, `host_fallback_reasons=none`.
- **Neighbouring specs: 19 `*style*` / `*cascade*` / `*inherit*` specs** under
  `browser_engine` / `rendering` / `render_opt` — exit code and timing-stripped
  output digest **identical on both sides**, run on this tree and then on
  `origin/main`'s copies of the three touched files (same tree, same binary, so
  only the change under test is toggled). Three are RED on both sides and were
  already RED at `origin/main`: `be_dom_event_path_and_style_serialize_spec`,
  `style_animation_spec`, `simple_web_css_cascade_spec` — pre-existing,
  untouched by this change, same three round 3 recorded.

## Left for round 5

With `sec_inherit` halved, it is no longer the largest style-stage bucket.
On `html` after this change the ordering is `sec_metrics_ms` 666 /
`sec_resolve_ms` 615 / `sec_inherit_ms` 382 / `sec_select_ms` 312 /
`sec_cascade_ms` 314. `sec_metrics` and `sec_resolve` (font metric resolution)
are the next targets and have never been profiled internally. Inside
`sec_inherit` the residue is `presentational_attr_decls` 81 ms and
`tag_defaults` 55 ms — both now small enough that the loop body itself and the
`inherit_from` parameter bind (34 ms) are comparable, so further work there has
a low ceiling.

# Chrome ↔ pure-Simple web parity — round 11 (2026-09-13, macOS)

Host macOS (Darwin 25.5.0), binary `build/cargo-r2/release/simple`
(`SIMPLE_EXECUTION_MODE=interpreter`), differ
`scripts/check/check-chrome-layout-geometry-diff.shs` at `GEOM_DIFF_HEIGHT=20000`.
One binary and one Chrome per comparison, both sides in this detached worktree:

- **A (before)** — `origin/main` @ `f281963e4ac` (round 10's landed tree).
- **B (after)** — A plus the changes below, and nothing else.

## (1) Which faces each side actually used

Chrome's faces are not recorded in a fixture — the differ launches headless
Chrome per page against the live catalog, so Chrome resolved the generic
families with the host's own defaults. Every catalog page declares exactly
`font: 16px/1.5 sans-serif`, with `<code>`/`<kbd>`/`<samp>` on the UA monospace,
and `lang="en"`. On macOS that is **Helvetica** for `sans-serif` and **Menlo**
for `monospace`.

Measured from the files themselves (`hmtx`/`head`/`cmap`, at 16 px):

| face | `M` | `abcdefg` |
|---|---|---|
| Menlo Regular (`Menlo.ttc` face 0) | **9.633** | 67.43 |
| Helvetica Regular (`Helvetica.ttc` face 0) | 13.328 | 56.94 |
| Helvetica Bold (`Helvetica.ttc` face 1) | 13.328 | **61.34** |
| Noto Sans Mono (bundled) | 9.600 | 67.20 |
| Noto Sans SC (bundled) — **Thin, wght=100** | 12.320 | 56.83 |

Menlo's `M` is 1233/2048 em = **9.633 px**, which is exactly the 9.63 px/char
round 10 measured out of Chrome. The bold delta is 61.34 − 56.94 = **+4.4 px**,
exactly Chrome's +4.

Simple's faces, read from `ResolvedFontMetrics.identity` in the running
renderer at `origin/main`:

| request | identity before | identity after |
|---|---|---|
| `monospace`, lang `en` | `sha256=2cb2adb…;axes=wght=400,wdth=100` (Noto Sans Mono) | `unmanaged=/System/Library/Fonts/Menlo.ttc#0` |
| `sans-serif`, lang `en` | `sha256=a304181…;axes=wght=100` (Noto Sans SC **Thin**) | `unmanaged=/System/Library/Fonts/Helvetica.ttc#0` |
| `sans-serif` bold, lang `en` | same as regular | `unmanaged=/System/Library/Fonts/Helvetica.ttc#1` |

Two things that table says and round 10 could not: the sans face was not merely
the wrong typeface, it was the wrong *instance* — the bundled variable font's
static metrics are its **wght=100 Thin** master, which is where the −7% /−12%
sans deficit came from; and bold and regular were literally the same identity,
which is why the bold delta was 0.

## (2) Why `try_load_runtime_ttf` rejected macOS system fonts

Root cause, `src/lib/nogc_sync_mut/sffi/spl_fonts.spl:215`
(`FontRasterizer.load_selected`):

```
if selected_font_asset_candidate_for_path(ttf_path) == nil:
    return FontRasterizer.invalid()
```

It is **a path allowlist, not a format check**. `selected_font_asset_candidates()`
is the pinned-provenance registry the bundle and the SimpleOS image rely on, and
a path with no entry in it is refused *before the file is ever opened*. Nothing
about `Arial.ttf` was ever looked at — not its `sfnt` tag, not a table count, not
a size cap. That is why round 9 saw a rejection in the same process that loaded a
bundled Noto asset, and why the rejection was identical for regular and bold.

The fix keeps that allowlist exactly as it is and adds an explicitly **unmanaged
lane beside it**, taken only after the managed one declines:
`FontRasterizer.load_unmanaged` (`spl_fonts.spl`), reached from
`FontRenderer.try_load_runtime_ttf` (`font_renderer.spl:1320`). It keeps every
structural validation the managed lane has (`font_runtime_ttf_default_supported`
→ `validate_default_glyf_font`); it widens *which files are accepted*, never
*whether a file is validated*.

**`ttcf` was a second, independent blocker.** Menlo and Helvetica ship only as
collections, and `parse_offset_table` never accepted `ttcf` — the four versions
it admits are `1.0`, `OTTO`, `true` and `typ1`. A collection's table records hold
offsets absolute from the start of the *file*, so a face cannot be used by
slicing. `sfnt_ttc_extract_face` (`src/lib/common/encoding/sfnt.spl`) **repacks**
one face into a standalone sfnt blob with rewritten offsets, so every downstream
consumer — `glyf`, `cmap`, `hmtx`, and the atlas composite — sees an ordinary
single-face TrueType file and needed no change at all. A face is named with the
spec `<path>#<N>`; a bare path is face 0.

## (3) The language/category override made the routing dead on real pages

Routing `monospace` → Menlo and `sans-serif` → Helvetica (prepended to the
bundled candidate lists, and only when the file is present, so Linux and CI keep
their exact candidate order) was **live under `lang="und"` and dead under
`lang="en"`**, which is what every catalog page declares. Measured:

```
sans-serif lang=und -> unmanaged=…/Helvetica.ttc#0   total=57
sans-serif lang=en  -> sha256=a304181…;axes=wght=100 total=56   <- bundled Thin
```

`_resolve_font_metrics_with_language_config_uncached` replaces the requested
family with the coverage matrix's witness family whenever the language is not
`und`, and `browser_bundled_font_path_for_family` then answers with that bundled
asset **alone**. The same override is what silently discards an explicit
`@font-face` source (filed in round 9). The matrix exists to guarantee a bundled
face with real coverage for a *script*, and for complex-script content that is
exactly right — so the override is now skipped only when the content is
simple-script **and** the family already resolves to a face the host provides
(`browser_family_has_host_face`). On a host with no platform faces that
predicate is false for every family, so Linux and CI keep the current behaviour.

## (4) Bold

`browser_font_family_for_weight` routes a bold run through the existing
`__simple_font_face__|<source>|<family>` channel, so neither call site learns a
new parameter. It routes **only** the two generic families whose platform bold
face is the same typeface as their regular one. Round 9 built a bold list that
fell back to `DejaVu-Bold` for an unrelated family and refused to land it,
correctly: that swaps the *typeface*, not the weight. So a serif stack, an
explicitly named family, a bundled family and an already-decorated `@font-face`
value are all returned untouched — **bold there stays the regular face, recorded
rather than synthesised**. Variable-font `wght=700` instancing was NOT
implemented; that remains the route for the bundled faces on Linux.

Measured through the live renderer at `lang="en"`, `abcdefg` at 16 px:
regular **57**, bold **62**, delta **+5** (Chrome +4; the face is now correct
and the residual is the integer rounding below). Round 10's probe measured
Chrome at 60/64 for the same runs because that probe declared
`-apple-system, system-ui, sans-serif` and Chrome resolved it to **SF**, not
Helvetica. The catalog declares bare `sans-serif`, which is Helvetica. That is
a real difference between the probe and the pages, not a residual error, and it
is why 57 is the right target here and 60 was not.

## Per-page, before → after

`compared` / `mismatched`:

| page | compared | A mismatched | B mismatched | delta |
|---|---|---|---|---|
| overview | 18 | 5 | **4** | −1 |
| html | 431 | 342 | **338** | −4 |
| css-layout | 401 | 384 | 384 | 0 |
| css-paint | 528 | 511 | 511 | 0 |
| forms-media | 103 | 102 | 102 | 0 |
| animation | 81 | 79 | 79 | 0 |
| evidence | 4 | 0 | 0 | 0 |
| tab-bar | 9 | 7 | 7 | 0 |
| **total** | **1575** | **1430** | **1425** | **−5** |

`compared` is 1575 on both sides and matches round 10 exactly, so the DOM
projection did not change and the delta is attributable. Nothing regressed on
any page.

**This is a small number and the round does not pretend otherwise.** The task
predicted the `li`/`p` wrap clusters and css-paint's root rows would "drop
substantially"; they did not move at all. The prediction assumed the mismatch
was driven by *which face* was measured. It is not — it is driven by the
per-codepoint integer rounding below, which the correct face cannot fix and
which is the same on both sides. What the round did buy is that the faces are
now the ones Chrome used, three real defects are gone, and bold exists at all;
the arithmetic that would actually move these rows is now identified and
written down rather than guessed at again.


## What is left, and the arithmetic for it

**Mono is now the right face and the same number.** Simple measures **10.0
px/char** (80 px for `MMMMMMMM`); Chrome measures 9.63 (77 px). Sans is
**57** for `abcdefg` against Helvetica's own 56.94, and bold is **62**
against Chrome's 64 — the bold DELTA is now +5 where it was 0, i.e. real, and
over-shoots Chrome's +4 by one pixel for the same rounding reason. Menlo's 9.633 and the bundled Noto Mono's 9.600
both round to 10, so the face swap could not move it and was never going to:
`ResolvedFontMetrics.advances` is `[i32]`, one integer per codepoint, and Chrome
accumulates fractionally — 8 × 9.633 = 77.06, which it reports as 77, while eight
independently-rounded 10s give 80.

The contained fix, recorded rather than attempted here because it is its own
lane: emit `advances[i] = round(cumulative[i+1]) − round(cumulative[i])` from a
milli-px advance inside `measure_text_advances` / the sfnt measure path. The sum
then accumulates fractionally (8 × 9.633 → 77) while every consumer keeps
`[i32]` and no layout code changes. The same arithmetic closes the residual +1
on bold.

## Perf

`sfnt_ttc_extract_face` copies the face's tables one byte at a time
(`630,420` interpreted iterations for Menlo). An earlier revision also hashed
the repacked face with `sha256_u8_hex` for its cache identity; that dominated —
a probe that ran in under two minutes stopped finishing in twenty. The identity
is now `unmanaged=<path>#<face>;bytes=<n>`, built and parsed in one place
(`font_unmanaged_face_identity` / `font_unmanaged_identity_face_spec`), which is
an honest name for what it is rather than a partial digest wearing a `sha256=`
prefix. The byte-copy loop remains; `common/encoding` may not reach for the
`rt_bytes_slice` extern that would replace it without taking a layer dependency
the baremetal font path cannot have.

## Paint, not just layout

Both paint consumers (`engine2d/engine.spl`, `draw_ir_target_metal.spl`)
re-resolve a face from the identity the *layout* recorded, via
`selected_font_asset_local_path_for_identity` — which answers `""` for an
unmanaged identity. Left alone, the page would have been measured against
Helvetica and drawn with the fallback. `try_load_registered_identity` now knows
both identity shapes, and `engine.spl`'s `selected_path == ""` gate now runs
*after* the identity is offered to the renderer rather than before.

## Specs

- New: `test/01_unit/browser_engine/platform_system_face_metrics_spec.spl`
  **24/24**. It includes round 9's exact reproduction —
  `try_load_runtime_ttf("/System/Library/Fonts/Supplemental/Arial.ttf")` must be
  true — plus: collection recognition and face count; a repacked face that the
  sfnt validator accepts; a rejected out-of-range face index; Menlo `M` = 9.632
  px at 16; the Arial regular/bold `abcdefg` delta of +4; a real `get_glyph`
  with non-zero width/height/advance off the repacked face (geometry parity with
  blank glyphs would be a regression, not a fix); two faces of one collection
  getting distinct identities; identity round-trip through a live renderer; and
  the four bold-routing cases that pin "never swap the typeface".

- Neighbours on B, all GREEN, including the two that exercise the loader
  directly: `monospace_inline_line_box` 5/5,
  `font_family_generic_classification` 5/5,
  `inline_run_advance_and_break_boxes` 5/5, `paint_layout_advance_parity` 2/2,
  `inline_content_area_half_leading` 4/4, `anonymous_block` 4/4,
  `first_child_top_margin_collapse` 10/10, `li_last_child_margin_collapse`
  12/12, `form_control_ua_font` 4/4, `li_nested_list_scope` 5/5,
  `html_tree_builder_flat_projection` 6/6,
  `test/03_system/lib/text_layout/vector_font_pipeline_spec` 3/3, and
  `test/02_integration/rendering/font_renderer_bungee_native_probe`
  `status=pass`.
- **The bungee probe is the one that matters most here.** It sets
  `SIMPLE_ASSET_ROOT=/dev/null` and requires `try_load_runtime_ttf` on a
  registry asset to answer FALSE. The unmanaged lane would have re-opened that
  same relative path from the cwd and loaded it, turning the new lane into a
  bypass for asset-root enforcement. `load_unmanaged` therefore refuses any
  path the registry owns, and this probe is what proves it — it is pinned a
  second time as a unit case in the new spec.


## Pre-push guards (recorded, not stepped over)

Run in the foreground against `f281963e4ac..aeda9f8ccda`, each exit code
captured into a variable on the line after the invocation, never through a
pipe:

| guard | rc | verdict |
|---|---|---|
| `check-no-conflict-markers-push` | 0 | PASS — 10 file(s) scanned, 0 conflict markers |
| `check-tree-size-push` | 0 | PASS — 1 commit checked, base 137,269 files, 0 structural faults |
| `check-no-conflict-tree-push` | 0 | PASS — 1 commit, 1 unique tree, 0 conflict trees |
| `check-no-revert-push` | 0 | PASS — 10 file(s) checked, 0 reverts |
| `check-test-tree-divergence-delta` | 0 | PASS — 3,213 pre-existing offender(s), 0 introduced by this range |

**Divergence-delta step-over, recorded as the rule requires.** The base guard
is honestly RED at `f281963e4ac` — `FAIL — 3941 diverged vs 965 baselined
(3079 new, 103 fixed-but-still-baselined); 32 mirror-only (31 unallowlisted, 0
stale-allowlist)` — and that red is entirely pre-existing. The delta helper ran
in `--ref` mode on BOTH sides and diffed the offender lists byte-for-byte:
**3,213 pre-existing offenders, 0 introduced by this range.** The saved list is
at `$TMPDIR/test_tree_divergence_preexisting.txt` for the run above. The only
test path this range touches is
`test/01_unit/browser_engine/platform_system_face_metrics_spec.spl`, a new file
with no twin under `test/unit/`; `git diff --name-only f281963e4ac..HEAD --
test/01_unit test/unit test/02_integration test/integration` lists that one
path and nothing else, and the helper's own offender-list diff — not that
enumeration — is the authority for the PASS.

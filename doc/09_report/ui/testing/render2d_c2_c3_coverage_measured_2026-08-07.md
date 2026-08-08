# C2/C3 decision coverage — engine2d SIMD + os/compositor closure — 2026-08-07 (retry)

Plan: `doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`
(Unit C2, lines 461-464; Unit C3, lines 466-471). Prior attempt (same day, earlier
session): `doc/09_report/ui/testing/render2d_c2_c3_coverage_blocked_by_contention_2026-08-07.md` —
blocked purely by shared-box contention (load 11-18), zero numbers produced.

Retry conditions: `uptime` load average ~3.5 (down from ~18) at start, confirmed
again mid-run. `bin/simple` (`bin/release/x86_64-unknown-linux-gnu/simple`) was
redeployed 2026-08-07 23:20, after the T7 JIT named-fn guard and blend-span native
kernels landed. All runs below used the redeployed binary and completed to a
printed `Results:` line — no run timed out.

## Verdict: real, artifact-backed decision-coverage numbers for both units. Labeled DECISION-ONLY — the runtime does not emit condition rows (see caveat below).

## Method

- `SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<distinct path>.sdn bin/simple run
  src/app/test_runner_new/test_runner_single.spl <spec> --no-session-daemon
  --sequential`, one spec at a time, output captured to a distinct path per spec
  (SIMPLE_COVERAGE_OUTPUT is overwritten per sub-process, not accumulated —
  confirmed and worked around).
- `bin/simple spl-coverage rollup --file <a>.sdn --file <b>.sdn ...` to union the
  per-spec artifacts into one dump per unit.
- The rollup `summary:` block's `total_decisions` / `covered_decisions` counts
  were cross-checked by parsing the RAW DUMP rows directly (`hash, path, line,
  col, arm0_count, arm1_count`; "covered" = both arm counts > 0). The manual
  parse reproduced the tool's summary numbers exactly for both units (68/31 for
  C2, 207/37 for C3), so — unlike `spl-coverage status`'s vacuous
  `condition_percent: 100.0` on `total_conditions: 0` — these particular
  decision counts are NOT tautological; they are a real ratio over real rows.
  `total_lines`/`covered_lines` in the same summary WERE 100%-equal in both
  rollups (246/246, 797/797) — that pairing is not trusted as a real line
  number here and is not reported as such; only the decision pair is cited.

## C2 — `src/lib/nogc_sync_mut/gpu/engine2d/` SIMD closure

All 4 specs in `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/` run individually,
all green:

| spec | its | duration |
|---|---|---|
| `simd_isa_provider_spec.spl` | 24/24 pass | 377.9s |
| `simd_native_rows_spec.spl` | 12/12 pass | 96ms |
| `simd_provider_spec.spl` | 10/10 pass | 66ms |
| `simd_span_batch_execute_spec.spl` | 3/3 pass | 2.0s |

Rollup of the 4 artifacts (`/tmp/c2c3_cov/{simd_isa,simd_native_rows,simd_provider,simd_span_batch}.sdn`):

```
total_decisions: 68
covered_decisions: 31   → 45.6% decision coverage (C2)
```

7 of 68 decision rows (10.3%) carry the `<entry>` placeholder path instead of a
real file span — those rows are counted in the ratio above (the tool does) but
their location cannot be attributed to a specific source line; treat the 45.6%
as including ~10% location-unattributable rows.

Files touched by the covered rows: `simd_isa_provider.spl` (dominant),
`simd_kernels.spl`, `simd_native_rows.spl`, plus scalar-oracle/kernel_registry
rows pulled in transitively (`src/lib/common/gpu/engine2d/scalar_oracle.spl`,
`kernel_registry.spl`). **No dedicated spec exists for `kernel_registry.spl`**
(the plan calls out its "bucket boundaries" as an explicit C2 focus item, still
unaddressed) — its decision rows above come only from incidental exercise by
the SIMD specs, not targeted coverage.

## C3 — `src/os/compositor/` engine2d+software+vulkan closure

4 specs run (the plan's named focus files; `frame_pacer_spec.spl` included —
no sibling-plan collision entry found naming it claimed):

| spec | its | duration | direct-file line % |
|---|---|---|---|
| `compositor_engine2d_surface_spec.spl` | 10/10 pass | 2.2s | `compositor_engine2d.spl` 57% (66/115) |
| `engine2d_baremetal_core_parity_spec.spl` | 8/8 pass | 86ms | `engine2d_baremetal_core.spl` 11% (25/209) |
| `vulkan_compositor_backend_spec.spl` | 21/21 pass | 218ms | `vulkan_compositor_backend.spl` 66% (6/9) |
| `frame_pacer_spec.spl` | 6/6 pass | 65ms | (no coverage line emitted — file below the printed threshold or zero-decision) |

Rollup of the 4 artifacts (`/tmp/c2c3_cov/{compositor_engine2d_surface,engine2d_baremetal_core,vulkan_compositor_backend,frame_pacer}.sdn`):

```
total_decisions: 207
covered_decisions: 37   → 17.9% decision coverage (C3)
```

39 of 207 decision rows (18.8%) carry the `<entry>` placeholder path.

No dedicated spec found for `display_backend_core.spl`, `dirty_rect.spl`, or
`engine2d_baremetal_rect_core.spl` (repo-wide `grep -rl` over
`test/**/*_spec.spl` confirmed — none of the hits reference these three files),
matching the prior session's note; this remains the largest C3 coverage gap —
`engine2d_baremetal_core.spl` at 11% direct-line coverage is the weakest
measured file in the unit.

## What was NOT done

- No new spec `it`s were written this session — the task was measurement +
  report, not closure authorship. The 45.6%/17.9% numbers are the baseline the
  plan's Wave 3 closure work should target, not a finished state.
- `kernel_registry.spl` bucket-boundary its (C2) and `display_backend_core.spl`
  / `dirty_rect.spl` / `engine2d_baremetal_rect_core.spl` specs (C3) remain
  unwritten — same gaps the prior session's inventory flagged, now with a real
  coverage number attached instead of "not run."
- `condition_percent` is still not reported for either unit — the runtime does
  not emit condition (sub-expression) rows at all, only decision (branch) rows,
  confirmed again this session on both dumps (`total_conditions` absent from
  the fields the raw rows carry; only decision hash/path/line/col/arm-counts).

## Artifacts (this session, local scratch — not committed)

`/tmp/c2c3_cov/*.sdn` (8 per-spec artifacts), `/tmp/c2c3_cov/rollup_c2_full.txt`,
`/tmp/c2c3_cov/rollup_c3_full.txt` (raw unioned dumps backing the two ratios
above).

## C2 follow-up — kernel_registry boundary + residual-arm closure (2026-08-07, later same day)

New spec: `test/01_unit/lib/gpu/engine2d/kernel_registry_boundaries_spec.spl`
(18 examples, 0 failures — verdict `18 total, 18 passed, 0 failed`).

Method: reused the prior session's `/tmp/c2c3_cov/{simd_isa,simd_native_rows,
simd_provider,simd_span_batch}.sdn` artifacts unchanged (same 4 specs, same
baseline — no re-run needed), ran the new spec with
`SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/cov_kernel_registry_boundaries.sdn`,
then `bin/simple spl-coverage rollup --file <4 baseline artifacts> --file
/tmp/cov_kernel_registry_boundaries.sdn`. The rollup's `summary:` block
(`total_decisions: 68`, `covered_decisions: 49`) was hand-verified by parsing
the raw `decisions |id, file, line, column, true_count, false_count|` rows
directly and counting `covered = true_count>0 and false_count>0`, excluding
neither real-path nor `<entry>` rows (both counted, per the original report's
convention) — the manual parse reproduced 49/68 exactly.

**Before: 31/68 (45.6%). After: 49/68 (72.1%).** All 18 newly-covered rows
came from the new spec; `total_decisions` stayed at 68 (same decision-hash
identities, only hit-counts changed) so the two rollups are directly
comparable and this is not crediting another session's landed work — the
pre-existing `test/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.spl`
(committed `dc60d433f05`, outside `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/`)
was intentionally NOT added to this rollup's artifact set, since it was never
part of the 31/68 baseline either.

Newly-covered decision rows (18, by file:line, true/false arm now both hit):

- `kernel_registry.spl:79,81,83` — `kernel_size_bucket`'s three `count<N`
  bucket-boundary ifs; only the false (large-count) arm was hit before.
  Closed with `kernel_size_bucket(5)==TINY`, `(30)==SMALL`, `(100)==MEDIUM`.
- `kernel_registry.spl:91,93,95,97,99` — `kernel_slot_key`'s five
  out-of-range axis checks (op/format/alignment/contiguity/bucket); the
  true (rejection) arm was never hit before. Closed with five isolated calls,
  each with exactly one axis out of range.
- `kernel_registry.spl:148` — `kernel_table_register`'s `key<0` short-circuit;
  closed with an out-of-range `op`.
- `kernel_registry.spl:168` — `kernel_table_lookup`'s `key<0` short-circuit;
  closed the same way.
- `kernel_registry.spl:217` — `span_batch_push`'s overflow-refusal true arm;
  closed by pushing past a capacity-1 batch.
- `scalar_oracle.spl:161,191,205,217,242` — the `count<=0` early return in
  `oracle_fill_const`/`oracle_src_over_const`/`oracle_src_over_image`/
  `oracle_mask_src_over`/`oracle_hash_span`; closed by calling each with
  `count=0` and asserting `dst`/the hash seed is untouched.
- `scalar_oracle.spl:222` — `oracle_mask_src_over`'s per-pixel `m>0` check;
  the false (zero-coverage-pixel-skipped) arm was never hit before. Closed
  with a 2-pixel mask `[0, 0xFF]` and asserting only index 1 changed.
- `simd_kernels.spl:127` — `detect_simd_level`'s `_simd_detected` in-process
  cache-hit true arm; closed by calling it twice in the same spec process.

Documented-unreachable / left open (15 real rows, all in `simd_isa_provider.spl`
and `simd_kernels.spl`, none forced): `simd_isa_provider.spl` lines 65, 68, 87,
101, 116, 127, 144, 156, 183, 196, 225, 233, 234 are CPU-feature-gated or
probe-count branches whose alternate arm needs either a host lacking the
detected ISA or a differently-shaped registration sequence than this box's
specs exercise — not attempted this round (would need its own harness, out
of scope for a boundary-focused spec). `simd_kernels.spl:130`
(`if engine2d_simd_has_avx2():`) is the same class — this host has AVX2, so
the false arm cannot be forced without mocking the extern. `simd_kernels.spl:64`
is a `match` arm inside `feature_text()`, not an independent branch pair;
forcing the "other case" side was judged not a meaningful additional test.
These 15 rows plus the 4 `<entry>`-placeholder rows account for the
`68 - 49 = 19` gap (68-49-4=15, matches).

Artifacts: `/tmp/cov_kernel_registry_boundaries.sdn`, `/tmp/rollup_c2_after.txt`
(raw unioned dump backing 49/68), spec durably content-addressed at git blob
`cabd98bd20ae2c8ca9f0b2b977d250a9fdb7539b` before the run.

## Follow-up (2026-08-07, same day, later session): dedicated specs for the two named C3 gaps

New files (unit tests only, real hand-derived oracles — `assert_true` /
`assert_false` / `expect(...).to_equal(...)`, no faked-green assertions):

- `test/01_unit/os/compositor/dirty_rect_spec.spl` (new — `dirty_rect.spl` had
  zero specs before this) — 30 `it`s covering `IRect` construction,
  `irect_union`, `irect_intersects` (including the edge-touching non-overlap
  case), `irect_intersection` (overlap / disjoint / contained), `irect_area` /
  `irect_is_empty`, and the `DirtyRegion` accumulator (`add_rect` zero-w/h
  no-ops, `add_full_screen`, `bounding_box` fold-over-union, `clear`,
  `count`).
- `test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl` (new,
  companion to the existing `engine2d_baremetal_core_parity_spec.spl`) — 19
  `it`s targeting branches the parity spec's happy-path coverage left
  untouched: `draw_rect_stroked`/`draw_circle_stroked` outline-only behavior
  (vs the filled variants), zero/negative-size no-op guards, a clip rect that
  fully excludes the draw, the `gradient_rect` single-row `denom==1` fallback,
  `draw_line`'s sign/step branches in all four diagonal directions and its
  `thickness<=0` fallback, `draw_image`'s run-length collapsing (solid-color
  vs multi-color rows, zero-width no-op), and `draw_codes12_block`'s
  per-slot skip (code 0/space) and `scale<=0` vs `scale>0` cell-size branches.
  `display_backend_core.spl` was left unspec'd: it is a pure trait
  declaration (18 signatures, no function bodies), so there is no
  deterministic logic to hand-derive an oracle against — writing a spec for
  it would mean spec'ing a mock implementation of the trait, not the trait
  itself, which is out of scope for closing the *file's* coverage gap.

**Hardware-bound paths intentionally not spec'd** (documented in the new
spec's header docstring rather than mocked or faked green):
`create_fb_engine_core`'s direct-framebuffer draw path (writes through extern
`rt_gui_fill4` to live MMIO with no readback) and
`baremetal_simd_fill_enabled/hits/chunks/tail_pixels` (thin wrappers over
extern `rt_gui_simd_fill_*` counters reflecting live runtime SIMD-dispatch
state, not deterministic pure logic).

### Spec verdicts (both green, run individually per the mandatory foreground
invocation)

```
bin/simple run src/app/test_runner_new/test_runner_single.spl \
  test/01_unit/os/compositor/dirty_rect_spec.spl --no-session-daemon --sequential
→ Results: 30 total, 30 passed, 0 failed   (66ms)

bin/simple run src/app/test_runner_new/test_runner_single.spl \
  test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl --no-session-daemon --sequential
→ Results: 19 total, 19 passed, 0 failed   (86ms)
```

### Coverage before/after

Method: `SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<distinct>.sdn bin/simple run
... test_runner_single.spl <one spec> ...` per spec (confirmed this session:
`test_runner_single.spl` only accepts a single spec path — a second path
argument is silently ignored, `Files: 1` in the summary — so the tool's own
printed `coverage: <file> N% (X/Y lines)` line can only be obtained per single
spec, never pre-combined across specs in one process). For a combined-spec
number, `bin/simple spl-coverage rollup --file <a>.sdn --file <b>.sdn` unions
the raw `lines:` rows from both artifacts and the union was counted by hand
(`grep '<file>,' | awk -F', ' '{print $2}' | sort -n -u | wc -l`), divided by
the same per-file total (`Y` from the single-spec run, which is constant for a
given file regardless of which spec exercises it — confirmed: both
`engine2d_baremetal_core_parity_spec.spl` alone and the new
`engine2d_baremetal_core_spec.spl` alone independently printed the same `209`
total for `engine2d_baremetal_core.spl`).

| file | before | after | delta |
|---|---|---|---|
| `dirty_rect.spl` | 0/38 lines (0% — no spec existed) | 35/38 lines (92.1%, single-spec printed value) | +92.1 pts |
| `engine2d_baremetal_core.spl` | 25/209 lines (11.96%, parity spec alone, matches the C3 table above) | 29/209 lines (13.88%, rollup union of parity + new spec) | +1.9 pts |

> **Correction (2026-08-08):** the `before`/`after` percentages in this row
> were originally floor-truncated to one decimal (11.0% / 13.9%), which
> silently understated `before` and made the delta read as +2.9 pts. The
> true values are 25/209 = 11.96% and 29/209 = 13.88%, a delta of +1.9 pts;
> corrected above rather than rewritten silently.

Caveat on the `engine2d_baremetal_core.spl` delta: the union only picked up 3
lines net-new beyond the parity spec's 26 (`72`, `74`, `75` — inside the
`_pixel_at` helper, reached via the new `draw_image` multi-color-row test).
The new spec's other 16 `it`s (`draw_rect_stroked`, `draw_circle_stroked`,
`draw_image`'s run-collapsing loop, `draw_codes12_block`'s 12-slot dispatch)
all pass with correct hand-derived pixel assertions — proving that code
executes correctly — but the `lines:` rows the coverage artifact emits for
those functions did not increase. The recorded `line` numbers in the rollup
dump (max value seen: `143`) are well below those functions' physical source
line numbers (`draw_rect_stroked` starts at line 244, `draw_circle_stroked` at
344, `draw_image` at 366, `draw_codes12_block` at 381, in a 389-line file) —
i.e. the artifact's line numbers are the coverage instrumentation's own
numbering (likely desugared/lowered IR line positions), not raw source line
numbers, and its "lines" tracking appears to record only a sparse subset of
executed statements (concentrated in small always-called helper functions
like `_bm_a`/`_bm_r`/`_bm_g`/`_bm_b`/`_bm_clamp`) rather than full per-statement
coverage of larger multi-statement function bodies. This matches the
already-documented "DECISION-ONLY" caveat above (the runtime's coverage
artifact under-reports relative to what the passing assertions prove was
exercised) and is reported here as a measurement-methodology caveat, not
re-litigated as a fresh defect — the +1.9pt delta is what the tool itself will
report; the *real* increase in exercised, assertion-backed behavior is far
larger (19 new `it`s across 4 previously-unspec'd/under-spec'd code paths).

### Artifacts (this follow-up session, local scratch — not committed)

`/tmp/c3_cov_new/{parity_before,ebc_new,dirty_rect,ebc_combined}.sdn` (per-spec
coverage artifacts), `/tmp/c3_cov_new/rollup_ebc.txt` (raw unioned dump backing
the `engine2d_baremetal_core.spl` before/after row above).

## C3 decision-coverage closure (2026-08-08): re-measure with the 2 new specs + one targeted closure spec

Task: raise C3 *decision* coverage past the 17.9% (37/207) baseline above by
(1) re-measuring the full C3 spec set including `dirty_rect_spec.spl` (30 its)
and `engine2d_baremetal_core_spec.spl` (19 its), landed `b851840a`, whose rows
were never in the 37/207 artifact set, and (2) writing one new spec,
`test/01_unit/os/compositor/compositor_decision_closure_spec.spl`, closing
missing arms on reachable branches identified from the raw decision dump.

### Method (same as the baseline: per-spec `SIMPLE_COVERAGE_OUTPUT`, union via `spl-coverage rollup`, hand-verified)

`SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<distinct>.sdn bin/simple run
src/app/test_runner_new/test_runner_single.spl <one spec> --no-session-daemon
--sequential`, one spec per invocation (confirmed again: a second spec path
argument is silently ignored). `bin/simple spl-coverage rollup --file <a>.sdn
--file <b>.sdn ...` unions the raw `decisions |id, file, line, column,
true_count, false_count|` rows. Hand-verification: parsed every non-blank
decision row directly and counted `covered = true_count>0 and false_count>0`
per row (a row can be true-only from one spec and false-only from another —
covered only in the union, so counts were summed by id across the unioned
dump, not maxed per artifact); the manual parse reproduced the tool's
`total_decisions`/`covered_decisions` summary exactly at every step below.

**The denominator moves** once `dirty_rect_spec.spl` is added — `dirty_rect.spl`
had zero specs before, so none of its decision rows existed in the original
207-row artifact set (a row only exists once its file is loaded by some spec
in the rollup's input). All three ratios are reported, plus the apples-to-apples
figure computed by decision-id: of the original 207 baseline row *identities*,
how many are covered by the new artifact set (decision ids are content
hashes of the branch site, stable across artifact regeneration — confirmed by
re-running the original 4-spec baseline standalone and reproducing 207/37
exactly, hand-verified, matching the prior session's tool-reported numbers).

| step | specs | total_decisions | covered_decisions | ratio | apples-to-apples on original 207 ids |
|---|---|---|---|---|---|
| baseline (reproduced) | 4 (surface, parity, vulkan, frame_pacer) | 207 | 37 | 17.9% | — |
| +2 new specs (measurement only) | 6 | 223 | 58 | 26.0% | 45/207 = 21.7% |
| +1 closure spec (this session) | 7 | 233 | 74 | **31.8%** | **57/207 = 27.5%** |

Step 2 (adding the 2 already-landed specs) alone raised the apples-to-apples
figure from 17.9% to 21.7% — real closure that had simply never been rolled
into the artifact set. Step 3 (the new closure spec, below) added a further
+12 covered rows on the original 207 ids (45→57) and raised the raw union
ratio to 31.8%.

`49` of `233` rows (21.0%) in the final union still carry the `<entry>`
placeholder path (untargetable, same caveat as the baseline) — unchanged in
count from the baseline's 39/207 proportionally, since none of the newly
loaded files added `<entry>`-path rows this round (checked: 49 in both the
6-spec and 7-spec unions).

### Spec verdicts (all 7 run individually, foreground, per the mandatory invocation)

| spec | its | duration |
|---|---|---|
| `compositor_engine2d_surface_spec.spl` | 10/10 pass | 2.4s |
| `engine2d_baremetal_core_parity_spec.spl` | 8/8 pass | 75ms |
| `vulkan_compositor_backend_spec.spl` | 21/21 pass | 197ms |
| `frame_pacer_spec.spl` | 6/6 pass | 65ms |
| `dirty_rect_spec.spl` | 30/30 pass | 56ms |
| `engine2d_baremetal_core_spec.spl` | 19/19 pass | 85ms |
| `compositor_decision_closure_spec.spl` (new) | 6/6 pass | 2.3s |

### New spec: `compositor_decision_closure_spec.spl` — 6 targeted `it`s, real assertions only

Each `it` closes one specific decision row (file:line, missing arm),
identified by reading the raw dump row's exact source line and confirming it
holds a real branch before writing the case (per-file line numbers were
verified to map to real source lines here, unlike the `engine2d_baremetal_core.spl`
"lines:" caveat noted in the earlier follow-up section above — that caveat was
about the `lines:` coverage kind, not `decisions:`; decision rows for this
file did map to their stated source lines on inspection):

- **`compositor_engine2d.spl:131` false arm** — `get_pixel_buffer()` falls
  through to `self.engine.read_pixels()` when no pixel-buffer override was
  ever set (previously only the override-present true arm was exercised).
  Closed by asserting `get_pixel_buffer().len() == 16` on a fresh 4x4 backend
  with `retained_pixel_buffer_override_count() == 0`.
- **`compositor_engine2d.spl:190` true arm** (+ newly-exposed `:194` both
  arms) — the `batch.source.style_key == "wm.content"` walk that counts
  DrawIR image commands. Closed with a batch built via
  `draw_ir_batch_with_source(..., draw_ir_source_gui_ast(id, "wm.content",
  rev))` containing one image command and one rect command (mixed kinds, so
  `:194`'s `kind == DRAW_IR_COMMAND_IMAGE` check hits both its true and false
  arm). Asserted `result.selected_backend.len() > 0` — the one field
  guaranteed populated regardless of whether the image URI itself resolves
  (an unresolvable `test://image` URI triggers `fallback_required`, which
  this test isn't targeting; `last_web_content_image_count` is gated behind
  that success guard so wasn't used as the oracle here).
- **`compositor_engine2d.spl:205` false arm** — the readback-completed guard
  (`not fallback_required and skipped_command_count==0 and
  rendered_command_count>0 and pixels.len()==w*h`). Closed with an
  empty-commands batch (`rendered_command_count` stays 0), asserting
  `frame_provenance()` still reports `completed=false`.
- **`engine2d_baremetal_core.spl:75` true arm** — `_pixel_at`'s
  `idx >= pixels.len()` fallback inside `draw_image`'s run-length scan.
  Closed by calling `draw_image(0,0,4,1,[2 pixels])` — width 4 requested
  against a 2-element source array — and hand-deriving the exact resulting
  4-pixel row (`0xFF010101, 0xFF020202, 0xFF020202, 0xFF020202`, following
  the real run-length + out-of-bounds-fallback logic through by hand) rather
  than asserting a placeholder value.
- **`engine2d_baremetal_core.spl:114` true arm** — `_bm_blend`'s `sa==0`
  fully-transparent-source short-circuit. Closed via
  `draw_rect_filled(...,0x00FFFFFFu32)` over a pre-cleared buffer, asserting
  the destination pixels are unchanged.
- **`frame_pacer.spl:134` true arm** — `warm_startup_ms()`'s
  `frame_count==0` short-circuit, called directly (the existing spec only
  ever reaches `warm_startup_ms()` indirectly through `contract()`, which
  guards `frame_count > 0` before calling it). Closed by calling
  `pacer.warm_startup_ms()` on a fresh `FramePacer.for_60hz()` and asserting
  `0`.

### Genuinely unreachable arms — documented, not forced (5 rows, all in `engine2d_baremetal_core.spl` + 1 in `compositor_engine2d.spl`)

- **`engine2d_baremetal_core.spl:72`** (`_pixel_at`'s `x<0 or y<0 or
  width<=0` guard) — its only call site, `draw_image`'s run-length scan,
  passes loop indices `col`/`row` that start at 0 and never go negative, and
  `draw_image` itself early-returns at line 367 (`if w<=0 or h<=0: return`)
  before ever reaching `_pixel_at`. The guard is defensive dead code under
  the current call graph, not a reachable branch.
- **`engine2d_baremetal_core.spl:96` and `:98`** (`_bm_clamp`'s `v<0` /
  `v>255` guards inside `_bm_rgba`) — both of `_bm_rgba`'s two call sites
  (`gradient_rect`'s row interpolation at line 272, `_bm_blend`'s output
  color at line 128) compute their `r/g/b/a` inputs as convex-combination
  (weighted-average, weights summing to the divisor) interpolations between
  two already-`[0,255]`-bounded channel values, which is mathematically
  bounded to `[0,255]` by construction — clamping never fires for any input
  those call sites can produce. Verified by reading both call sites; not an
  argument that could be falsified by a test without bypassing those two
  callers entirely (which would mean testing `_bm_clamp` as an isolated unit,
  not as a reachable branch of this file's actual control flow).
- **`engine2d_baremetal_core.spl:112`** (`_bm_blend`'s `sa==255` opaque-source
  short-circuit) — both of `_bm_blend`'s call sites (`_fill_rect` line 211-212,
  `_blend_pixel` line 231-232) guard `_bm_a(color) < 255` before ever calling
  `_bm_blend`, so `sa==255` can never be true inside it under the current
  call graph. Same class as the `:72` finding — a defensive branch made
  unreachable by an upstream guard, not a missing test case.
- **`compositor_engine2d.spl:290`** (`font_provenance()`'s
  `identity == ""` guard, false/non-empty-identity arm) — `selected_font_identity()`
  returns `FontRenderer.current_font_identity()`, which is `""` (bitmap-default)
  until a real font asset is installed via `install_font_renderer`/font-file
  loading. Forcing the non-empty arm would require standing up a real font
  asset in the unit-test environment, which is host-font/filesystem-dependent
  infrastructure out of scope for a decision-arm closure spec — left open,
  matching the class of gap the C2 follow-up (kernel_registry section above)
  called "would need its own harness, out of scope for a boundary-focused
  spec."

Accounting: `233 - 74(covered) - 49(<entry>) = 110` remaining real-path
uncovered rows across the full transitive dependency graph pulled in by the 7
specs (most outside `src/os/compositor/` proper — the same transitively-pulled
`gpu/engine2d/` files the baseline noted). Restricted to files directly under
`src/os/compositor/`: `23` real-path rows, `18` covered (78.3%), `5`
documented-unreachable above (0 forced, 0 left silently uncounted).

### Artifacts (this session, local scratch — not committed)

`/tmp/c3_close_cov/{compositor_engine2d_surface,engine2d_baremetal_core_parity,
vulkan_compositor_backend,frame_pacer,dirty_rect,engine2d_baremetal_core,
closure}.sdn` (7 per-spec artifacts), `/tmp/c3_close_cov/rollup_4specs_baseline.txt`,
`/tmp/c3_close_cov/rollup_6specs.txt`, `/tmp/c3_close_cov/rollup_7specs_final.txt`
(raw unioned dumps backing the three ratios in the table above).

## Re-measurement after `<entry>` fix (deployed) — 2026-08-08

Context: `doc/08_tracking/bug/coverage_entry_placeholder_two_root_causes_2026-08-08.md`
landed a fix for root cause 1 (`Node::Impl` block methods never got
module-owner tagged, so any branch/line inside an `impl X:` block attributed
to the `<entry>` sentinel instead of the real file). Root cause 2
(entry-script top-level functions still get no owner) is **deferred, not
fixed** — residual `<entry>` rows from that cause still exist in this
re-measurement. Binary redeployed 2026-08-08 00:53
(`bin/release/x86_64-unknown-linux-gnu/simple`, 58,893,800 bytes).

### Method

Re-ran the same 7 C3 specs individually, foreground, one `SIMPLE_COVERAGE_OUTPUT`
per spec, per the original methodology:

```
SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<distinct>.sdn bin/simple run \
  src/app/test_runner_new/test_runner_single.spl <spec> \
  --no-session-daemon --sequential
```

then `bin/simple spl-coverage rollup --file <7 artifacts>` to union, then
hand-parsed the raw `decisions |id, file, line, column, true_count,
false_count|` rows directly (`covered = true_count>0 and false_count>0`) —
reproduced the tool's `total_decisions: 239` / `covered_decisions: 77`
exactly (239 real data rows counted after excluding the trailing blank line
the dump ends with).

All 7 specs still pass: surface 10/10, parity 8/8, vulkan **29/29** (was
21/21 — file grew independently, unrelated to this fix; total lines for
`vulkan_compositor_backend.spl` also grew 9→26), frame_pacer 6/6, dirty_rect
30/30, engine2d_baremetal_core_spec 19/19, compositor_decision_closure_spec
6/6.

### (a) Line coverage per compositor file — before vs. after

Single-spec `coverage: <file> N% (X/Y lines)` printed lines, before = original
2026-08-07 report's numbers (or the "before" row from its follow-up section);
after = same spec re-run today with the deployed fixed binary. Where the
report gave a union-of-multiple-specs number, the union is used on both
sides for a fair comparison.

| file | before | after (single spec, same spec as before) | delta |
|---|---|---|---|
| `compositor_engine2d.spl` (surface spec) | 57% (66/115) | 57% (66/115) | **0** — free-function-dominant file, `impl` fix doesn't touch it |
| `engine2d_baremetal_core.spl` (parity spec alone) | 11.96% (25/209) | **64% (135/209)** | **+52 pts** |
| `engine2d_baremetal_core.spl` (union: parity+new+closure specs) | 13.88% (29/209, 2026-08-08 correction) | **85.6% (179/209)** | **+71.7 pts** |
| `vulkan_compositor_backend.spl` | 66% (6/9) | 84% (22/26) — denominator changed (file grew independently), not purely attributable to this fix | n/a (denominator moved) |
| `dirty_rect.spl` | 92.1% (35/38) | 92% (35/38) | **0** — free-function file (`IRect`/`DirtyRegion` are struct field ops, not `impl` methods this fix touches), confirms the "only impl-heavy files move" prediction |
| `frame_pacer.spl` | "no coverage line emitted" (below print threshold) | still no per-spec coverage line printed; union rollup shows 6 lines covered against a 158-line file | unchanged behavior — same non-report quirk as before, not evidently the same bug family |

**Confirmed prediction: the fix is impl-method-file-specific.**
`engine2d_baremetal_core.spl` (impl-heavy — `Engine2DBaremetalCore` methods
like `draw_rect_stroked`, `draw_circle_stroked`, `draw_image`,
`draw_codes12_block`) is the file that moved dramatically — the single
`parity` spec alone went from 11.96% to 64% with **zero new test code**,
purely from correct attribution. `compositor_engine2d.spl` and
`dirty_rect.spl`, which are free-function/struct-op-dominant, did not move at
all — exactly matching the task's expectation ("the fix only helps
impl-method files; free-function files won't change").

`display_backend_core.spl` and `engine2d_baremetal_rect_core.spl` remain at
**0 covered lines** in the union — still no dedicated spec exercises either
file (confirmed again this session), same gap as the original report.

### (b) Decision (branch) coverage ratio — new C3 numbers, hand-verified

Full union (7 specs, all files transitively pulled in, matching the original
report's scope):

```
total_decisions: 239
covered_decisions: 77   → 32.2% (was 233/74 = 31.8% on 2026-08-07)
```

Hand-verified by parsing all 239 raw decision rows and counting
`true_count>0 and false_count>0`: reproduces 77 exactly.

**This ratio barely moved (31.8%→32.2%), and that is the expected, honest
result** — a branch's hit/miss status (true_count, false_count) does not
change when its file-attribution label changes from `<entry>` to a real
path. The `<entry>` fix relabels rows; it does not make more branches
execute. The interesting change is in the per-file breakdown, not the
aggregate.

**Restricted to `src/os/compositor/` real-path rows only** (the number the
original report called out specifically):

```
total = 74, covered = 52 → 70.3%   (was 23 real-path rows, 18 covered, 78.3%)
```

Per-file breakdown of the 74:

| file | decisions total | covered | ratio |
|---|---|---|---|
| `compositor_engine2d.spl` | 10 | 9 | 90% |
| `engine2d_baremetal_core.spl` | 52 | 32 | 61.5% |
| `vulkan_compositor_backend.spl` | 7 | 6 | 85.7% |
| `dirty_rect.spl` | 4 | 4 | 100% |
| `frame_pacer.spl` | 1 | 1 | 100% |

**The percentage went DOWN (78.3%→70.3%) even though both numerator and
denominator roughly tripled.** This is the honest, correct direction, not a
regression: the old 23-row set was a small, cherry-picked-by-accident subset
— rows that happened to already carry a real path (because they weren't
inside an `impl` block). The 51 newly-real rows revealed by the fix
(mostly from `engine2d_baremetal_core.spl`'s `impl` block, which the fix
newly attributes) include a substantial number of genuinely uncovered
branches — `engine2d_baremetal_core.spl` alone is 61.5% covered at the
decision level even though its line coverage looks like 85.6% (union); line
and decision coverage measure different things, and this file still has real
decision-level gaps worth targeting next (e.g. the previously-documented
"genuinely unreachable" rows in the original report should be re-audited
against the new real-path row set, since some of what was `<entry>` before
may now show up as reachable-but-untested rather than unreachable).

### `<entry>` residual count — root cause 2 still open

**3 `<entry>` rows remain** in the 239-row union (was 49/233 = 21.0% before
the fix; now 3/239 = 1.3%) — a real, large drop, consistent with root cause 1
being fixed. The 3 residual rows:

```
3179026103, <entry>, 106, 21, 24, 11
1168717216, <entry>, 104, 21, 11, 24
3996283373, <entry>, 104, 9, 1, 0
```

All three are at lines 104/106, column 9/21 — consistent with root cause 2
(entry-script top-level functions, i.e. code in the spec file itself, e.g. an
`it` block or helper `fn` defined directly in one of the 7 `*_spec.spl`
files rather than in an imported module). This matches the deferred/documented
scope of root cause 2 in the bug tracking doc — not re-investigated further
here, since it's explicitly out of scope for this measurement pass.

### Artifacts (this session, local scratch — not committed)

`/tmp/c3_remeasure/{surface,parity,vulkan,frame_pacer,dirty_rect,ebc_new,closure}.sdn`
(7 per-spec artifacts), `/tmp/c3_remeasure/rollup_full.txt` (raw unioned dump
backing all ratios above), `/tmp/c3_remeasure/decisions_only.txt` (extracted
decision-row section used for the hand-verification counts).

## Addendum (2026-08-08): 0%-covered files closed out

Two files remained at 0% covered lines with no dedicated spec after the
above measurement pass: `engine2d_baremetal_rect_core.spl` and
`display_backend_core.spl`. Both are now resolved.

### `display_backend_core.spl` — trait-only, no spec written

Confirmed still a pure trait declaration on origin/main: two traits
(`CompositorGlassCapable`, `CompositorBackend`), 18 method signatures total,
zero bodies. There is no logic to execute — any spec against this file would
either be vacuous (asserting a trait exists) or would actually be testing a
concrete implementer elsewhere (e.g. `Engine2dCompositorBackend`, which has
its own coverage path). No spec was written, per the instruction not to
write a vacuous spec for a file with no testable logic.

### `engine2d_baremetal_rect_core.spl` — new spec, 0% → 100% line coverage

New spec: `test/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.spl`
(13 examples, 0 failures). This narrow RV64-desktop-service rect core has no
buffer-backed render target (unlike its full sibling
`engine2d_baremetal_core.spl`) — `rect_core_draw_rect_filled`'s only paint
path calls `extern fn rt_gui_fill4` directly, and that extern has no
host-runtime implementation (`src/runtime/runtime_native.c` implements only
`rt_gui_get_glyph_8x16`, not `rt_gui_fill4`), so the actual-paint branch
cannot be safely reached from a hosted unit test.

The spec instead hand-derives every clamp/exclusion branch that runs BEFORE
the extern call, using rect geometries constructed so the post-clamp
exclusion guard (`x1<=x0 or y1<=y0`) returns early: the `w<=0 or h<=0`
guard (both operands), all four bounds-clamp `if`s (x0<0, y0<0, x1>width,
y1>height — true AND false outcomes for each), `rect_core_clear`'s
delegation through the same guard, and `rect_core_present`'s no-op body.

Measured with `SIMPLE_COVERAGE=1` + distinct `SIMPLE_COVERAGE_OUTPUT`,
foreground, `test_runner_single.spl --no-session-daemon --sequential`:

- **Line coverage: 0% → 100% (17/17 executable lines)**
- **Decision coverage: 11/12 branches (91.7%)** — 5 of 6 decision points
  (the `w<=0 or h<=0` guard and all four clamp `if`s) have both true and
  false outcomes hit. The 6th decision, `x1<=x0 or y1<=y0`, has only its
  TRUE (early-return) outcome hit — its FALSE outcome (proceed to paint) is
  exactly the `rt_gui_fill4` extern-call path documented above as
  host-unreachable. This is an honest, correctly-labeled gap, not a hidden
  one; no hardware/QEMU-only defect was found in the clamp arithmetic itself
  (all 13 hand-derived assertions passed against the real clamping logic).

No defect surfaced in either file. `_pack` (the file-private packing helper)
has no visibility modifier (default = same-file-only, per the Visibility
guide) and so cannot be imported into the spec directly; it is exercised
transitively by every case above.

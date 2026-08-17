# CPU hot-loop idiom gate: red at new=158, and the number is key churn, not new debt

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

- **Date:** 2026-08-01
- **Guard:** `scripts/check/check-cpu-hotloop-idiom.shs`
- **Baseline:** `scripts/check/cpu_lane_hotloop_baseline.txt`
- **File list:** `scripts/check/cpu_lane_hotpath_files.txt`
- **Measured at:** `b4b14d513b41846306b1e58049f04c567200465e` (origin/main tip)
- **Related:**
  `doc/08_tracking/bug/ui_backend_isolation_gate_red_and_unreachable_2026-08-01.md`
  — documents the job-abort mechanism by which this step's failure made every
  later step in `code-idiom-gates` report `skipped`. This gate is **step 4**,
  i.e. the abort point itself.

## 1. Summary

`check-cpu-hotloop-idiom.shs` exits 1 with `cpu_lane_hotloop_new=158` on every
push. Because it is step 4 of the `code-idiom-gates` job, steps 5-9 (including
`check-ui-backend-isolation`) reported `skipped` and never executed. A sibling
has since added `if: ${{ !cancelled() }}` to all six steps so they report
independently; this step is nevertheless still red and is the largest number in
the job.

Three findings, all PROVED by replay/sabotage at the tip commit:

1. **The 158 are genuine detections but not new debt.** Baseline total is 381,
   current total is **365** — current debt is *lower* than baseline. The 158
   arise because the content-keyed baseline was never regenerated after a large
   renderer refactor re-keyed the loops (same loops, renamed variables).
2. **The rule scored prose.** The BYTE/SUBSTR/CHAIN patterns are unanchored
   substring matches and fired on comments and string literals — including a
   comment documenting the rule itself. Fixed; zero real hits lost.
3. **Blame dates are fictional.** All nine flagged files *and the baseline file*
   trace to `7f5a55fa46e`, the 109.5k-file ENOSPC-wipe restore.

## 2. Date-attribution poisoning (PROVED)

`git log -1` for every flagged file, and for the baseline itself, returns:

```
7f5a55fa46e 2026-08-01 revert: restore main after truncated-tree wipe in 118c636ead8
```

The wipe-restore reset blame across the tree, so per-file ages are meaningless.
True history was recovered by **replaying the guard at earlier revisions**
(extracting each tree with `git archive` into an isolated scratch dir and running
the guard there):

| revision | date | baselined | current | NEW |
|---|---|---|---|---|
| `37cda4befdc` | 2026-07-25 | 361 | 376 | **42** |
| `1282f6e04d7` | 2026-07-25 | 381 | 376 | **18** |
| `beea94b72ce` | 2026-08-01 | — | — | *(tree wiped, no script)* |
| `b6234c8b6a0` | 2026-08-01 | 381 | 363 | **156** |
| `118c636ead8` | 2026-08-01 | — | — | *(tree wiped, no script)* |
| `7f5a55fa46e` | 2026-08-01 | 381 | 363 | **156** |
| `b4b14d513b4` (tip) | 2026-08-01 | 381 | 365 | **158** |

Readings:

- The gate was **already red before the wipe** (42 on 2026-07-25). It has never
  been green in the window examined.
- `1282f6e04d7` regenerated the baseline to 381, dropping NEW to 18.
- The jump 18 → 156 happened across `beea94b72ce`
  ("feat(2d): CSS-reachable gradients, tilemap texel sampling, DrawIR affine"),
  a **real feature landing** that rewrote the browser-engine renderers. The
  source churn is genuine; only the *dates* are wipe artifacts.

## 3. Triage of the 158

All 158 are **LOOP (157) + SUBSTR (1)**. Every one was hand-checked against the
rule and the source; **none is a false positive**. Per-file:

| file | new |
|---|---|
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` | 49 |
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl` | 40 |
| `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl` | 37 |
| `src/os/compositor/compositor.spl` | 11 |
| `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl` | 11 |
| `src/os/compositor/compositor_engine2d.spl` | 3 |
| `src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl` | 3 |
| `src/lib/gc_async_mut/gpu/engine2d/compositor.spl` | 2 |
| `src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl` | 2 |

126 of 158 (80%) are the three browser-engine renderer files.

**Why these are churn, not growth.** The same nine files also produced 113
*stale* baseline keys (baseline count exceeds current). The refactor replaced
loops rather than adding them: 133 keys went up, 113 went down, and the total
moved 381 → 365. Reported "new" is an artifact of content-keying — renaming a
loop variable retires one key and mints another.

**Why they were still not absorbed.** Absorbing them via `--update-baseline`
would be exactly the cover-up this gate exists to prevent, and would also
silently bless any genuine regression mixed into the refactor. They remain
scored. See §6 for the paydown plan.

### 3.1 A keying weakness worth noting (PROVED, FIXED 2026-08-02)

Five distinct multi-line loop headers in
`simple_web_html_layout_renderer_core.spl` collapsed to the single degenerate key
`while (`, because the key was the trimmed text of the header's first line. The
count ratchet still worked, but the key carried no information and could not
distinguish which of the five loops changed.

**Fixed.** The gate now joins a multi-line header's continuation lines up to and
including the one that closes with `:`, so the key is the full header text
(bounded at 12 lines; if no closing line is found the old first-line content is
kept, so the failure mode is the previous behaviour, never zero hits).

Safe to do now because the ratcheted baseline contains **no** multi-line key
(verified: every one of its 142 entries ends in `:`), so re-keying migrates
nothing. The refinement changes keys only, never the scored total:

* Real designated set, before and after: `baselined=207 current=365 new=158` —
  byte-identical totals. The degenerate `while (` (count 5) became four distinct
  keys summing to 5; reported violation *lines* went 133 → 136.
* All nine pre-existing fixture controls return identical
  `current`/`new`/`ok` triples before and after.
* Non-vacuity is durable, not just observed: fixture
  `multiline_distinct_offender.spl` holds two headers whose first line is the
  bare token `while (`. Old gate: one key `while (` count=2. New gate: two
  distinct keys, count=1 each. `new=2` in **both** — the fix refines keys, it
  does not loosen the gate. Asserted by
  `test/03_system/app/ui/feature/cpu_hotloop_gate_spec.spl`.

> Measurement trap hit while proving this: running the pre-change copy of the
> script from a scratch directory made it resolve `ROOT_DIR` outside the repo
> and exit 2 with no output, which read as "old gate found nothing" and would
> have faked a much larger improvement. The A/B is only valid with both copies
> under `scripts/check/`.

## 4. Rule defect: the gate scored comments and string literals (PROVED, FIXED)

`LOOP` is line-start anchored (`^[[:space:]]*(while|for)\b`) and is therefore
immune. `BYTE`, `SUBSTR` and `CHAIN` are unanchored substring matches and were
not. Sabotage probe on `src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl`,
adding four prose-only lines, moved the gate **158 → 162**:

```
CHAIN  ...backend_emu_adv.spl:# PROSE PROBE: this file uses .for_each( nowhere; documenting compliance.
CHAIN  ...backend_emu_adv.spl:val doc = "call .map( to transform"
SUBSTR ...backend_emu_adv.spl:# Avoid buf.substring(pos, end) in hot loops.
SUBSTR ...backend_emu_adv.spl:val doc2 = "use s.substring(i, j) sparingly"
```

Note the first line: a file was penalised for a comment **documenting its own
compliance** — the same failure class the neighbouring UI-isolation gate hit.

**Fix.** A hit in these three classes now survives only if its construct still
matches after trailing comments are removed and string *contents* are blanked,
i.e. only when it is real code. Quote state is tracked so a `#` inside a string
is not mistaken for a comment. This is a strictness *correction*, not a
relaxation: it removes only prose.

**Verification (all at tip):**

- Applying the fix to the unmodified tree leaves the new-violation key set
  **bit-identical** (`new=158`, diff empty) — zero real hits lost, including the
  one genuine `props.substring(pos, line_end)` and the one genuine
  `backend.mask_buf[mi]` byte read.
- Re-running the prose probe against the fixed rule drops all four prose hits
  while still catching a real `while total < n:` **and** a real
  `s.substring(pos, n)` in code (SUBSTR non-vacuity preserved).

## 5. Non-vacuity proof (PROVED by observed failure)

Sabotage of a real designated source file, four shapes including two negatives:

| shape | line added | expected | observed |
|---|---|---|---|
| A real loop | `while total < n:` | flagged | **flagged** (`LOOP`, 158 → +1) |
| C comment-only loop | `# while comment_only_i < n:` | ignored | **ignored** |
| E annotated loop | `while total < n:  # cpu-lane-loop-ok: ...` | ignored | **ignored** |
| D comment-only chain | `# items.map(fn)` | ignored | **flagged (bug, §4)** |

After restoring the file the gate returned to `new=158` with a key set
**identical** to the pre-sabotage run. The gate is live, the annotation escape
works, and it is not decorative.

## 6. Baseline hygiene (done) and the paydown plan

**Hygiene landed.** The baseline was ratcheted **down**: 239 keys / total 381 →
**142 keys / total 207**. 97 keys whose current count is 0 were dropped, 16 were
tightened to their current count, **0 added, 0 raised** (asserted
mechanically). `cpu_lane_hotloop_baseline_stale` went 113 → **0**.

> A correctness trap worth recording: 16 of the 113 stale keys had
> `0 < current < baseline`. *Deleting* those entries — the naive reading of
> "remove stale entries" — would have converted them into new violations and
> pushed the gate above 158. Stale entries must be tightened to `current`, and
> only entries with `current == 0` may be removed.

Non-absorption is proved: with the ratcheted baseline in place the gate still
reports exactly `cpu_lane_hotloop_new=158`.

**Remaining cost.** 158 loops across 9 files, in live rendering hot paths.
Converting a per-element interpreted loop to a bulk idiom changes rasteriser
semantics, so each needs a parity check against the CPU-lane reference body,
not a mechanical rewrite. Prioritised:

1. **`backend_software.spl` (11), `engine2d/compositor.spl` (2),
   `backend_emu.spl` (3), `backend_emu_adv.spl` (2)** — the engine2d rasteriser
   lane. Smallest, has a parity oracle (`indexed_fill`), highest per-loop payoff.
   Do first.
2. **`os/compositor/compositor.spl` (11), `compositor_engine2d.spl` (3)** —
   compositor blits; several are plausibly annotatable as documented permanent
   exceptions rather than rewrites.
3. **The three browser-engine renderers (126)** — largest and least hot per
   loop; much of this is CSS/selector parsing, where the correct fix is often a
   bulk scan rather than a per-position `substring`. Expect this to be the bulk
   of the effort and to need its own plan.

Until (1)-(3) land, the gate stays red at 158 by design. It must **not** be
absorbed, weakened, or given an env hatch.

### 6.1 Paydown landed 2026-08-02 — new 166 → 16

Steps (1)-(3) were executed as a **triage**, not a rewrite. All 269 flagged
loops across the nine designated files were read in place; **260 carry an
annotation naming what the loop walks and what its bound is**, and 9 were
deliberately left unannotated because they are real defects (§6.2). The change
was **comments only** — with `#`-comments and blank lines stripped, every
touched file is byte-identical to its parent. Baseline, file list, gate script
and spec untouched; `--update-baseline` was not used.

**The "126 in 3 renderers" concentration was one un-triaged file designation,
not 126 independent problems.** The three renderer files hold two different
subsystems — a CSS parse/cascade engine (`_core`) and a paint/DrawIR emitter
(`_paint_layout`) — so no single file-level verdict could be right for both.

**The mixing is organisational, not a runtime defect (PROVED).**
`simple_web_layout_rerender_retained` gates `compute_styles_with_material`
behind `dirty_stage == "css"` and reuses `prior.hit_index.styles` on paint-only
frames. Cascade does **not** run per paint frame.

**§3's "none is a false positive" is REFUTED.** Several flagged loops are not
bounded by any pixel, element or string length:

| site | actual bound |
|---|---|
| `os/compositor/compositor.spl` PS/2 keyboard drain | 8042 status-register output-full bit |
| `os/compositor/compositor.spl` PS/2 mouse drain | hardware queue, hard-capped at 64 packets |
| `_paint_layout` `while row < 4:` ×2, `while index < 2:` | literal constants |
| `_core:60` `props.substring(pos, line_end)` (the 1 SUBSTR) | per **line**, advanced by `find_from`, i.e. already the bulk scan the rule asks for — matched only because the cursor is named `pos` |

Design §6 states a **bound-based** rule ("a loop whose bound is a pixel-count /
element-count / string length"); the implementation approximates it with an
any-loop-header grep. These are false positives *of the approximation*. They
are annotated with the discrepancy stated explicitly. **The detector was not
weakened to drop them** — narrowing `LOOP` to a bound-based test would be a
loosening and is deliberately not done here.

Two more §6 assumptions refuted, recorded so they are not re-derived:
`_sort_candidates_by_specificity` / `_sort_positive_z_indices` /
`_sort_style_order_indices` are **bottom-up merge sorts** (O(n log n)), not
insertion sorts; and `draw_image_blend` does **not** bypass the bulk span
primitives — its five span loops are the SIMD gather, the SIMD scatter, two
scalar fallbacks and the clip/mask slow path around
`engine2d_simd_blend_row_u32`.

### 6.2 The residue: 16 scored, all filed, none annotated

The gate stays red at **`new=16`** on purpose. Each is a defect, not an
un-examined loop:

| site | defect |
|---|---|
| `_core:101` `_cb_chars_between` | **dead code** — exactly one occurrence in `src/` (its own definition). Delete it. |
| `_core:161` `_css_collect_custom_props` | backward selector rescan per declaration block |
| `_core:840` `_extract_css_vw_with_rule_limit` | O(n²) dedup rescan over emitted groups |
| `renderer:1020,1057,1058,1078` `_apply_css_animations` | 5-level nesting: per animated style × per keyframe × per declaration |
| `renderer:2439` `_web_gpu_solid_fill_ops` | `ops = ops.push(...)` — arrays are value types, so this clones the whole op list per node |
| `_paint_layout:1405,1417` `_html_draw_ir_nth_int` | **parse work on the paint path** — re-parses ints out of a text value per call, per node |
| `_paint_layout:1878,2146,2408,2754` | repeated linear scans that should be an index: `_html_draw_ir_image_index` walks the whole image list per node **inside** `for layer in background_layers`, i.e. O(nodes × layers × images) |
| `_paint_layout:316,344,368` input-text visual map | repeated boundary rescans per glyph |

Fixing these changes behaviour, so each needs a parity check rather than a
mechanical rewrite — they are intentionally left scored and red.

One perf TODO recorded in place rather than filed here:
`backend_emu.spl` `_emu_gradient_color_at` does a linear gradient-stop search
**per pixel**. A 1001-entry permille LUT makes it O(1) per pixel and is
bit-exact, because `pos_permille` is already an integer permille value.

### 6.3 Working the residue (2026-08-02): `new` 16 → 14, and two entries above are wrong

Three of the eight rows in §6.2 were re-examined against evidence. **Two were
not defects of the kind recorded, and one measurement refutes its premise
outright.** §6.2 is left standing above as written so the correction is
legible; read it together with this section.

**Landed — both were dead code, not optimisation targets** (`d881261b`):

- `_cb_chars_between` and `_html_draw_ir_nth_int` each have **exactly one
  occurrence in `src/`** — their own definition — and **zero in `test/`**.
  Neither is `pub`, neither is exported. §6.2 filed `_html_draw_ir_nth_int` as
  "parse work on the paint path" needing an optimisation with a parity check;
  **nothing calls it.** Both deleted, per the repo rule that dead code is
  deleted completely.
- Parity was established on real input, not by compiling:
  `test/01_unit/browser_engine/browser_renderer_spec.spl`, four runs
  alternating a pristine export of the parent (control) with the modified
  tree. All four arms report **10 examples, 2 failures**, and the two failures
  are the **same two by name** in both arms, so they are pre-existing and
  common-mode. Control-vs-control runs are byte-identical after normalising
  absolute paths. The only cross-arm output differences are diagnostic line
  numbers (which shift by exactly the deleted line count) and
  `web-style-producer budget-break` probe lines, which are wall-clock-budget
  dependent.
- **Measurement trap hit and recorded:** a first attempt had three of four arms
  SIGTERM-killed at **exit 143** by the 60 s `kill_simple_monitor` CPU guard,
  which truncated the outputs at different points and produced a *plausible
  but meaningless* "115 lines differ". Set `SIMPLE_TIMEOUT_SECONDS=0` for any
  A/B on this path, and assert every arm emitted a verdict line before
  comparing.

**REFUTED — `ops = ops.push(...)` does not clone** (§6.2 row 5):

The row claims "arrays are value types, so this clones the whole op list per
node". Measured externally, per process, alternating arms:

- `x = x.push(v)` versus a bare `x.push(v)` statement, identical total work
  asserted by both arms printing the same accumulator: **1.00x**, no
  measurable difference.
- Scaling test with **total pushes held constant at 120,000** while list
  length varies 500 → 2,000 → 8,000: relative cost **1.00x / 1.11x / 1.04x**,
  i.e. **flat across a 16x range of list length**. A clone-per-push would make
  the n=8,000 arm ~16x the n=500 arm. It does not.

So `x = x.push(v)` is **amortised O(1)** on this runtime, and the form is the
repo-wide idiom (**14,640 occurrences** of `X = X.push(` in `src/`). Singling
out this one site was wrong; there is nothing to fix here. This also
contradicts the older "seed `.push()` always clones, no fast path" note for
this form on this binary — treat that note as needing re-measurement rather
than as established.

**Not landed, and why** — the remaining rows all need a signature-threading
refactor (`_html_draw_ir_image_index` is called from three sites, two of them
inside per-node helpers, so hoisting the lookup into a prepared URI→index map
changes several signatures). The image list is genuinely **uncapped** — it
comes from the GPU host daemon's decoded resource payload — so
O(nodes-with-background × layers × images) is a real term and the row stands.
But this path's spec output is timing-noisy and already carries two
pre-existing failures, so a refactor of that blast radius cannot be held to
the parity bar used above. **Filed, not landed** — per the rule that a change
whose parity cannot be proved is not landed.

The `_emu_gradient_color_at` LUT is likewise **not** landed: a 1001-entry
table costs 1001 stop-scans to build, so it is a *pessimisation* for any
gradient smaller than ~1001 px (e.g. 32×32). Making it conditional on pixel
count adds a branch and a second code path for a per-pixel scan over ≤5 stops.
The TODO stays in place; it is not worth the complexity as stated.

**Binary-identity note for anyone repeating this:** the binary at
`bin/release/x86_64-unknown-linux-gnu/simple` currently prints *"this
Rust-built Simple binary is a bootstrap seed only"*. All arms above used the
same binary, so the comparisons are common-mode and valid, but none of these
numbers describe the pure-Simple self-hosted tool.

## 7. Status

- FIXED: prose scoring in BYTE/SUBSTR/CHAIN.
- FIXED: baseline staleness (381 → 207, stale 113 → 0).
- PAID DOWN (2026-08-02): 260 of 269 flagged loops triaged and annotated,
  `new` 166 → **16**. Comments only; baseline/file-list/script/spec untouched.
  See §6.1.
- FIXED (2026-08-02): two of the §6.2 rows were **dead code**, deleted with
  spec parity proved on real input — `new` 16 → **14**. See §6.3.
- OPEN: **14** scored violations. The gate remains red on the merits and must
  not be absorbed or weakened. The largest remaining item
  (`_html_draw_ir_image_index`, O(nodes × layers × images) over an uncapped
  image list) is filed rather than landed because a signature-threading
  refactor cannot be held to this lane's parity bar — §6.3.
- REFUTED (2026-08-02): §3's "none of the 158 is a false positive" — see the
  table in §6.1. Also refuted: the sorts are merge sorts, not insertion sorts;
  `draw_image_blend` does not bypass the bulk span primitives; §6.2's
  `_html_draw_ir_nth_int` row ("parse work on the paint path") described a
  function nothing calls; and §6.2's `ops = ops.push(...)` row is wrong —
  measured flat across a 16x list-length range, i.e. amortised O(1), not a
  clone per push (§6.3).
- FIXED (2026-08-02): degenerate `while (` multi-line key (§3.1), totals unchanged.
- CONFIRMED (2026-08-02): re-measured at origin tip `e4b4561c803`, independently
  of this document — `baselined=207 current=365 new=158`, and the 158 split
  126 / 32 exactly as §3 records. The count is **158**; `207/142` is the
  baseline total / key count, not a replacement figure for it. The committed
  baseline is a strict subset of current detections (0 keys present in the
  baseline but absent from a fresh regeneration; 122 keys new plus 20 count
  increases = 158), which independently confirms §6's "0 added, 0 raised".
- NOTE (2026-08-02): the gate spec's last example,
  "ratchets clean on the real designated file set", asserts `new=0` and is
  therefore RED for as long as §6's paydown is open. That is the gate working as
  designed, not a spec defect — do not relax the assertion to make it pass.

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: STILL-OPEN.** `scripts/check/cpu_lane_hotloop_baseline.txt` and
`scripts/check/check-cpu-hotloop-idiom.shs` are both still present and no rekeying commit
exists in current content. The date-attribution poisoning argument in the doc stands; the
baseline still needs rekeying so new=158 stops being reported as new debt.

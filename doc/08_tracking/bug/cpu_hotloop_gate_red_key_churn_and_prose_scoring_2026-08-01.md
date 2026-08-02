# CPU hot-loop idiom gate: red at new=158, and the number is key churn, not new debt

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

## 7. Status

- FIXED: prose scoring in BYTE/SUBSTR/CHAIN.
- FIXED: baseline staleness (381 → 207, stale 113 → 0).
- OPEN: 158 genuine hot-loop violations, plan in §6.
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

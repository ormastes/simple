# Geometry differ reported a whole page as "430 of 431 mismatched" when the page was never laid out

- **Filed:** 2026-09-13 (web parity round 13, macOS), as a layout defect
- **Root-caused:** 2026-09-14 (round 13). It is **not** a layout defect and there
  is nothing to bisect in `src/lib`.
- **Cause:** a runner binary older than an extern the layout module declares.
  Unregistered extern -> silent nil -> every box `(0,0,0,0)`.
- **Status:** the measurement lane is FIXED (fails closed). The underlying
  silent-nil class remains open —
  `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`.

## The evidence

`build/cargo-r2/release/simple`, the runner every recent round used, was built
**Sep 12 16:57**. Commit `08770cc5025` (**Sep 14 00:32**) added
`rt_engine2d_blend_cov_span_u32` — both the declaration in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl`
and its registration in `src/compiler_rust/compiler/src/interpreter_extern/simd.rs`
— in the SAME commit. A binary from two days earlier therefore loads a layout
module declaring an extern it cannot resolve.

The observable result on `html.html` at 900x20000:

| tree | zero boxes / total |
|---|---|
| `9290752171d` (before `08770cc5025`) | **0 / 432** — real geometry |
| `a7c3570d64f` (after) | **432 / 432** |

and on the newer tree the count is 432/432 on every repetition, with or without
`SIMPLE_EXECUTION_MODE=interpreter` and `SIMPLE_TIMEOUT_SECONDS=0`. **Env was
ruled out, not ruled in** — an interpreter that does not know a symbol answers
nil for it in any mode. (An earlier draft of this record blamed the env vars;
that draft was measuring two different TREES, not two different modes.)

## Why it looked like a detailed bug report instead of an error

Every KEY is still emitted — the renderer enumerates layout elements
independently of whether it can size them — so `missing_in_simple` is 0 and
nothing is structurally wrong. Each row's delta is then **Chrome's own
`(x, y, w, h)` verbatim**, because it is being subtracted from zero. On the
correct tree the same differ over the same archived Chrome harvest reports
`compared=431, mismatched=329` with ordinary small deltas (`main` dh=56,
`section` dy=1, `b` dw=4).

This artifact produced `html` 430/431 and `css-paint` 515/528 in rounds 12 and
13, and is also what round 12 recorded as "host/Chrome variance" (html 338 at
round 11 vs 430 at round 12).

## The fix: the measurement lane fails closed

`src/app/ui/chrome_showcase/layout_geometry_diff.spl` gains
`all_boxes_degenerate(boxes)` and refuses to diff when it holds:

```
ERROR — nothing was checked (every Simple box is 0x0 at 0,0 for <page>;
the page was not laid out. ...)
```

Two boxes minimum, so a genuinely single-element zero-sized page is not
mis-flagged. A fifth fatal selftest fixture covers both halves — the degenerate
side must be caught, and a real side that merely *contains* a zero box must
not be — so `--selftest` now reports `PASS — 5 fixture(s) checked, 0 failed`.

It was proven live on first contact: run against `a7c3570d64f` with the stale
binary it returns the ERROR above in 13 s instead of a 430-row table.

`scripts/check/check-chrome-layout-geometry-diff.shs` additionally pins
`SIMPLE_EXECUTION_MODE`/`SIMPLE_TIMEOUT_SECONDS` — not as a fix for this, which
it is not, but so an unpinned lane stops producing rounds of numbers that are
not comparable with each other.

## What is NOT fixed

- The silent-nil extern behaviour itself. A declared-but-unregistered extern
  should fail, not return nil; that is the tracked Stage-1 defect above.
- Nothing rebuilds or version-checks the runner against the tree it measures.
  A parity lane that runs a stale binary against a moving `src/lib` will keep
  finding new shapes of this; the guard catches the total-collapse shape only.
  A **partial** collapse (some boxes laid out, the tail zero) would still pass
  through — named here rather than left implicit.

## Superseded claims (from this record's original draft)

- "It appears to have REGRESSED ... bisect `round 11 tip .. round 12 tip`" — no.
- "`dh = 19` mono-block cluster" (round 12's next target) — that cluster is this
  artifact, not a line-box metric.
- "html 430 / css-paint 515" in `web_chrome_parity_round12_2026-09-13.md` — not
  attributable.

# Guide D — `check-no-direct-rt.shs`: scope honestly, then reduce; never re-baseline

Owner: one sonnet-class agent. Follow literally. `--generate-baseline` is
FORBIDDEN in this guide.

## Measured facts (2026-09-05, this host)

- `sh scripts/check/check-no-direct-rt.shs --roots src` →
  `PASS — 16244 file(s) scanned (roots=src, src=6230), forbidden=6230, extern_decls=6459 (baseline 7776)` exit 0.
  This is EXACTLY the invocation the push-tier manifest row uses
  (`config/check/must_check_gates.sdn` row `push-no-direct-rt`), so the wired
  gate is green.
- Bare `sh scripts/check/check-no-direct-rt.shs` (default roots
  `src,examples,tools,scripts,test`) →
  `FAIL — forbidden direct rt_* count 27454 exceeds baseline 7776 (... src=6230 examples=1344 tools=14 scripts=308 test=19558)` exit 1.
  The script's own header (lines 16-20) says a baseline is only comparable to
  the `--roots` set it was recorded under. The recorded baseline is a src-only
  number; the bare run compares it to a five-root number. That comparison is
  meaningless, and a meaningless FAIL trains people to ignore the gate.
- Per-directory test debt (from `--offenders`): `test/01_unit/compiler` 2559,
  `test/01_unit/lib` 2458, `test/01_unit/app` 1157, `test/01_unit/os` 858,
  `test/03_system/feature` 780, `test/03_system/os` 737, `test/unit/lib` 554,
  `test/unit/app` 539, `test/unit/os` 423, `test/03_system/compiler` 395,
  `test/03_system/tools` 392, `test/05_perf/graphics_2d` 388.

## Change 1 — the baseline records its roots (fail-closed on mismatch)

- `scripts/check/no_direct_rt_baseline.txt`: keep line 1 as the integer (format
  rule: "a single integer, first line"). Add line 2: `roots=src`.
- `scripts/check/check-no-direct-rt.shs`: after parsing `--roots`, read line 2 of
  the baseline. If it is present and differs from the effective roots and
  `--generate-baseline` is NOT set, print
  `ERROR — nothing was checked (baseline recorded for roots=<rec>, run requested roots=<req>; pass --roots <rec> or record a separate baseline for this lane)`
  and exit 2. If line 2 is absent, treat it as `roots=src` (the value it was
  recorded under) and print a one-line WARNING naming this assumption.
- Add a selftest fixture (the script already has a fixture block): a baseline
  file with `roots=src` on line 2 run with `--roots src,test` must exit 2 with
  that message; run with `--roots src` must proceed.

This turns the red bare run into a fail-closed ERROR that names the fix. It
does not touch the 7776 number.

## Change 2 — reduction plan for `test/` (no gate change in this guide)

Do NOT create a test-roots baseline in this guide; whether to open a second,
advisory ratchet for `roots=test` is a decision for the plan owner (recorded in
`plan_remains_completion_2026-09-05.md` item D3). Your deliverable is the
mechanical replacement list:

1. `sh scripts/check/check-no-direct-rt.shs --roots test --generate-baseline` is
   FORBIDDEN. Instead run
   `sh scripts/check/check-no-direct-rt.shs --roots src --offenders build/no_direct_rt/src_offenders.txt`
   and, separately, produce the test tally with the same grep the script uses
   (`RT_RE='^[^#]*\brt_[a-z0-9_]*\('`, comment lines excluded) over `test/`.
2. For the top 12 directories above, group call sites by `rt_` symbol name and
   write `doc/08_tracking/todo/no_direct_rt_test_reduction_2026-09-05.md` with
   one table row per symbol: `symbol | count | std wrapper that already exists
   (grep src/lib for a fn whose body calls it) | wrapper missing?`.
3. A symbol whose wrapper exists is a mechanical rewrite (call the wrapper);
   list those first. A symbol with no wrapper is a `src/lib` addition and goes
   in a second table.

## Acceptance

- Bare `sh scripts/check/check-no-direct-rt.shs` → last line starts with
  `ERROR — nothing was checked (baseline recorded for roots=src` and exit 2
  (capture: `out=$(sh ...); rc=$?` — never through a pipe).
- `sh scripts/check/check-no-direct-rt.shs --roots src` → still
  `PASS — ... forbidden=6230 ... (baseline 7776)` exit 0 with the baseline file
  line 1 UNCHANGED (`git diff scripts/check/no_direct_rt_baseline.txt` shows
  only the added line 2).
- `sh scripts/check/check-no-direct-rt.shs --selftest-only` → PASS, including
  the new roots-mismatch fixture.
- The reduction doc exists, its first table is non-empty, and every row's count
  sums to the measured `test=19558` ± the delta of any commits since (state the
  measured total in the doc header).

## Checkbox rule

Tick plan items D1/D2 ONLY when the corresponding acceptance bullets hold, and
append `— verified <last stdout line>, exit <n>, <date>`.

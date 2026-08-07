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

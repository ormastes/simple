# Lane Y: the "per-file HIR cost grows 2x as the build proceeds" claim is FALSE.
# The real discriminator is WHICH module, not HOW MANY have been done. — 2026-08-24

Source data: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
(the same log Lane X used; `SIMPLE_COMPILER_PHASE_PROFILE=1`, stage-2 pure-Simple
compiler, 2026-08-20 23:53-23:57). 87 complete `phase3:hir:file:start/done`
pairs, deduplicated for the stdout+stderr doubling.

## 1. Growth curve: REFUTED

    corr(hir ms, file index)  = -0.002      (n=87)

Block means (15 files each) are 1948, 1959, 1536, 1298, **726**, 3107 ms —
non-monotone, and the *lowest* block is the second-to-last. The "~1.7 s early vs
3.4 s late" figure was block-average noise over a heavy-tailed distribution, not
a trend. There is **no growth term** in the measured window (files 0-86).

Scope: this is 87 of 614 files (14%). It refutes growth *in that window*; it
cannot prove absence of growth later — but see §4, the run never got further.

## 2. Cost is not explained by the file's own content either

    corr(hir ms, bytes)   = 0.193
    corr(hir ms, lines)   = 0.128
    corr(hir ms, funcs)   = -0.067      (NEGATIVE)
    corr(hir ms, imports) = 0.582       (confounded — see below)

Counter-examples that kill the size hypothesis outright:
`driver_pipeline_aop.spl` — 5,152 B / 128 lines / 4 funcs — **4,068 ms**.
`policy_schema.spl` — 2 imports, same import count — **153 ms**.
A 62 KB file (`driver_types.spl`) costs 5,421 ms; a 62 KB file is only 33% more
than a 5 KB one here. Per-file HIR cost is essentially independent of the file.

## 3. The real discriminator: the module's DIRECTORY

| directory | n | total ms | mean ms |
|---|---|---|---|
| `src/compiler/driver` | 33 | 105,758 | **3,205** |
| `src/compiler/backend` | 12 | 25,036 | 2,086 |
| `src/compiler/frontend` | 4 | 4,370 | 1,092 |
| `src/compiler/mir` | 8 | 6,448 | 806 |
| `src/compiler/hir` | 3 | 2,374 | 791 |
| `src/compiler/common` | 12 | 1,410 | **118** |
| `src/std/common` | 3 | 309 | 103 |

**27x** between driver-extension modules and `common` modules. 33 driver files
are 71% of all measured phase-3 time. The `imports` correlation is a confound:
driver files have both more imports and the high cost. Wildcard (`use X.*`)
count is a weaker secondary signal (0 wildcards -> 1,350 ms mean; 4 -> 3,421 ms)
and does not explain the 58 zero-wildcard files that still average 1,350 ms.

## 4. The archived run did not take 4 hours — it DIED at 4.5 minutes

Log ends mid-file 87 at `+268,949 ms` with `phase3:hir:file:start
driver_hir_pipeline_lowering.spl` and no matching `:done`, no completion line,
and no stage-3 artifact. mtime 23:57 = start 23:53 + 269 s. Whatever produced
the "~4 h" figure, it is **not** this log, and no growth after file 87 can be
inferred from it.

## 5. This confirms an already-filed open blocker

`doc/08_tracking/bug/phase3_hir_import_materialization_time_rss_2026-08-22.md`
(OPEN) names the suspected mechanism: *"rebuilding the complete imported
`CompilerDriver` method/type closure for every driver extension module."*
The per-directory table above is the first quantitative confirmation of exactly
that shape — the expensive modules are precisely the driver extension modules
that import `CompilerDriver`, and cost tracks that, not file size or position.

Predecessor (RESOLVED 2026-08-21):
`doc/08_tracking/bug/hir_phase_per_module_cost_2026-08-21.md` — full-registry
rescans in two HIR resolvers, memoized in `a865dced154`. Same defect FAMILY
(work that is O(registry) per consumer rather than per answer); the residue
measured here is the part that memoization did not remove.

## 6. Not the same defect as the lint superlinear bug

`doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`'s dominant term
was **located** on 2026-08-18 and is a de-JIT constant factor: `lint_entry.spl`
trips the seed's `should_prefer_interpreter_for_source` text-grep and pins the
whole program to the tree-walking interpreter. Stage 3 here runs a NATIVE
pure-Simple binary — no interpreter pin is possible. Different defect class.
(A minor secondary superlinear term in lint remains unlocated; it is not this.)

## 7. NOT reproduced live — stage 3 is blocked in PHASE 2, before HIR runs

Three attempts to re-measure with the finer, already-in-tree
`SIMPLE_HIR_PHASE_PROFILE=1` instrument (per module: imports / declare / enums /
functions / `other`, plus 12 `RIS_*` sub-buckets and call counters; emitted as
`[hir-prof] module=... total=...ms ...` from
`hir_phase_profile_module_end`, `src/compiler/20.hir/hir_lowering/hir_phase_profile.spl`,
default off). Binary: `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
(the exact stage-2 compiler that produced the archived log).

| run | tree | entry | outcome |
|---|---|---|---|
| 1 | current working tree | `src/app/cli/main.spl` | `phase 2 FAILED`, parse error |
| 2 | `build/bootstrap-pinned/.input-snapshot` | `bootstrap_main.spl` | rejected: `Stage4 entry must be src/app/cli/main.spl or src/app/os/main.spl` |
| 3 | `build/bootstrap-pinned/.input-snapshot` | `src/app/cli/main.spl` | `phase 2 FAILED`, **same** parse error |

The blocking error, identical in runs 1 and 3 (working tree *and* pinned
snapshot), at file 140 of 2,572 in the parse phase:

    [parser_error] src/app/office/sheets/data_ops.spl line 38:33:
      const generic arguments are not supported: a numeric literal such as
      `Tensor<i64, 2>` is not a type, and Simple has no const generic parameters.
    error: focused native-build: parse error in src/app/office/sheets/data_ops.spl

That is a separate, independent stage-3 blocker from the HIR cost this lane
targets: the deployed stage-2 compiler cannot parse `Tensor<i64, 2>` in
`src/app/office/sheets/data_ops.spl`, so **phase 3 is never entered at all** on
either tree. Zero `[hir-prof]` lines were produced. Per the evidence rule this
is UNKNOWN, not a measurement — the bucket-level attribution (which of
imports / RIS_field_dep / RIS_methods / functions carries the 27x) remains
**unmeasured**, and is the single next step that would upgrade §3 from
"confirms the filed hypothesis's shape" to "names the mechanism".

No edit was made to `src/compiler/20.hir` (lane U owns it concurrently), and no
fix was attempted: the mechanism is already filed as an OPEN blocker with a
designated investigation path (§5).

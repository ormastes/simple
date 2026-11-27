# SSA write counting scans every previously seen local

Status: FIXED in source (`b1a30d05283`, verified at release/1.0.0 tip `b99b512ada8`, 2026-11-24);
native qualification pending, so the OPEN reference required below stays.
Indexed counting repair passes seven interpreter-hosted
compiler-pass regressions; native performance and original producer
qualification remain pending.

Bug ID: `ssa_write_count_quadratic_scan_2026_10_25`.

The full05 native worker 77530 sample at 2026-10-25 21:02:06 recorded 244 of
250 samples in `var_reassign_analysis.local_count_increment`, called by
`ssa_reassigned_locals_for_blocks`. This describes that bounded sample, not
97.6% of the complete build. Evidence is the retained
`provisional-p3-future-constructor-object-20261025-05/logs/worker-77530-native-first-object.sample.txt`,
SHA256 `71737c6bd5cf7dc2a1c596ca959ad582ddf8f30d1508e317d27f6fc3bba3b68f`.
Its reported physical footprint was 40.1G (peak 41.4G), while RSS was
about 5.06 GiB; this alone does not attribute all retained memory to counting.

The only production caller accumulates parallel first-seen/count arrays and
linearly searches their local ids for each written destination. N distinct
writes therefore perform N(N-1)/2 lookup comparisons, as well as array growth.
The repair uses a function-local dictionary for counting, then scans the same
original instruction order to emit each repeated local once. It preserves
local zero, sparse ids, negative/no-write exclusions, first-definition order,
the writer classifier, and the input MIR graph.

Only the counting lookup and first-count arrays are repaired. The existing
output `.push` may still copy R repeated-local entries quadratically; no whole
pass linear bound or measured native speedup is claimed.

The single authorized gen13 diagnostic executed seven tests: seven passed,
zero failed/skipped/dropped, raw status zero. The 3 GiB/120 s process-tree guard
recorded peak RSS 612960 KiB, complete enforced observation, no observer errors,
and quiescent=1. Seed, pinned runtime artifacts, and source/spec hashes matched
before/after. Review-workspace evidence is
`build/verify/ssa-write-count-index-regression-20261025-01/`; its RSS receipt
SHA256 is `8569b8a198f33d2aec1d68ba145b1bb1b7efd32933c5bc81fe623d106f2d935c`.
This does not test native timing or repair the running Phase 2 executable.

The fixed Phase 2 executable already contains the old code. Editing compiler
source does not change that native producer. There is no supported SSA-disable
flag in its normal/bootstrapping LLVM route, and skipping SSA is not a repair.
A separately reviewed source-function split may reduce its workload temporarily.
That workaround must retain this OPEN reference until a producer containing
the counting fix emits the original unsplit CLI source's native object under
the same guarded source/runtime/provenance contract and its behavior qualifies.

## WA-S8 Verification (2026-11-26)

- **Classification:** `ROOT-FIXED+STAGE2-GATED`
- **Disposition:** Kept `src/app/io/_CliCompile/compile_targets.spl` phase-split helpers and `@workaround bug=ssa_write_count_quadratic_scan_2026_10_25` intact. The compiler root cause (`ssa_reassigned_locals_for_blocks` indexed local counting in `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`) is already fixed, but the parsed-options struct/helper (`CliNativeBuildParsedOptionsV1` / `cli_native_build_parse_options_v1`) are part of the exported surface used by `src/app/io/cli_compile.spl`, `src/app/cli/bootstrap_surface_inspection_v1.spl`, and multiple unit specs, and removing the tag requires a rebuilt native producer qualifying the unsplit CLI.
- **Verification (`SIMPLE_BINARY=wa_shared_bin/simple.exe`, build-commit `03a407dabae`, `--mode=interpreter`):**
  - `test/01_unit/compiler/mir_opt/ssa_write_count_index_spec.spl` (7/7 passed)
  - `test/01_unit/compiler/mir/wa_src_lane8_lowering_spec.spl` (4/4 passed — checks `ssa_reassigned_locals_for_blocks` on sparse/cross-block MIR locals)
  - `test/01_unit/app/devhub/wa_src_lane8_retirement_spec.spl` (5/5 passed — exercises `cli_native_build_parse_options_v1`)
  - `test/01_unit/app/native_build_xray_options_spec.spl` (6/6 passed), `test/01_unit/app/native_build_no_borrow_check_option_spec.spl` (2/2 passed)

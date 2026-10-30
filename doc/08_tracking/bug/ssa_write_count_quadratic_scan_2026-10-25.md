# SSA write counting scans every previously seen local

Status: OPEN. Indexed counting repair passes seven interpreter-hosted
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

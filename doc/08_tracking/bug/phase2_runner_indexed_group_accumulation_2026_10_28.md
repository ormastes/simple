# Native SDN group counters remain zero after indexed assignment

A native `test_run_result_sdn` result retains correct per-file and run totals,
but every derived group reports zero for passed, failed, skipped and pending.
The retained phase2 compiler drops the update for self-referential indexed assignment in
`_test_output_group_summaries`. Both `array[index] += value` and the expanded
`array[index] = array[index] + value` fail; the expanded native disassembly
computes the sum into a stack slot but contains no array setter call.

The standalone native fixture uses two interleaved files in one group and a
skip-only file in another. It requires passed=3, failed=1, skipped=4, pending=2
and done_pct=50 for the repeated group, and skipped=5 with done_pct=0 for the
group whose completion denominator is zero. Both indexed assignment forms
emit zero for all those counters and the native fixture exits 1.

Use dictionaries keyed by group for the four counters, retaining a separate
first-seen name list for output order. Compute each next count in a scalar local
then store it in a separate statement. Dictionary self-updates also fail without
that separation; ordinary dictionary stores (including initialization and the
canonical SDN record builder) retain their setter calls. The dictionary lookups
preserve aggregation without rescanning all files for every group. This is a source workaround, not a compiler repair. Remove it only after the same fixture passes
with indexed assignment on a repaired compiler. The preflight bounds and
overflow checks remain unchanged.

Build `test/fixtures/test_runner_sdn_groups/main.spl` with the selected native
compiler and run `scripts/check/check-native-sdn-groups.shs --binary PATH`.
Native evidence is retained under
`/tmp/runner-source-routes-evidence-20261028/sdn-groups-*`; this does not claim
full-runner or all-format acceptance.

Validation: the native baseline fixture fails with zero group counters; the
final scalar-read/dictionary-store implementation passes the native gate.
Final binary SHA-256:
`50c7d8ab7e06165b0302afb43d48efab21f37e5e9ae9c072382e1167c46bf055`.
The 15-module final native build completed in 12.0 seconds with the retained
pure-Simple phase2 compiler. The gate also rejects a zero-exit binary that
omits its required regression summary.

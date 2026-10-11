# Retired test module imports in Phase 1 specs

Seventeen retained specs import std.test, which has no module in current
release. The canonical assertion module is std.spec. Replace only that import;
all original assertions and fixtures remain unchanged.

This first completed source-repair slice contains five complete cached diagnostic
passes: stdio_dispatch (1/1), builder_default_parser (2/2), ARM32 page-table
owner (7/7), process artifact grant (3/3), and core payload gap (4/4). Total 17
executed, 17 passed, zero failed/skipped/dropped. No production files changed.

The complete 17-spec diagnostic collection executes 90 examples: 60 passed,
30 failed. Twelve other specs retain real source-contract or behavior failures;
they are kept in a separate unfinished repair slice, not discarded or weakened.
The current actor ABI baseline fails before execution with Cannot resolve
module: std.test. The changed import clears that prerequisite and exposes a
remaining actor-hook contract mismatch. No broad backlog closure is inferred.

The first sparse-worktree launch also failed to locate std.spec. The collector
then used copied exact spec bytes in its external artifact directory, with the
retained library closure and current release source-contract files as cwd.
No passing check was replayed. Producer SHA256 is
15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.
Evidence: build/phase1-test-imports-20261011/CLOSURE_SUMMARY.json and per-case
logs, exact spec hashes, original failure receipts, and selected.json.

This is cached bootstrap source-repair evidence; imported implementation
closure and admitted pure runtime/native qualification are not established.
There were no compiler rebuilds, source assertion changes, or cache deletions.
The global 4,758-row historical queue remains unchanged.

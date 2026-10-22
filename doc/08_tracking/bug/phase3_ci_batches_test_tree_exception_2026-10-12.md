# CI conflict-tree batching: existing test-tree divergence

The exact delta helper checked release base
`7cc35f0db1518fa8a02976183d6c870e63348bed` and CI repair
`901b33df5e53f36ae7e6d63e6a295155255a8fb8`. It reports 3155 existing
offenders, zero introduced, and identical full guard failures: 3821 diverged
against 965 baseline entries, 2985 new-relative-to-baseline, 129 stale baseline
entries, and 42 mirror-only paths including 41 unallowlisted.

The complete helper-produced list is retained in
`phase3_ci_batches_preexisting_test_tree_offenders_2026-10-12.txt`, SHA256
`599b51f0edf92ecdb900dd4d55efba54ef806ff683cc98d656ebfd0308b700d6`.
Neither baseline nor allowlist changed. This uses the existing zero-new-offender
exception in `.claude/rules/vcs.md`; it does not make the full guard green.

Actual logs are retained in
`C:/dev/simple-phase3-mcp-receiver-evidence/conflict-tree-batches/`:
`support-test-tree-delta.log`, `support-tree.log`, `support-markers.log`,
`support-size.log`, and `support-api.log`. All four focused push guards passed.
The broad push-tier run exceeded its budget while selecting unrelated advisory
rows and remains ERROR in `support-pr-push-gates.log`; it is not PASS evidence.
Required remote checks and review remain mandatory before this repair lands.

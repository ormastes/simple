# command_dispatch: two migrated app dispatch targets missing on disk (2026-08-12)

**Status:** OPEN — real drift, deliberately left RED in the spec.

`test/01_unit/app/tooling/command_dispatch_spec.spl` documented 12 commands as
migrated to Simple apps dispatched at `src/app/<tool>/main.spl`, but its
"Simple app files exist" describe only asserted string literals' prefixes and
suffixes against themselves — a fake gate that could never fail. Rewritten
2026-08-12 to check the real filesystem via `rt_file_exists_str` (same idiom as
`test/01_unit/app/cli/cli_migration_spec.spl`). An earlier session's fake-gate
sweep reported this same rewrite and RED result, but that work never reached a
landed commit (`62494425ed4` fixed `cli_help_alignment_spec.spl` instead); this
re-does and lands it.

## Real failures exposed (2 of 12)

- `src/app/formatter/` — directory does not exist at all.
- `src/app/depgraph/` — exists but has no `main.spl`.

Spec result: `Results: 111 total, 109 passed, 2 failed` — the 2 failures are
these, and they must stay RED until either the apps are created at the
documented dispatch paths or the dispatch documentation/spec list is corrected
to the real target paths (whichever the CLI dispatch code actually uses —
check `src/app/cli` dispatch tables before "fixing" by deletion).

Per `.claude/rules/testing.md`: a correct spec that fails is a legitimate
artifact; do not weaken the assertion or mark it pending.

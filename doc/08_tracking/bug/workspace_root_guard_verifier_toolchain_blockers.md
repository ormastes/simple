# Workspace Root Guard Verifier Toolchain Blockers

Status: Both runtime crashes are gone. `bin/simple lint` and `bin/simple fmt` run

## Status: RESOLVED (2026-05-29)

Both runtime crashes are gone. `bin/simple lint` and `bin/simple fmt` run
without crashing. The follow-up check gates can now be used normally.

## Summary

While verifying `workspace_root_write_guard`, the global lint/format/check
tooling failed on both changed and unrelated files. The failures reproduced
outside the workspace root guard path and appeared to predate this feature.

## Original Evidence (now resolved)

`bin/simple lint src/app/io/cli_ops.spl` — previously crashed:

```text
Runtime error: Function 'line' not found
```

Now produces structured lint output (warnings and errors) without crashing.
Likely fix: `src/compiler/90.tools/lint/main_part2.spl` EasyFix field access
was repaired; `fix_reps[0].line` resolves correctly.

`bin/simple fmt src/app/io/cli_ops.spl --check` — previously crashed:

```text
Runtime error: Function 'extend' not found
FAIL src/app/io/cli_ops.spl needs formatting
```

Now reports `src/app/io/cli_ops.spl: needs formatting` without a runtime error.
The formatter uses `.push()` throughout; no `.extend()` call present in current
`src/compiler/90.tools/formatter/main.spl`.

Same resolution confirmed for `src/lib/nogc_sync_mut/src/set.spl`.

## Current State

- `bin/simple lint <file>` — working; emits structured warnings/errors
- `bin/simple fmt <file> --check` — working; reports formatting status cleanly
- `bin/simple check` — unblocked for use as a verification gate

## Remaining Work

Rerun broad `bin/simple check` gates over the changed `app/io` and
`lib/nogc_sync_mut` paths to confirm workspace root guard verification is
complete.

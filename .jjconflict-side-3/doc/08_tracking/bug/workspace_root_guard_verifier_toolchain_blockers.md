# Workspace Root Guard Verifier Toolchain Blockers

## Summary

While verifying `workspace_root_write_guard`, the global lint/format/check
tooling failed on both changed and unrelated files. The failures reproduce
outside the workspace root guard path and appear to predate this feature.

## Evidence

`bin/simple lint src/app/io/cli_ops.spl`:

```text
Runtime error: Function 'line' not found
```

`bin/simple lint src/lib/nogc_sync_mut/src/set.spl`:

```text
Runtime error: Function 'line' not found
```

Likely source: `src/compiler/90.tools/lint/main_part2.spl` reads
`fix_reps[0].line`, but runtime resolves the field access as a missing function.

`bin/simple fmt src/app/io/cli_ops.spl --check`:

```text
Runtime error: Function 'extend' not found
FAIL src/app/io/cli_ops.spl needs formatting
```

`bin/simple fmt src/lib/nogc_sync_mut/src/set.spl --check`:

```text
Runtime error: Function 'extend' not found
FAIL src/lib/nogc_sync_mut/src/set.spl needs formatting
```

Likely source: `src/compiler/90.tools/formatter/main.spl` calls
`result.extend(code)`.

## Impact

`bin/simple check ...` cannot currently be used as decisive evidence for this
feature because it enters the same failing lint/format path and then may hang in
the test phase.

## Follow-Up

Repair formatter array extension support and linter EasyFix replacement field
access, then rerun the broad `bin/simple check` gates for the changed app/lib
paths.

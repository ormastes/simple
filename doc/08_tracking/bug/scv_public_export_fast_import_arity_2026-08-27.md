# scv public-export: arity mismatch on scv_export_git_fast_import (FIXED)

Date: 2026-08-27
Status: FIXED
Class: (b) real product bug — incomplete signature migration
Found by: root-causing long-standing RED `test/integration/app/scv_gates_spec.spl` (4/10)

## Symptom
Every `scv public-export` invocation aborted with a *compile-time* error:

    error: semantic: function expects argument for parameter 'since', but none was provided

`scv_gates_spec.spl` failed 6 of 10 examples; each failing example's actual
output ended in `exit=1` where the spec asserted `exit=0`. The error text
appeared exactly 6 times in the run log — one per failing example.

## Root cause
`src/lib/scv/fast_import.spl:217` declares

    fn scv_export_git_fast_import(root: text, stream_path: text, branch: text, since: text) -> text

The `since` parameter was added when incremental export landed. Two call sites
exist. `src/app/scv/main.spl:293` was updated (it threads `export_since` from
`--since`). `src/lib/scv/public_remote.spl:61` was NOT, and still passed three
arguments. Because the whole scv app is compiled per invocation, the unresolved
call is a hard semantic error, so the command never ran at all.

## Fix
`src/lib/scv/public_remote.spl:61` now passes `""` for `since`. Empty `since` is
the "no lower bound / export full DAG" value already used as the default in
`main.spl:280` and honoured by `scv_export_dag_commits`. A public export is by
definition a full export, so `""` is the semantically correct argument, not a
placeholder.

## Notes
No behaviour change to any path that already compiled; this only restores a path
that could never execute.

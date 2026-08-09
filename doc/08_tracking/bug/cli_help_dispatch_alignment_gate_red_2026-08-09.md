# `cli_help_alignment_spec` is RED — help text and dispatch have drifted by 18 commands

Date: 2026-08-09
Status: OPEN — pre-existing, not caused by the change that found it.
Severity: medium. The gate that is supposed to keep `simple --help` honest is
itself failing, so help/dispatch drift is currently unpoliced.

## Symptom

`bin/simple run test/01_unit/app/cli_help_alignment_spec.spl`

```
declared>=15 executed=15 passed=10 failed=5   exit 1
```

The five failures:

| example | failure |
|---|---|
| `check-capsule from help exists in dispatch` | `expected false to equal true` — help advertises a command the dispatcher does not handle |
| `help command count matches dispatch command count for visible commands` | `expected 33 to equal 51` — an 18-command gap |
| `every dispatch command has help text or is tagged experimental` | `semantic: cannot call mutating method 'push' on immutable array 'missing_from_help_non_experimental'` — the spec itself cannot run to completion |
| `verify is shown in help with experimental tag` | `expected simple verify <file.spl>    Run formal verification to contain [experimental]` |
| `gen-lean is shown in help with experimental tag` | `expected simple gen-lean generate    Generate Lean verification files to contain [experimental]` |

Note the third failure is a **defect in the spec**, not in the CLI: it declares
`missing_from_help_non_experimental` with `val` and then calls `.push` on it.
That example can never pass and never could, so the "every dispatch command has
help text" invariant has never actually been enforced.

## Proof it is pre-existing

Found while adding a `counterpart` subcommand to
`src/app/cli/_CliMain/main_and_help.spl`. Isolated by removing exactly the three
added lines (the `use app.counterpart.main.{counterpart_main}` import and the
two-line `elif` branch) from the current file and re-running:

```
without the counterpart lines: declared>=15 executed=15 passed=10 failed=5  exit 1
with    the counterpart lines: declared>=15 executed=15 passed=10 failed=5  exit 1
```

Byte-identical failure set, and the 33-vs-51 counts are unchanged, so the new
subcommand contributes nothing to the gap. The file was restored byte-exactly
afterwards (`git hash-object` matched, `git status` clean).

## Unblock condition

1. Fix the `val` → `var` defect on `missing_from_help_non_experimental` so the
   third example can actually execute; expect it to then report the real list of
   dispatch commands missing help text.
2. Reconcile the 18-command gap between `print_cli_help()` and the dispatcher —
   either add help entries or tag the commands experimental/hidden.
3. Remove `check-capsule` from help, or implement its dispatch branch.
4. Restore the `[experimental]` tags on `verify` and `gen-lean`.

Until (1) is fixed, treat a green run of this spec as meaningless for the
"dispatch has help text" invariant — the check is fail-open.

## Related

- The sibling `surface_alignment_spec` (28/28) and `inventory_drift_spec` (9/9)
  are green, so the command registry itself is consistent; the drift is
  specifically between help text and the dispatcher.
- `src/app/cli/_CliMain/main_and_help.spl` — dispatcher
- `src/app/cli/cli_helpers.spl` — `print_cli_help`

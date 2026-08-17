# `cli_help_alignment_spec` is RED — help text and dispatch have drifted by 18 commands

Date: 2026-08-09
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
the unblock condition (the `val`/`push` spec defect) is FIXED as of 2026-08-10;
items 2-4 (the real 25-command help/dispatch gap, `check-capsule`, and the
`verify`/`gen-lean` experimental tags) remain open and are CLI-surface work,
not a test-repair fix.
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

## Re-verify 2026-08-10 — item 1 FIXED, real gap now measured

`val missing_from_help_non_experimental: [text] = []` in
`test/01_unit/app/cli_help_alignment_spec.spl:197` was changed to `var` (the
array is `.push`ed in the loop below it, which requires a mutable binding).
Re-ran `bin/simple run test/01_unit/app/cli_help_alignment_spec.spl`:

```
declared>=15 executed=15 passed=10 failed=5   exit 1
```

Same pass/fail count as before (the spec-defect failure is replaced by a real
one), but the third example now actually executes and reports the true gap:

```
✗ every dispatch command has help text or is tagged experimental
  expected 25 to equal 0
```

i.e. 25 dispatch-only commands lack help text or an experimental tag (larger
than the 18 estimated from the count mismatch). The other four failures
(`check-capsule`, the 33-vs-51 count, and the `verify`/`gen-lean` experimental
tags) are unchanged and still require real CLI-surface changes to
`src/app/cli/_CliMain/main_and_help.spl` / `src/app/cli/cli_helpers.spl` —
out of scope for this pass; left OPEN.

## Unblock condition

1. ~~Fix the `val` → `var` defect on `missing_from_help_non_experimental` so the
   third example can actually execute; expect it to then report the real list of
   dispatch commands missing help text.~~ DONE 2026-08-10.
2. Reconcile the 18-command gap between `print_cli_help()` and the dispatcher —
   either add help entries or tag the commands experimental/hidden.
3. Remove `check-capsule` from help, or implement its dispatch branch.
4. Restore the `[experimental]` tags on `verify` and `gen-lean`.

Until (1) is fixed, treat a green run of this spec as meaningless for the
"dispatch has help text" invariant — the check is fail-open.

## Duplication census 2026-08-11 — there are FOUR hand-maintained registries, and one dispatcher is dead code

The framing above ("help text vs the dispatcher") understates the problem: the
command list is written out by hand in four places, none of which derives from
another. Counts measured on this date:

| # | source of truth | accessor | commands | read at runtime? |
|---|---|---|---|---|
| 1 | `src/app/cli/_CliMain/main_and_help.spl` | `elif str_eq(first, "...")` chain from :253 | ~90 branches | **YES — this is the only executing dispatch** |
| 2 | `src/app/cli/cli_helpers.spl` | `print_cli_help()` :22 | 60 | YES (help output only) |
| 3 | `src/app/cli/dispatch/table.spl` | `get_command_table()` :12 | 84 | NO |
| 4 | `src/app/cli/surface_alignment.spl` | `all_cli_commands()` :24 | classification list | NO |
| 5 | `src/app/cli/bootstrap_check.spl` | inline array :350 | subset | NO (bootstrap check only) |

Set differences between (2) and (3): 44 table commands absent from help
(`bench bug-add bug-gen bug-resolve check-skip clean context dashboard debug
deps electron feature-doc feature-gen fix game itf jupyter-kernel
llm-process-gen model3d native-build play process publish qemu qualify-ignore
record release repl run scv search security sound spec-coverage spec-gen
spipe-process-harness spritesheet task-gen todo-gen todo-scan var vscode web`),
and 14 help commands absent from the table (`check-arch doc-coverage ide jj lex
mem office plugin sbom stats t32 test-daemon ui update`).

### `src/app/cli/dispatch.spl` is shadowed dead code (measured, not inferred)

`src/app/cli/dispatch.spl` (150 lines) and `src/app/cli/dispatch/__init__.spl`
(32 lines) both claim the import path `app.cli.dispatch` and both define
`find_command`, `command_count`, `simple_impl_count`, `coverage_percentage`.
Which one wins was measured by sabotage rather than assumed: changing
`command_count()` in `dispatch/__init__.spl` to return `-12345` and re-running
`bin/simple test test/02_integration/app/cli_dispatch_spec.spl` moved it from
`Results: 6 total, 6 passed` to `Results: 6 total, 4 passed, 2 failed` with
`expected -12345 to be greater than 80`. So **`dispatch/__init__.spl` shadows
`dispatch.spl` entirely**; `dispatch.spl`'s unique symbols (`dispatch_command`,
`try_simple_app`, `dispatch_to_rust`, `print_dispatch_stats`) are unreachable —
`/usr/bin/grep -rn 'find_command\|dispatch_command\|app\.cli\.dispatch' src/`
returns no production caller outside the `dispatch/` directory itself, only a
re-export line at `src/app/cli/__init__.spl:42`.

Deleting `dispatch.spl` was deliberately NOT done in this pass: it is a
published API surface with a committed baseline
(`doc/08_tracking/api_surface/baseline.sdn:20-24` lists the module and its
symbols by name), its header declares it the in-progress landing pad for the
`rust/driver/src/main.rs` migration, and validating a CLI-surface deletion needs
a bootstrap that the host could not afford. Recorded here instead of stepped
over silently.

### Why `surface_alignment_spec` being green proves nothing

`surface_alignment.spl` is registry (4) — a hand-written classification list
that no production code path reads (it declares no `export` statements at all;
its only referents are its own specs). Its specs compare that list against
itself, so "the command registry itself is consistent" above should be read as
"one of the five hand-written lists agrees with the spec that hard-codes it".

### `cli_help_alignment_spec` cannot be fixed by changing the CLI

Every assertion in `test/01_unit/app/cli_help_alignment_spec.spl` compares
hard-coded literals against hard-coded literals — e.g. :182
`expect(visible_help_count).to_equal(visible_from_dispatch)` where both sides
are literals declared four lines above (`33` vs `56 - 5`). The spec never reads
`cli_helpers.spl` or the dispatcher, so **no source change can turn it green**;
only editing the spec's own constants can, which would be weakening it. Any
real fix must first replace it with an oracle that parses the two sources.
This supersedes unblock item 2's implicit assumption that adding help entries
would move the gate.

## Related

- The sibling `surface_alignment_spec` (28/28) and `inventory_drift_spec` (9/9)
  are green, so the command registry itself is consistent; the drift is
  specifically between help text and the dispatcher.
  (Superseded — see the 2026-08-11 census above: those specs hard-code the list
  they check.)
- `src/app/cli/_CliMain/main_and_help.spl` — dispatcher
- `src/app/cli/cli_helpers.spl` — `print_cli_help`
- `src/app/cli/dispatch.spl`, `src/app/cli/dispatch/__init__.spl` — the shadowed pair
- `src/app/cli/surface_alignment.spl`, `src/app/cli/bootstrap_check.spl` — registries 4 and 5

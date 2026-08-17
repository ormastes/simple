> **Owner decision is consolidated in
> `app_interpreter_deletion_evidence_package_2026-08-11.md` section 0**
> (re-measured 2026-08-17: 100 files on disk, 99 tracked, 1.1 MB, 25,232 lines,
> 62/99 using `from X import`, **zero** external `use app.interpreter` imports).
> This doc remains the original diagnosis. No deletion performed.

# `src/app/interpreter/` is declared REMOVED but is still on disk and still compiled

**Status:** OPEN — filed rather than half-migrated
**Date:** 2026-08-10
**Supersedes the diagnosis in:** `88b3874cd51`, and the header comment in
`test/01_unit/lib/nogc_async_mut/generator_intensive_spec.spl` (+ its `test/unit/` twin)

## Summary

The goal was to make
`use app.interpreter.async_runtime.generators.GeneratorState` importable by
migrating the sibling `actors.spl` off `static mut` / `unsafe { }`.

That goal is **not reachable by any change to `actors.spl`**, and the target
package is one the repo has already declared deleted. Two independent findings,
both measured:

### Finding 1 — removing the eager import does NOT decouple

`__init__.spl` was edited to drop `from actors import {...}` and the matching
`export` line. The probe still failed with the *same* parse error:

```
error: compile failed: parse: in ".../async_runtime/actors.spl":
  Syntax error at 59:19: reserved keyword 'actor' cannot be used as a parameter name
```

The compiler compiles **every `.spl` in the package directory**, not just the
ones `__init__.spl` imports. So the "decouple by unwiring the import" option
does not exist for this package. Any fix must remove the file from disk or make
it parse.

### Finding 2 — the whole package is un-buildable, and officially removed

With `actors.spl` moved aside entirely, the probe advanced exactly one step and
failed again:

```
 18 | from mailbox import {Mailbox, MailboxConfig, MessageRef, ...}
error: semantic: variable `from` not found
    Use 'use module.{...}' instead
```

The package uses the legacy Python-shaped `from X import {...}` form throughout;
the compiler rejects it semantically. 61 of the 99 files under
`src/app/interpreter/` use that form. `actors.spl` was never the blocker — it
was merely the *first* blocker.

And the tree is already declared gone:

- `src/app/__init__.spl:33` — ``` `app.interpreter` - REMOVED. Use
  `core.interpreter` instead ```
- `src/compiler/10.frontend/core/interpreter/mod.spl:21` — "**Legacy
  Interpreter (DELETED 2026-02-10)** … Location: `src/app/interpreter/`
  (removed)"

The 99 files were never actually deleted from disk.

## What `actors.spl`'s global registry does

For the record, since the migrate option was evaluated and rejected:

- `static mut NEXT_ACTOR_ID: u64` — monotonic id allocator, bumped in `eval_spawn`.
- `static mut ACTOR_REGISTRY: Dict<u64, Actor>` — process-global live-actor map;
  `register_actor` / `unregister_actor` / `get_actor` insert, remove, look up;
  `process_all_actors` iterates it and drains up to 10 messages per actor per tick.

Migration was rejected because the module is not a near-miss. It also depends on
`Channel<T>`, `Box<T>`, `Duration`, `Expr`, `MatchArm`, and
`interp.current_actor()` — none of which exist as reachable Simple types here.
Rewriting it onto `src/lib/nogc_async_mut` actor/mailbox primitives is writing a
new module from scratch, i.e. exactly the "substantial new concurrency design"
that the standing instruction says to file rather than attempt.

## Why it is dead code (evidence that ruled out migrate)

- The live `eval_spawn` the interpreter actually dispatches to is
  `src/app/interpreter/expr/advanced.spl:181`, re-exported via
  `src/app/interpreter/expr/__init__.spl:13,27` and called at `:119`.
  `actors.spl`'s `eval_spawn` is a dead duplicate.
- The only importers of the `async_runtime` package are
  `src/app/interpreter/perf/__init__.spl:36` and
  `src/app/interpreter/perf/perf_config.spl:6` — both in the same removed tree,
  and both import **only** heap/mailbox/scheduler names, never
  `Actor` / `eval_spawn` / `eval_send` / `eval_receive`.
- No file outside `src/app/interpreter/` imports the package at all.

## Why deletion was not done here either

Deleting `actors.spl` alone changes nothing (Finding 2). Deleting the whole
99-file `src/app/interpreter/` tree is the disposition the two source comments
above already imply is correct — but that is a repo-wide removal well outside
the scope of "migrate one file", and it needs its own reviewed change. Filed as
the follow-up below rather than performed unilaterally.

## Consequence for the spec mirror

`test/01_unit/lib/nogc_async_mut/generator_intensive_spec.spl` and its
`test/unit/` twin must **keep** their mirrored `GeneratorState` enum. The real
import cannot be switched on. Their header comments have been corrected: the
previously-stated reason (`actors.spl`'s `static mut`/`unsafe`) is wrong and was
only the first of many blockers.

## Follow-up

TODO: decide the fate of the 99-file `src/app/interpreter/` tree as its own
change — either delete it (matching `src/app/__init__.spl:33` and
`core/interpreter/mod.spl:21`, which both already say it is gone) or, if any of
it is still wanted, migrate the package off `from X import {...}` wholesale.
Until then no symbol in that tree is importable, and specs must not claim
otherwise.

## Measurement

- Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 181524312 bytes,
  mtime 2026-08-10 11:06:25 UTC. Not relinked or rebuilt.
- Oracle: `bin/simple test <relative spec path>` (not `run` — `run` does not
  enforce the reserved-keyword rule). Every claim above is backed by a printed
  verdict line, not by exit status.

## 2026-08-17 re-verification — unchanged; awaiting the repo owner's decision

`git ls-files src/app/interpreter/ | wc -l` still returns **99**. Nothing about
the diagnosis has changed. This is not a defect a triage lane can close: the
deletion is a scoped, reviewed change that removes 99 tracked files, and the
prior doc explicitly reserves that decision for the repo owner. Deleting them
here would also collide with the `check-tree-size-push.shs` load-bearing-path
and file-count gates, which is exactly the review those gates exist to force.
Status OPEN, owner-gated, no code change.

## 2026-08-17 — RESOLVED: tree deleted, with the uniqueness check finally done

User approval to delete was given explicitly (deleting an app tree is an owner
decision). The evidence package's outstanding item — **file-by-file uniqueness
across all 99 tracked files** — was run first, by declared-symbol name against
all **36,120** other tracked `.spl` files, not by filename:

- **864** symbols declared in the tree; **358** are also declared elsewhere.
- Of the **506** declared ONLY here, only **94** appear as an identifier
  anywhere outside; **25** of those are methods (`me`) declared outside,
  leaving **69**.
- Those 69 are namesakes or generic tokens (`bool`, `int`, `float`, `string`,
  `dict`, `tuple`, `ref`, `address`, `cycle`) or type names with independent,
  complete implementations elsewhere: `PersistentVec` →
  `src/lib/nogc_async_immut/persistent_vec/`, `CopyStrategy` →
  `src/lib/*/message_transfer.spl`, `PerfProfile` → `src/lib/*/perf.spl`,
  `Interpreter` → `src/app/cli/`, `MatchCase`/`Statement`/`BinaryOp`/`Generator`
  → the compiler and other trees. `LazySeq`'s only outside occurrence is a
  `pending_reason` string inside a pending stub spec.
- The watchdog/execution API names (`start_watchdog`, `stop_watchdog`,
  `check_timeout`, `check_execution_limit`, `reset_execution_count`,
  `run_script`, `evaluate_module`) were checked one by one: every outside hit is
  a comment, a string literal, or an unrelated namesake.

**Verdict: no file was the sole implementation of live functionality.**
Corroborated independently — the tree does not parse:
`bin/simple run src/app/interpreter/main.spl` exits 1 with
`parse: in ".../ast_convert.spl": Unexpected token: expected pattern, found Indent`.
Nothing in it could have been live.

Deleted: 99 tracked files, 25,232 lines, 1.1 MB, plus one gitignored
`.simple/logs/` residue directory (the 100th on-disk file).
Recoverable from `ae55a7467197350bdf8b91c48444c167219ce8bb`, the last commit
that touched the tree. Exact file list preserved at
`doc/08_tracking/bug/app_interpreter_deleted_file_list_2026-08-17.txt`.

### The 14 in-tree `_spec.spl` files
12 have live counterparts under `test/01_unit/app/interpreter/` — which is a
**namesake test tree**, importing only `std.*` and `app.io`, never
`app.interpreter`, so it tests the stdlib equivalents and is unaffected. The 2
without a counterpart (`mailbox_spec.spl`, `control_flow_spec.spl`) test only
tree-internal code (`from mailbox import {...}`, and
`eval_for`/`eval_while`/`eval_loop`/`eval_if`/`eval_match`): they have no
subject left, and could not run anyway.

### Prevention
`scripts/check/check-removed-trees-absent.shs` — scans every
`src/**/__init__.spl` for a removal declaration (`` `a.b.c` - REMOVED ``, also
`DELETED`) and fails if `src/a/b/c` still holds files. Tree check, not a range
check, since a commit that edits only the `__init__.spl` can introduce the
contradiction without touching the tree it names. `--selftest` (6 fixtures) runs
before every scan and is fatal; fixture 1 replays this exact incident and must
FAIL. Verdict convention matches the pre-push guards: `PASS — <n> declaration(s)
checked, 0 still on disk` / `FAIL` exit 1 / `ERROR — nothing was checked` exit 2,
with a 0-declaration run always ERROR. Measured on this tree after the deletion:
`PASS — 1 declaration(s) checked, 0 still on disk`.

Status: RESOLVED.

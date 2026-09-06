# Five real compiler/interpreter contract gaps found while modernizing the integration scaffold

Date: 2026-09-06
Status: open
Severity: P3 (each is a real but narrow correctness/diagnostics gap, not a crash)
Location: found via
`test/02_integration/compiler/compiler_interpreter_integration_spec.spl`,
which used to be 25 `pass`-only scaffolds (`# TODO: Implement when parser
integration complete`) with zero real assertions (scorer blocker
`SSDOC-ORA-001`). Converting them into real subprocess-based integration
tests (each scenario writes a small fixture `.spl` program and runs it
through `src/compiler_rust/target/bootstrap/simple run <file>`) surfaced 5
genuine, previously-undocumented gaps between the scaffold's original
intent and current pipeline behavior. All 5 are left legitimately RED in
the spec (never weakened) with a `# NOTE:` at each site citing this record.

## 1. No ambiguous-method-call detection

Two `impl Box:` blocks each defining a zero-arg `fn get() -> i64` compile
and run without any diagnostic. The call silently resolves to the LAST
definition (confirmed: a `Box(v: 10)` prints `11`, from the second impl's
`self.v + 1`, not `10` from the first). This matches the
`compiler_cross_module_private_symbol_collision` JIT `$dupN`-fallback
warning already printed by every subprocess invocation elsewhere in this
repo, but there is no compile-time or run-time error surfaced for the
in-file case. Repro: scenario "detects ambiguous method calls".

## 2. No static enforcement of an annotated type against a literal initializer

`val x: i64 = "not a number"` compiles and runs with exit 0, printing the
string unchanged. The `i64` annotation is not checked against the text
literal initializer on this path. Repro: scenario "propagates type errors
correctly".

## 3. Diagnostics carry no line/column (source span) information

A division-by-zero on line 3 of a 3-line fixture produces
`error[E2001]: division by zero` with a `help:` line, but neither stdout
nor stderr contains any `line 3` (or other line/column) reference. Repro:
scenario "provides error location information".

## 4. No export-visibility enforcement across module boundaries

A function that is never `export`ed (e.g. `fn _secret_add(...)`, no
trailing `export` statement) is still importable and callable from another
module via `use mod.{_secret_add}` -- exit 0, prints the computed result.
Private/unexported symbols are not hidden from importers on this path.
Repro: scenario "enforces export visibility".

## 5. No circular-import detection

Two modules that `use` each other's top-level `val` (module A imports B's
`b_val`, module B imports A's `a_val`) compile and run without any
diagnostic. Repro: scenario "detects circular dependencies".

## Measurement note (folded into this record, not filed separately)

While investigating gaps 4/5's siblings ("handles reference counting
correctly", "detects memory leaks"), an early absence-check used plain
`grep -rl "fn refcount\|fn ref_count(" src/lib` (no `-E`) and silently
returned no matches -- a BSD-grep alternation-syntax false negative,
exactly the class of trap `.claude/rules/testing.md` warns about ("never
A/B across two grep invocations with different flags"). Rerunning with
`-E` found real, narrowly-scoped APIs: `fn refcount(fd: u32) -> u32` in
`src/lib/nogc_sync_mut/fs/nvfs_posix/fd_table.spl:70` (POSIX fd-table
refcounts, not general heap objects) and `fn leak_checkpoint(name: text,
snapshot_id: i64) -> LeakCheckpoint` in
`src/lib/nogc_sync_mut/sanitizer/lsan/types.spl:8` (LSan checkpoint
infrastructure). Both scenarios were corrected in the spec to assert the
real (scoped) presence of these APIs rather than a blanket absence, using
a live `grep -E` executed by the scenario itself rather than a hardcoded
literal, before this record was filed.

## Fix

Each of the 5 gaps needs its own investigation and fix in the relevant
compiler/interpreter stage (symbol resolution, type checking, diagnostics
span tracking, module visibility, module graph construction respectively);
none was attempted here, this is a test-file-only modernization batch. The
spec scenarios above are the reproduction fixtures for each.

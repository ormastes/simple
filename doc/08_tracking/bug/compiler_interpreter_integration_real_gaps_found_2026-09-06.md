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

## 2026-11-10 P3 triage (work/p3-interp-20261110) — all 5 gaps confirmed LIVE; out of interpreter lane

Each gap re-reproduced on the deployed Windows Rust seed (worktree
`bin/simple.exe`, fixtures under `build/p3fix/gap4/`):

1. Ambiguous zero-arg `get()` across two `impl Box` blocks: no diagnostic;
   silent resolution prints `10` (first impl wins on this build; either way
   ambiguous). LIVE.
2. `val x: i64 = "not a number"` compiles and runs exit 0, printing
   `6207503407825` — a raw pointer/bits reinterpretation, i.e. silent
   mis-coercion, worse than the original note ("prints the string"). LIVE.
3. `print(10 / 0)` (line 3): process dies `Illegal instruction` (exit 132)
   with NO diagnostic at all on this host — no E2001, no span. LIVE; on
   Windows strictly worse than "no line/column".
4. Non-exported `fn _secret_add` imported via `use secret_mod.{_secret_add}`
   from another module: exit 0, prints `5`. LIVE.
5. Circular `use` between moda/modb over top-level vals: exit 0, prints `3`,
   no diagnostic. LIVE.

All five fixes live in the compiler frontend (symbol resolution, type
checking, diagnostics span tracking, module visibility, module graph) —
`src/compiler/**` or the seed compiler frontend, both outside the P3
interpreter lane's write scope. Routing to the compiler/compiler-seed lanes;
no code change attempted here.

## 2026-11-10 P3 triage (work/p3-interp2-20261110) — independently confirmed LIVE; out of lane

Second-lane spot re-verification on the same deployed Windows Rust seed
(worktree `bin/simple.exe`): gap 2 (`val x: i64 = "not a number"`)
still compiles and runs exit 0, printing a raw pointer/bits value
(`3854699993329`), i.e. silent mis-coercion unchanged from the
work/p3-interp-20261110 note above. All five gaps remain owned by the
compiler frontend (`src/compiler/**`, src/compiler_rust) — outside this
lane's write scope. Concur with routing to the compiler lanes; no code
change here.


## 2026-11-11 P3 triage (work/p3-interp7-20261111) — gaps 1+2 FIXED on the fresh seed; gaps 3/4/5 remain LIVE (out of lane)

Third-lane re-verification on the fresh seed (worktree `bin/simple.exe`,
build-commit `46fe8f6b6def`; minimal fixtures under `build/p3fix-interp7/`):

1. Ambiguous zero-arg `get()` across two `impl Box` blocks: NOW A HARD ERROR —
   `error: semantic: duplicate method `get` in `impl` blocks of the same type
   (the same signature is defined twice)`, exit 1 (JIT HIR lowering also
   rejects it before any interpreter fallback). FIXED. Both new diagnostics
   originate in `src/compiler_rust/compiler/src/impl_duplicate_check.rs`,
   introduced by PR #7597 (`9e7e7a526edb`, in branch ancestry).
2. `val x: i64 = "not a number"`: NOW A HARD ERROR — `error: semantic: type
   mismatch: cannot initialize `i64` binding with a text literal`, exit 1.
   FIXED (same PR #7597 file). The silent mis-coercion reported by both
   2026-11-10 lanes is gone on this seed.
3. `print(10 / 0)` (line 3 of the fixture): process still dies `Illegal
   instruction` (exit 132) after printing `2`, with NO diagnostic and no
   line/column. LIVE, unchanged on this host.
4. Non-exported `fn _secret_add` imported via `use secret_mod.{_secret_add}`:
   exit 0, prints `5`. LIVE, unchanged.
5. Circular `use` between moda/modb over top-level vals: exit 0, prints `3`,
   no diagnostic. LIVE, unchanged.

Note: the tracked spec
`test/02_integration/compiler/compiler_interpreter_integration_spec.spl`
drives its scenarios through `src/compiler_rust/target/bootstrap/simple`,
which does not exist in this worktree (no cargo build permitted in this lane),
so its scenario verdicts were not refreshed here; the fixture repros above
against `bin/simple.exe` are this lane's evidence. Gaps 3 (div-zero span
diagnostics), 4 (export visibility), 5 (circular-import detection) remain
owned by the compiler frontend (`src/compiler/**`, `src/compiler_rust`) —
outside this lane's write scope; routing to the compiler/compiler-seed lanes
stands. Status stays OPEN (partial closure only).

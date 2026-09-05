# Stage 4 streaming AST mode slot reclaimed between files

## Status

Claimed from a native debugger trace on 2026-08-04.

## Reproduction

The retained LLVM 23.1 Stage 3 compiler completed the 1,726-source closure,
released the first streaming module surface, and crashed while initializing
the second parser.  The debugger stack is retained at
`build/focused/stage4-first-surface-gdb/gdb.log`:

`parser_init_with_path -> ast_reset -> expr_reset -> expr_count_set -> expr_env_mirror_enabled`.

The first reset lazily replaces the empty `expr_env_mirror_slot` with a
singleton while the caller-owned transient scope is active.  Scope teardown
reclaims that singleton, but the module global keeps its non-nil pointer.  The
second reset consequently calls `.len()` through a dangling array.  The
statement, declaration, and AST-harden cached mode slots use the same lazy
empty-to-singleton pattern and share the root cause.

## Repair boundary

Initialize the four cached mode slots as persistent singletons at module load;
their existing per-reset refresh functions continue to overwrite the cached
value.  Do not weaken transient reclamation, retain full parser modules, add a
runtime alias, or revive the rejected lexer-lifetime experiment.

## Required evidence

- A focused native executable performs two `ast_reset` calls around transient
  teardown and survives the exact second-reset crash boundary.  A broader
  two-surface fixture remains adjacent evidence; its initial build exposed the
  independent `compiler.mir.mir_serialization` surface-registration blocker
  before execution and is not counted as a result.
- The existing streaming lifecycle SSpec retains the real two-file and alias
  cases for the rebuilt self-hosted test runner.
- One bounded incremental Stage 2/3 refresh and Phase 4 retry crosses release
  sequence 1 before any broader completion claim.

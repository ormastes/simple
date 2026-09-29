# Handler commands rely on implicit compile-driver imports
## Closed 2026-09-16 — FIXED/RESOLVED 2026-08-02; explicit leaf imports landed

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Status:** FIXED / RESOLVED 2026-08-02
**Fix owner:** `codex-genuine-imports` (RESOLVED)
**Area:** `src/app/io/_CliCommands/handler_commands.spl`

## Finding

`cli_handle_compile` calls `cli_compile`, and `cli_check` calls `check_file` and
matches `CompileResult`, but the leaf module imports none of their authoritative
owners. Resolution currently depends on the circular broad
`use app.io.cli_commands.*` facade.

## Acceptance

- Import `cli_compile`, `check_file`, and `CompileResult` explicitly from their
  owning modules.
- Preserve an exact source-level ownership regression plus an adjacent guard
  against restoring these symbols to the circular wildcard dependency.

## Resolution

The handler now imports `check_file`, `CompileResult`, and `cli_compile` from
their leaf owners. The broad command facade remains only for actual sibling
command helpers; it is no longer the accidental provider for compiler APIs.


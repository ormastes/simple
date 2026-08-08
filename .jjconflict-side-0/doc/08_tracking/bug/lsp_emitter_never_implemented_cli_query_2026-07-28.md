# `LspEmitter` / `LspCodeAction` are imported and called but were never implemented

**Date:** 2026-07-28 · **Status:** open · **Class:** NEVER-EXISTED (capability gap)
**Found:** triage of `scripts/check/check-dangling-references.shs` findings scoped
to `src/app/cli/**`.

## Symptom

The checker reports, for three separate CLI query modules:

```
src/app/cli/query_check.spl:16:      SYMBOL: imported name `LspEmitter` is declared in no src file
src/app/cli/query_commands.spl:22:   SYMBOL: imported name `LspEmitter` is declared in no src file
src/app/cli/query_commands.spl:22:   SYMBOL: imported name `LspCodeAction` is declared in no src file
src/app/cli/query_navigation.spl:12: SYMBOL: imported name `LspEmitter` is declared in no src file
```

## Referencing sites

| File | Line | Reference |
|---|---|---|
| `src/app/cli/query_check.spl` | 16 | `use std.report.emitter.lsp.{LspEmitter}` |
| `src/app/cli/query_check.spl` | 113, 539, 645 | `val emitter = LspEmitter.default_emitter()` |
| `src/app/cli/query_commands.spl` | 22 | `use std.report.emitter.lsp.{LspEmitter, LspDiagnostic, LspCodeAction, LspTextEdit}` |
| `src/app/cli/query_commands.spl` | 133 | `val emitter = LspEmitter.default_emitter()` |
| `src/app/cli/query_navigation.spl` | 12 | `use std.report.emitter.lsp.{LspEmitter}` |
| `src/app/cli/query_navigation.spl` | 90 | `val emitter = LspEmitter.default_emitter()` |

## Missing targets

1. The module `std.report.emitter.lsp` — **no `report/emitter` directory exists
   anywhere under `src/`** (`find src -path '*report*' -name '*.spl' | grep -i emit`
   is empty). The dangling-reference checker does not flag the MODULE path only
   because its last-two-segment fallback matches the unrelated key `lsp`
   (`src/compiler_rust/lib/std/src/mcp/lsp/mod.spl`).
2. `LspEmitter` — declared in no file, of any type, anywhere in the repo.
3. `LspEmitter.default_emitter()` — no `default_emitter` exists on any LSP type.
4. `LspCodeAction` — declared nowhere.

`LspDiagnostic` and `LspTextEdit` (the other two names on the same import line in
`query_commands.spl`) *do* exist, but in a different module
(`src/compiler_rust/lib/std/src/mcp/lsp/mod.spl`, which declares `Diagnostic`,
`Position`, `Range`, `Location`, `SymbolInfo`, `HoverInfo`, and five
`Lsp*Handler` classes — but no emitter and no `LspCodeAction`). So the import
line as written cannot be satisfied by any single module.

## Git evidence — NEVER-EXISTED, not a deletion victim

Checked against a healthy pre-incident tree from before the jj-conflict-tree
mass-deletion (`6fd7474260c`, the parent of `115803a7aff`):

```
git grep -l 'LspEmitter' 6fd7474260c -- 'src/*.spl'
  src/app/cli/query_check.spl
  src/app/cli/query_commands.spl
  src/app/cli/query_navigation.spl
```

Three hits, all of them the *consuming* import sites — identical to today. There
has never been a commit in which `LspEmitter` was defined. This is an unfulfilled
promise, **not** collateral damage from the conflict-tree push
(`37cda4befdc` / `3f577c312de`).

## Consequence

`query_check`, `query_commands` and `query_navigation` are live code:
`query_navigation` is imported by `src/app/cli/query_rich.spl`, and
`query_commands` is imported by
`src/compiler_rust/lib/std/src/tooling/__init__.spl`. Every code path that
reaches one of the five `LspEmitter.default_emitter()` call sites is
unresolvable. The LSP-shaped output of `simple query --check` /
`--code-actions` / rename cannot ever have worked.

## Not fixed here

Deliberately not guessing an implementation: an emitter type with a
`default_emitter()` constructor plus whatever the five call sites do with the
result is a real design decision, not a repoint. Needs an owner for
`std.report.emitter.lsp`.

## Secondary finding (separate, not fixed)

`src/app/cli/query_check.spl` defines `fn query_check`, but the *live* wiring
goes through a different definition: `src/app/cli/query_diagnostics.spl:11`
also defines `query_check`, and `src/app/cli/query_rich.spl:23` re-exports it
from `query_diagnostics` — not from `query_check.spl`. Nothing in `src/` or
`test/` imports `app.cli.query_check`. So `query_check.spl` looks like a
shadowed duplicate. Left in place rather than deleted, because removing a
~650-line file needs its own verification pass.

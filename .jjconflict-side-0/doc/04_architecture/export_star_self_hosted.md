# Self-Hosted `export *` Parity

## 1. Problem statement

The Rust bootstrap parser at `src/compiler_rust/parser/src/stmt_parsing/module_system.rs:579-600` accepts bare `export *` and emits `ExportUseStmt { path: "", target: ImportTarget::Glob }`. The Rust resolver was wired in commit `99f6dd11aa16` (3 files: `src/compiler_rust/compiler/src/module_resolver/resolution.rs`, `.../manifest.rs`, and `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs`).

The self-hosted Simple parser at `src/lib/common/parser/` lags: `ast.spl:99-110` only has `Stmt.Export([text])` — no `ImportTarget`, no `ExportUseStmt`. Self-hosted builds fail at parse time when they encounter the bare `export *` that now lives in `src/compiler_rust/lib/std/src/mcp/lsp/__init__.spl`.

This is the remaining blocker for TODO #26.

## 2. AST delta (minimal)

In `src/lib/common/parser/ast.spl`:

- New enum `ImportTarget` with variants `Named(text)`, `Aliased(text, text)`, `Group([text])`, `Glob`. Mirrors the Rust-side `ImportTarget` enum. The resolver's `src/compiler/99.loader/module_resolver/types.spl` already imports `ImportTarget` from `parser.ast`, so adding it here unblocks downstream consumers.
- New `Stmt` variant: `ExportUseStmt(text, ImportTarget)`. `path: text` is `""` for bare `export *`. Reserved for future `export foo.* from bar` which would set `path = "bar"`.

**Non-migration:** `Stmt.Import([text])` and `Stmt.Export([text])` keep their existing payloads. Only the export-star path goes through the new variant.

## 3. Parser delta

In `src/lib/common/parser/parser.spl`, after consuming the `export` keyword, peek the next token:

- If `*` → consume, emit `Stmt.ExportUseStmt("", ImportTarget.Glob)`.
- Else → fall through to the existing named-list path → `Stmt.Export([...])`.

Mirrors Rust parser at `module_system.rs:579-600`. Single-line statement; no newline/indent handling changes.

## 4. Resolver delta

Two self-hosted hook sites already contain placeholder arms for `ImportTarget.Glob`:

- `src/compiler/99.loader/module_resolver/manifest.spl:190-191` — where `Node.ExportUseStmt` is collected. Fill the Glob arm: iterate `manifest.child_modules`, call `add_export(symbol_id)` per child module.
- `src/compiler/99.loader/module_resolver/resolution.spl:324` — placeholder comment says "Glob exports - would need to resolve the target module". Replace with a loop that resolves the current module's children and pushes all public names into the resolved-names list.

`should_keep_selective_export` has no self-hosted counterpart found — "keep all for Glob" is the safe default.

## 5. Non-goals

- Full migration of `Stmt.Import` / `Stmt.Export` to carry `ImportTarget`. That's a separate, wider effort.
- `export foo.* from bar` (path-based re-export glob). The AST carries the `path: text` field to accommodate it; parser-side support deferred.

## 6. Rollback / forward-compat

Backout path: revert `src/compiler_rust/lib/std/src/mcp/lsp/__init__.spl` from `export *` to the explicit list. Separately revert the resolver fill, parser peek, and AST addition in reverse order.

**Exhaustive-match audit:** adding a new `Stmt` variant can break exhaustive pattern matches. Grep `match stmt\|case Stmt\.` before landing and either add a `_` fallback or an explicit `ExportUseStmt(path, target) => ...` arm per site.

## 7. Verification

| Check | Pass criterion |
|---|---|
| `bin/simple build check` | exit 0 |
| Parser spec | `export *` → `Stmt.ExportUseStmt("", ImportTarget.Glob)` |
| Regression | `export foo, bar` → `Stmt.Export(["foo","bar"])` unchanged |
| Resolver fixture | module A `export *`, consumer B imports from A, sees all children's public symbols |
| E2E | `bin/simple` parses `src/compiler_rust/lib/std/src/mcp/lsp/__init__.spl` (now `export *`) with no error |

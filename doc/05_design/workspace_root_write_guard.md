<!-- codex-design -->

# Workspace Root Write Guard Detail Design

## Commands

- `audit`: check root and immediate child entries.
- `audit --staged`: check only staged added/renamed paths.
- `fix`: run audit and move violations into `build/workspace_quarantine/`.
- `fix --dry-run`: print planned moves only.
- `lock` / `unlock`: print platform-specific permission restore commands for
  the root plus protected immediate child directories.
- `lock --apply` / `unlock --apply`: perform opt-in permission changes while
  leaving mutable generated directories such as `build`, `tmp`, and `target`
  writable.

## Policy Parsing

Root entries are read from backtick/bold entries in the `FILE.md` Quick
Reference and Root Files tables up to the "No other files at root" marker.

Immediate child entries are read from `FILE.md` tables containing explicit
paths such as `doc/04_architecture/`. Entries already tracked by VCS are treated
as legacy baseline unless `--strict` is used.

## Diagnostics

- `WRG001`: root entry is not allowed by `FILE.md`.
- `WRG002`: immediate root child entry is not declared by `FILE.md`.

Both are deny-level diagnostics for staged lint/hook usage.

## Integration

`bin/simple build lint` invokes `sh scripts/check-workspace-root-guard.shs audit
--staged` before delegating to the runtime. The hook at `scripts/hooks/pre-commit`
does the same. Users can install it with:

```sh
git config core.hooksPath scripts/hooks
```

## Safety

The implementation never deletes files. Quarantine manifests record original
and destination paths. Existing untracked full-audit violations are reported but
not moved unless the user explicitly runs `fix`. Permission changes are preview
only unless `--apply` is present.

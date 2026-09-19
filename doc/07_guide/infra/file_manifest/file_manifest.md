# FILE.md Manifest Guide

## What is FILE.md?

FILE.md files declare which entries (files and directories) are allowed in a
directory. The workspace root guard enforces these declarations during lint and
pre-commit checks.

## Format

Each FILE.md has two key sections:

### Allowed Entries

Declares what belongs in this directory:

```markdown
## Allowed Entries

| Entry | Description |
|---|---|
| `app` | Applications |
| `compiler` | Unified compiler |
```

### Child Manifests

Links to child FILE.md files that enforce subdirectories:

```markdown
## Child Manifests

| Path | Enforces |
|---|---|
| `compiler/FILE.md` | `compiler/` directory |
```

Only linked manifests enforce. An orphan FILE.md (not referenced by its parent)
is documentary only.

### Submodules (optional)

Directories containing git submodules should declare them in a `## Submodules`
section listing path, upstream URL, and a short description:

```markdown
## Submodules

| Path | URL | Description |
|---|---|---|
| `07_ml/svllm` | `ormastes/svllm` | Simple vLLM inference engine |
```

This section is documentary (not enforced by the root guard) but helps tools
and contributors discover which entries are external repositories.

## How to Add a New Entry

1. Open the FILE.md in the target directory
2. Add the entry to the `## Allowed Entries` table
3. If the entry is also at root depth-2, add it to the root FILE.md's
   `## dir/` section as well
4. Run `sh scripts/check-workspace-root-guard.shs audit` to verify

## How to Create a New Child Manifest

1. Create `<dir>/FILE.md` with `## Allowed Entries` listing the directory contents
2. Add `<dir>/FILE.md` to the parent FILE.md's `## Child Manifests` section
3. Add `<dir>/FILE.md` to the parent FILE.md's `## Allowed Entries` (or root `## dir/` section)
4. Run `sh scripts/check-workspace-root-guard.shs audit --strict` to verify

## Error Codes

| Code | Meaning | Fix |
|------|---------|-----|
| WRG001 | Root entry not in FILE.md | Add to root `## Root Files` or remove the file |
| WRG002 | Depth-2 entry not in FILE.md `## dir/` section | Add to the root FILE.md's dir section |
| WRG003 | Deeper entry not in linked child FILE.md | Add to the child FILE.md's `## Allowed Entries` |

## Integration Points

- **Lint**: `bin/simple build lint` runs the guard automatically
- **Pre-commit**: `.git/hooks/pre-commit` blocks commits with violations
  (install via `sh scripts/setup/install-workspace-guard-hook.shs --apply`)
- **SPipe verify**: Phase 7 runs the guard in strict mode
- **MCP**: File I/O protection engine has in-memory root policy rules

## Commands

```bash
sh scripts/check-workspace-root-guard.shs audit           # Non-strict (grandfathers tracked entries)
sh scripts/check-workspace-root-guard.shs audit --strict   # All entries must be declared
sh scripts/check-workspace-root-guard.shs audit --staged   # Only newly staged files
sh scripts/check-workspace-root-guard.shs fix              # Quarantine violations
sh scripts/check-workspace-root-guard.shs --self-test      # Run smoke tests
sh scripts/setup/install-workspace-guard-hook.shs --check        # Check hook status
sh scripts/setup/install-workspace-guard-hook.shs --apply        # Install hook
```

## Related: directory fan-out and depth (doc layout)

FILE.md governs *which entries* are allowed in a directory. A sibling guard,
`scripts/check/check-directory-fanout.shs`, governs a different axis — *how
many* files a directory holds and *how deep* the doc tree nests — backing
`.claude/rules/structure.md`'s "≤10 files per directory; max depth 4
(doc/phase/domain/topic)" rule. It is baseline-relative (new/grown violations
fail, pre-existing ones are grandfathered), configured by
`config/check/doc_layout.sdn` (`root`, `file_limit`, `max_depth`,
`exempt_phase` per DO-NOT-REFACTOR phase), and supports `--config`/`--root`
overrides, a `--depth`-only or `--fanout`-only mode, a `--plan` mode that
prints a proposed (never-applied) file-to-subdirectory split for an
over-limit directory, and a fatal `--selftest`. See the script's own header
comment for the full contract and the two baseline files
(`scripts/check/directory_fanout_baseline.txt`,
`scripts/check/doc_depth_baseline.txt`).

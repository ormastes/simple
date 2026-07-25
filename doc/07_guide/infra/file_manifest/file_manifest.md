# FILE.md Manifest Guide

## What is FILE.md?

FILE.md files declare which entries (files and directories) are allowed in a
directory. The workspace root guard enforces these declarations through its
explicit audit, pre-commit, and SPipe verification paths.

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

- **Manual**: run `sh scripts/check-workspace-root-guard.shs audit`
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

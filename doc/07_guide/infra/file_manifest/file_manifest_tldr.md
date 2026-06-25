# FILE.md Manifest — TLDR

Declare allowed files per directory. Enforced at lint, commit, and SPipe verify.

```
  FILE.md (root)                     ← WRG001/WRG002
    ├── ## Child Manifests
    │     └── src/FILE.md            ← linked → enforced
    │         ## Allowed Entries
    │           app, compiler, lib…  ← WRG003 if missing
    ├── ## Root Files
    │     CLAUDE.md, src, doc, …
    └── ## src/
          src/app, src/compiler, …   ← WRG002 fallback
```

## Enforcement Points

| Where | Command | Scope |
|-------|---------|-------|
| Lint | `bin/simple build lint` | auto |
| Commit | `.git/hooks/pre-commit` | `--staged` |
| SPipe | verify phase step 7 | `--strict` |

## Quick Actions

```bash
# Add new root entry      → edit FILE.md ## Root Files
# Add new depth-2 entry   → edit FILE.md ## dir/ section
# Add governed dir entry   → edit dir/FILE.md ## Allowed Entries
# Create new child manifest → create dir/FILE.md + link in parent
# Check status             → sh scripts/check-workspace-root-guard.shs audit
# Install hook             → sh scripts/setup/install-workspace-guard-hook.shs --apply
```

Orphan FILE.md (not linked by parent) = documentation only, not enforced.

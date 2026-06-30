# Workspace Root Write Guard — TLDR

FILE.md manifests form a linked tree that controls which files can exist in each
directory. Enforcement runs at lint, pre-commit, and SPipe verify time.

```
                      ┌─────────────┐
                      │  FILE.md    │  Root manifest
                      │ (root)      │  WRG001: root entries
                      └──────┬──────┘  WRG002: depth-2 (fallback)
                             │
              ┌──────────────┼──────────────┐
              │              │              │
         ┌────┴────┐   ┌────┴────┐   ┌────┴────┐
         │src/     │   │doc/     │   │config/  │  Child manifests
         │FILE.md  │   │FILE.md  │   │FILE.md  │  WRG003: governed entries
         └────┬────┘   └─────────┘   └─────────┘
              │
         ┌────┴────┐
         │compiler/│   Deeper manifests (future)
         │FILE.md  │   WRG003: deeper entries
         └─────────┘
```

## Enforcement Chain

```
git commit ──→ .git/hooks/pre-commit ──→ audit --staged ──→ block
                                                            on WRG*
bin/simple build lint ──→ _cli_run_workspace_root_guard()

SPipe verify (Phase 7) ──→ audit --strict
```

## Key Rule

A child FILE.md only enforces when **linked** by its parent's
`## Child Manifests` section. Orphan FILE.md = documentary only.

## Error Codes

| Code | Trigger | Fix |
|------|---------|-----|
| WRG001 | Root entry not listed | Add to `## Root Files` |
| WRG002 | Depth-2 child, dir not governed | Add to `## dir/` section |
| WRG003 | Entry in governed dir not listed | Add to child FILE.md |

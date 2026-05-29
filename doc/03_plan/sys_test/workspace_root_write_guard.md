# Workspace Root Write Guard System Test Plan

## Coverage

- Clean staged audit exits zero.
- Synthetic bad root path emits `WRG001`.
- Synthetic bad immediate child path emits `WRG002`.
- `bin/simple build lint` invokes staged audit before normal lint.
- `scripts/hooks/pre-commit` delegates to the same staged audit.
- Lock/unlock modes print recovery commands instead of mutating by default.

## Commands

```sh
sh scripts/check-workspace-root-guard.shs audit --staged
tmp=$(mktemp); printf '%s\n' bad.root src/new_child > "$tmp"; sh scripts/check-workspace-root-guard.shs audit --path-file "$tmp"; rm -f "$tmp"
sh scripts/check-workspace-root-guard.shs lock --dry-run
bin/simple test test/unit/app/workspace_root_write_guard_spec.spl --mode=interpreter
```

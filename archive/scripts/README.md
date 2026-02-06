# Archived Scripts

**Purpose:** Historical scripts that have been replaced or are no longer needed

**Archive Date:** 2026-02-06

---

## Directory Structure

```
archive/scripts/
├── build/          # Build scripts replaced by Simple implementations
├── migrate/        # One-time migration scripts (already executed)
├── verify/         # Verification scripts (to be replaced)
└── profiling/      # Profiling scripts (to be replaced)
```

---

## Build Scripts (Migrated to Simple)

These scripts have been replaced by Simple implementations in `src/app/build/`:

| Archived Script | Replacement | Status |
|-----------------|-------------|--------|
| `link-bins.sh` | `src/app/build/link_bins.spl` | ✅ Migrated |
| `run_quick_tests.sh` | `src/app/test/quick_runner.spl` | ✅ Migrated |
| `capture_bootstrap_debug.sh` | `src/app/build/capture_debug.spl` | ✅ Migrated |

**Do not use these scripts** - use the Simple implementations instead.

---

## Migration Scripts (Obsolete)

These were one-time migration scripts for syntax changes. They have been executed and are no longer needed:

### Shell Scripts (.sh)
- `complete_mixin_phase1.sh` - Completed mixin phase 1 migration
- `fix_expr_if_patterns.sh` - Fixed if expression patterns
- `fix-paths.sh` - Path fixing migration
- `migrate_to_ll1.sh` - LL(1) grammar migration
- `migrate_to_scala_syntax.sh` - Scala-style syntax migration

### Python Scripts (.py)
- `fix_if_val_pattern.py` - if let → if val migration
- `migrate_spec_to_spl.py` - .spec → .spl migration
- `migrate_syntax.py` - General syntax migration
- `migrate_to_me_syntax.py` - me keyword migration
- `refactor_lowering.py` - HIR lowering refactoring
- `remove_self_params.py` - Remove explicit self parameters

### Simple Scripts (.spl)
- `migrate_to_ll1.spl` - LL(1) migration (Simple version)
- `migrate_with_syntax.spl` - with syntax migration

**Status:** All migrations complete. Scripts kept for reference only.

---

## Why Archive Instead of Delete?

1. **Historical Reference:** Shows evolution of the language and tooling
2. **Debugging:** May need to reference old behavior
3. **Documentation:** Demonstrates what changes were made
4. **Recovery:** Can extract patterns if needed for future migrations

---

## When to Archive a Script

Archive a script when:

- ✅ It has been migrated to Simple (.spl)
- ✅ It was a one-time migration tool (already executed)
- ✅ It is no longer referenced by CI/workflows
- ✅ A superior replacement exists

Do NOT archive:

- ❌ Bootstrap scripts (build-bootstrap.sh, install.sh, build-full.sh)
- ❌ Scripts still used in production
- ❌ Scripts without a replacement

---

## Restoration

If you need to restore an archived script temporarily:

```bash
# Copy from archive (don't move - keep archive intact)
cp archive/scripts/build/link-bins.sh script/build/link-bins.sh.old

# Use for reference, then delete
rm script/build/link-bins.sh.old
```

---

## See Also

- **doc/report/script_migration_2026-02-06.md** - Migration status
- **doc/guide/script_migration.md** - Migration guide
- **CLAUDE.md** - Current script policy

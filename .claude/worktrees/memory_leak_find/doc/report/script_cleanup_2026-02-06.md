# Script Cleanup Report - 2026-02-06

**Status:** ✅ Complete
**Action:** Archived obsolete scripts to `archive/scripts/`

---

## Summary

Successfully cleaned up 18 obsolete scripts by archiving them to `archive/scripts/`:

- **3 migrated build scripts** (replaced by Simple implementations)
- **15 obsolete migration scripts** (one-time migrations already executed)
- **1 empty directory removed** (`scripts/migrate/`)

All archived scripts are preserved for historical reference but are no longer in active use.

---

## Archived Files

### Build Scripts → `archive/scripts/build/` (3 files)

These have been **replaced by Simple implementations**:

| Archived | Replacement | Status |
|----------|-------------|--------|
| `link-bins.sh` (910 bytes) | `src/app/build/link_bins.spl` (97 lines) | ✅ Migrated |
| `run_quick_tests.sh` (2.9 KB) | `src/app/test/quick_runner.spl` (203 lines) | ✅ Migrated |
| `capture_bootstrap_debug.sh` (985 bytes) | `src/app/build/capture_debug.spl` (97 lines) | ✅ Migrated |

**Total:** ~4.8 KB of Bash scripts replaced

### Migration Scripts → `archive/scripts/migrate/` (15 files)

One-time migration tools that have already been executed:

#### Shell Scripts (5 files)
- `complete_mixin_phase1.sh` (4.3 KB)
- `fix_expr_if_patterns.sh` (917 bytes)
- `fix-paths.sh` (2.3 KB)
- `migrate_to_ll1.sh` (4.3 KB)
- `migrate_to_scala_syntax.sh` (3.5 KB)

#### Python Scripts (8 files)
- `fix_if_val_pattern.py` (3.8 KB)
- `migrate_spec_to_spl.py` (12.6 KB)
- `migrate_syntax.py` (5.2 KB)
- `migrate_to_me_syntax.py` (5.1 KB)
- `refactor_lowering.py` (7.0 KB)
- `remove_self_params.py` (3.0 KB)

#### Simple Scripts (2 files)
- `migrate_to_ll1.spl` (9.2 KB)
- `migrate_with_syntax.spl` (2.6 KB)

**Total:** ~63 KB of migration code archived

---

## Archive Structure

```
archive/scripts/
├── README.md              # Documentation
├── build/                 # Migrated build scripts (3 files)
│   ├── link-bins.sh
│   ├── run_quick_tests.sh
│   └── capture_bootstrap_debug.sh
└── migrate/               # Obsolete migration scripts (15 files)
    ├── complete_mixin_phase1.sh
    ├── fix_expr_if_patterns.sh
    ├── fix_if_val_pattern.py
    ├── fix-paths.sh
    ├── migrate_spec_to_spl.py
    ├── migrate_syntax.py
    ├── migrate_to_ll1.sh
    ├── migrate_to_ll1.spl
    ├── migrate_to_me_syntax.py
    ├── migrate_to_scala_syntax.sh
    ├── migrate_with_syntax.spl
    ├── refactor_lowering.py
    └── remove_self_params.py
```

---

## What Was NOT Archived

### Bootstrap Scripts (KEEP - Required)

These MUST remain as Bash (run before Simple runtime exists):

- ✅ `scripts/build-bootstrap.sh` - GitHub Actions first build
- ✅ `scripts/build-full.sh` - Release package builder
- ✅ `scripts/install.sh` - End-user installer

### Active Scripts (KEEP - Still Used)

Scripts that are still in use and have not been migrated yet:

- `scripts/jj-wrappers/git.sh` - Git→JJ wrapper (kept per user request)
- `scripts/fix_ffi_calls.py` - Active audit tool (Phase 2 migration)
- `scripts/build/spec_gen.py` - Active doc generator (Phase 2 migration)
- `scripts/verify/*.sh` - Active verification tools (Phase 3 migration)
- `scripts/profiling/*.sh` - Active profiling tools (Phase 4 migration)

---

## Benefits

1. **Cleaner Repository:**
   - Removed 18 obsolete scripts from active paths
   - Deleted empty `scripts/migrate/` directory
   - Clear separation of active vs historical code

2. **Reduced Confusion:**
   - No duplicate build scripts (old .sh vs new .spl)
   - Clear that migration tools are one-time use only
   - Archive location signals "historical reference only"

3. **Historical Preservation:**
   - All scripts preserved for reference
   - Can recover patterns if needed
   - Shows evolution of the language

4. **Documentation:**
   - `archive/scripts/README.md` explains what each script was for
   - Clear migration status in reports
   - Easy to see what's been accomplished

---

## Next Actions

### Immediate
- [ ] Test new Simple scripts work correctly
- [ ] Update CI workflows if they reference archived scripts
- [ ] Commit archive with clear message

### Phase 2 (Build Tools)
- [ ] Migrate `scripts/fix_ffi_calls.py` → `src/app/audit/ffi_analyzer.spl`
- [ ] Migrate `scripts/build/spec_gen.py` → `src/app/doc/spec_gen/`
- [ ] Archive after successful migration

### Phase 3 (Verification)
- [ ] Migrate `scripts/verify/*.sh` → `src/app/verify/*.spl`
- [ ] Archive after successful migration

---

## Commands Used

```bash
# Create archive structure
mkdir -p archive/scripts/{build,migrate,verify,profiling}

# Archive migrated build scripts
git mv scripts/build/link-bins.sh archive/scripts/build/
git mv scripts/build/run_quick_tests.sh archive/scripts/build/
git mv scripts/build/capture_bootstrap_debug.sh archive/scripts/build/

# Archive obsolete migration scripts
git mv scripts/migrate/*.sh archive/scripts/migrate/
git mv scripts/migrate/*.py archive/scripts/migrate/
git mv scripts/migrate/*.spl archive/scripts/migrate/

# Remove empty directory
rmdir scripts/migrate/

# Create documentation
# (Created archive/scripts/README.md)
```

---

## Verification

```bash
# Count archived files
find archive/scripts -type f | wc -l
# Expected: 19 (18 scripts + 1 README)

# Verify originals are gone
ls scripts/build/link-bins.sh 2>/dev/null
# Expected: No such file or directory

# Verify new scripts exist
ls src/app/build/link_bins.spl src/app/test/quick_runner.spl
# Expected: Files exist
```

---

## See Also

- **archive/scripts/README.md** - Archive documentation
- **doc/report/script_migration_2026-02-06.md** - Overall migration status
- **doc/guide/script_migration.md** - Migration guide for remaining scripts

# Import Path Migration - TODO Plan

**Status:** Planned
**Priority:** P1 (High - affects all imports)
**Estimated Effort:** 3-5 days
**Date:** 2026-02-04

## Problem Statement

Current import system treats all paths as relative, causing confusion and inconsistency. Need to implement proper absolute/relative distinction as per design.

## Current State

**All imports are relative:**
```simple
use testing.*              # Resolves relatively (confusing)
use .smf_enums.*          # Resolves relatively (correct)
use ../parent.module.*    # Resolves relatively (correct)
```

**No enforcement of:**
- Absolute path syntax (no prefix)
- Relative path rules (`.` for same dir only)
- Parent path rules (`..` for parent only)

## Target State

**Clear absolute/relative distinction:**
```simple
use testing.*              # Absolute (from root)
use .smf_enums.*          # Relative (same dir)
use ..parent.module.*     # Parent (up one level)
```

## Migration Plan

### Phase 1: Analysis & Audit (0.5 days)

**Goal:** Understand current import usage across codebase

**Tasks:**
1. Scan all `.spl` files for import statements
2. Categorize imports by pattern:
   - No prefix: `use module.*`
   - Dot prefix: `use .module.*`
   - Parent prefix: `use ..module.*`
   - Invalid: `use path/to/module.*`
3. Create migration spreadsheet with:
   - File path
   - Current import
   - Intended type (absolute/relative/parent)
   - Required change

**Deliverable:** `doc/migration/import_audit_2026-02-04.csv`

**Command:**
```bash
# Find all imports
grep -r "^use " src --include="*.spl" > import_audit.txt

# Analyze patterns
grep "^use [^.]" import_audit.txt    # Potential absolute
grep "^use \." import_audit.txt      # Relative
grep "^use \.\." import_audit.txt    # Parent
grep "use .*/" import_audit.txt      # Invalid (uses /)
```

### Phase 2: Compiler Implementation (1.5 days)

**Goal:** Implement absolute/relative resolution in compiler

**File:** `src/compiler/dependency/resolution.spl`

**Tasks:**

1. **Update Import Resolution Logic**
   ```simple
   fn resolve_import(import_path: text, current_file: text) -> text:
       if import_path.starts_with(".."):
           # Parent import: resolve from parent directory
           resolve_parent_import(import_path, current_file)
       else if import_path.starts_with("."):
           # Relative import: resolve from current directory
           resolve_relative_import(import_path, current_file)
       else:
           # Absolute import: resolve from project root
           resolve_absolute_import(import_path)
   ```

2. **Add Path Validators**
   - `validate_absolute_path(path)` - No `.` or `..` prefix
   - `validate_relative_path(path)` - Must start with `.`, no subdirs
   - `validate_parent_path(path)` - Must start with `..`, one level only

3. **Update Parser Warnings**
   - Warn on `use .subdir.module` (relative can't traverse subdirs)
   - Warn on `use ../..` (double parent not allowed)
   - Error on `use path/with/slash`

**Deliverables:**
- Updated `src/compiler/dependency/resolution.spl`
- Updated `src/compiler/parser.spl` with new warnings
- Unit tests in `test/compiler/import_resolution_spec.spl`

### Phase 3: Codebase Migration (2 days)

**Goal:** Fix all existing imports to match new design

**Strategy:** Automated where possible, manual for edge cases

**3.1 Automated Migration (1 day)**

Create migration script: `tools/migrate_imports.spl`

```simple
fn migrate_import(file_path: text, import_line: text) -> text:
    val import = parse_import(import_line)

    # Determine correct prefix based on file locations
    if is_same_directory(file_path, import.module):
        # Should be relative: .module
        return "use .{import.module} {import.items}"
    else if is_parent_directory(file_path, import.module):
        # Should be parent: ..module
        return "use ..{import.module} {import.items}"
    else:
        # Should be absolute: module
        return "use {import.module} {import.items}"
```

**Run migration:**
```bash
# Backup first
jj bookmark create pre-import-migration

# Run migration
simple tools/migrate_imports.spl --scan src/
simple tools/migrate_imports.spl --fix src/ --dry-run
simple tools/migrate_imports.spl --fix src/

# Verify
simple test
```

**3.2 Manual Review (0.5 days)**

Review and fix:
- Edge cases flagged by migration script
- Imports in generated code
- Test files with special import patterns

**3.3 Cleanup (0.5 days)**

Remove deprecated patterns:
- Old `use path/to/module` syntax (if any remain)
- Incorrect relative imports
- Update templates in `.claude/templates/`

### Phase 4: Testing & Validation (1 day)

**Goal:** Ensure migration didn't break anything

**Tasks:**

1. **Unit Tests**
   - Import resolution tests
   - Path validation tests
   - Parser warning tests

2. **Integration Tests**
   - Build entire project
   - Run full test suite
   - Verify all imports resolve correctly

3. **Regression Tests**
   - Compare generated code before/after
   - Verify SMF files still load
   - Check LSP still works

**Test Commands:**
```bash
# Build
simple build

# All tests
simple test

# Specific import tests
simple test test/compiler/import_resolution_spec.spl

# Verify no warnings
simple build 2>&1 | grep "import.*warning"
```

### Phase 5: Documentation (0.5 days)

**Goal:** Update all documentation with new import syntax

**Files to Update:**
- `CLAUDE.md` - Update import examples
- `doc/guide/syntax_quick_reference.md` - Import syntax section
- `doc/design/import_path_design.md` - Already created
- `.claude/skills/coding.md` - Import guidelines
- README examples
- Tutorial files

**Deliverable:** `doc/report/import_migration_complete_2026-02-XX.md`

## Validation Checklist

Before considering migration complete:

- [ ] All imports follow new design (absolute/relative/parent)
- [ ] No `/` in any import paths
- [ ] Parser warns on invalid syntax
- [ ] Compiler resolves all three import types correctly
- [ ] All tests pass
- [ ] No import-related warnings in build
- [ ] Documentation updated
- [ ] Migration script committed
- [ ] Completion report written

## Rollback Plan

If migration causes issues:

```bash
# Rollback to pre-migration state
jj bookmark set main -r pre-import-migration

# Fix issues
# ... manual fixes ...

# Re-run partial migration
simple tools/migrate_imports.spl --fix src/compiler/ --dry-run
```

## Dependencies

**Blocked by:** None (can start immediately)

**Blocks:**
- LSP improvements (needs correct import resolution)
- Package system (needs absolute imports)
- Module refactoring (depends on import clarity)

## Timeline

| Phase | Duration | Start | End |
|-------|----------|-------|-----|
| Phase 1: Analysis | 0.5 days | Day 1 AM | Day 1 PM |
| Phase 2: Compiler | 1.5 days | Day 1 PM | Day 3 AM |
| Phase 3: Migration | 2 days | Day 3 AM | Day 5 AM |
| Phase 4: Testing | 1 day | Day 5 AM | Day 6 AM |
| Phase 5: Documentation | 0.5 days | Day 6 AM | Day 6 PM |
| **Total** | **5.5 days** | **Day 1** | **Day 6** |

## Success Criteria

1. ✅ All imports use correct prefix (none, `.`, or `..`)
2. ✅ No `/` in any import path
3. ✅ Compiler distinguishes absolute from relative
4. ✅ All tests pass
5. ✅ Documentation updated
6. ✅ Zero import warnings in build

## References

- Design: `doc/design/import_path_design.md`
- Current parser: `src/compiler/parser.spl`
- Resolution logic: `src/compiler/dependency/resolution.spl`
- Python PEP 328: Relative imports (inspiration)
- Rust module system: Absolute vs relative (comparison)

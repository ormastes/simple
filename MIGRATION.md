# Structural Refactoring Migration Guide

## Overview

This document describes the repository restructuring completed to separate Simple language files from the Rust compiler implementation.

## Changes

### New Directory Structure

| Old Path | New Path | Purpose |
|----------|----------|---------|
| `lib/std/` | `std_lib/src/` | Simple language standard library |
| `test/` | `std_lib/test/` | Simple language tests |
| N/A | `bin/` | Binary tools (gitignored) |
| `doc/` | `simple_doc/` (symlink) | Documentation (symlink for convenience) |

### Files Migrated

**Standard Library:**
- All `.spl` files from `lib/std/` → `std_lib/src/`
- Preserves all subdirectories: `core/`, `host/`, `gpu/`, etc.

**Tests:**
- All test files from `test/` → `std_lib/test/`
- Includes: `unit/`, `integration/`, `fixtures/`

### Code Updates

**Rust Code:**
- Updated references in 5 files:
  - `src/loader/src/package/format.rs` - Documentation example
  - `src/runtime/src/value/doctest_io.rs` - Test path
  - `src/compiler/src/interpreter_extern.rs` - Documentation comments (2 locations)
  - `src/driver/tests/interpreter_native_io.rs` - Documentation comment
  - `src/compiler/src/interpreter_native_io.rs` - Documentation comment

**Documentation:**
- Updated `CLAUDE.md` with new structure
- Created `std_lib/README.md`
- Created `bin/README.md`

**Build Files:**
- Updated `.gitignore` to exclude `bin/`

## For Developers

### Using the New Structure

**Standard Library Development:**
```bash
# Edit stdlib files
vim std_lib/src/core/array.spl

# Run stdlib tests
simple test std_lib/test/
```

**Binary Tools:**
```bash
# Place compiled tools here (not tracked by git)
simple build my_tool.spl -o bin/my_tool
./bin/my_tool
```

**Documentation:**
```bash
# Access via symlink
ls simple_doc/

# Or use original path
ls doc/
```

### Updating Existing Work

If you have local branches or work in progress:

1. **Rebase on main:**
   ```bash
   git checkout main
   git pull
   git checkout your-branch
   git rebase main
   ```

2. **Update any custom references to `lib/std`:**
   ```bash
   # Search for old paths
   grep -r "lib/std" .
   
   # Replace with new paths
   sed -i 's|lib/std|std_lib/src|g' your_file.rs
   ```

3. **Test your changes:**
   ```bash
   make check
   ```

## Rationale

This restructuring achieves several goals:

1. **Clarity:** Separates Simple language code from Rust implementation
2. **Discoverability:** Standard library is now at top-level `std_lib/`
3. **Tooling:** Binary tools have dedicated ignored directory
4. **Testing:** Test files co-located with library in `std_lib/test/`
5. **Documentation:** Symlink provides convenience without duplication

## Backward Compatibility

The old `lib/` and `test/` directories remain in the repository for now to avoid breaking existing workflows. They will be removed in a future cleanup commit once all references are verified updated.

## Questions?

See:
- `std_lib/README.md` - Standard library documentation
- `CLAUDE.md` - Updated development guide
- `doc/architecture.md` - Design principles

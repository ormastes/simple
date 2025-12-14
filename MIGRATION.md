# Structural Refactoring Migration Guide

## Overview

This document describes the repository restructuring to create a dedicated `simple/` workspace for Simple language development.

## Changes

### New Directory Structure

| Component | Location | Purpose |
|-----------|----------|---------|
| Rust compiler | Root directory | Compiler implementation in Rust |
| Simple workspace | `simple/` | Simple language development |
| Binaries | `simple/bin/` → `target/debug/` | Symlink to compiled executables |
| Documentation | `simple/doc/` → `doc/` | Symlink for convenience |
| Standard library | `simple/std_lib/src/` | Simple stdlib (.spl files) |
| Tests | `simple/std_lib/test/` | Simple language tests |

### Structure Overview

```
simple/                          # Project root (Rust compiler)
├── src/                         # Rust compiler source
├── doc/                         # Documentation
├── lib/                         # Legacy stdlib (to be removed)
└── simple/                      # Simple language workspace
    ├── bin/ -> ../target/debug/ # Compiled binaries (symlink)
    ├── doc/ -> ../doc/          # Documentation (symlink)
    └── std_lib/                 # Simple stdlib
        ├── src/                 # .spl library files
        └── test/                # .spl test files
```

### Files Migrated

**Standard Library:**
- All `.spl` files from `lib/std/` → `simple/std_lib/src/`
- Preserves all subdirectories: `core/`, `host/`, `gpu/`, etc.

**Tests:**
- All test files from `test/` → `simple/std_lib/test/`
- Includes: `unit/`, `integration/`, `fixtures/`

### Code Updates

**Rust Code:**
- Updated references in 5 files to use `simple/std_lib/src/` paths:
  - `src/loader/src/package/format.rs` - Documentation example
  - `src/runtime/src/value/doctest_io.rs` - Test path
  - `src/compiler/src/interpreter_extern.rs` - Documentation comments (2 locations)
  - `src/driver/tests/interpreter_native_io.rs` - Documentation comment
  - `src/compiler/src/interpreter_native_io.rs` - Documentation comment

**Documentation:**
- Updated `CLAUDE.md` with new structure
- Created `simple/std_lib/README.md`
- Updated `MIGRATION.md` (this file)

**Build Files:**
- Removed `/bin/` from `.gitignore` (now a symlink, should be tracked)

## Note on native_lib/

The `simple/native_lib/` directory mentioned in some documentation does not exist yet. Native Rust implementations are currently scattered throughout the `src/` tree:
- Runtime FFI: `src/runtime/src/value/ffi.rs`
- Native I/O: `src/compiler/src/interpreter_native_io.rs`
- Codegen FFI: `src/compiler/src/codegen/runtime_ffi.rs`
- Native loader: `src/native_loader/`

Future refactoring may consolidate these into `simple/native_lib/`.

## For Developers

### Using the New Structure

**Standard Library Development:**
```bash
# Edit stdlib files
vim simple/std_lib/src/core/array.spl

# Run stdlib tests  
simple test simple/std_lib/test/

# Access compiled binary
simple/bin/simple --version
```

**Binary Tools:**
```bash
# Binaries are in target/debug, accessible via symlink
simple/bin/simple run myfile.spl
```

**Documentation:**
```bash
# Access via symlink
ls simple/doc/

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
   sed -i 's|lib/std|simple/std_lib/src|g' your_file.rs
   ```

3. **Test your changes:**
   ```bash
   make check
   ```

## Rationale

This restructuring achieves several goals:

1. **Separation:** Clear boundary between Rust compiler (root) and Simple language (simple/)
2. **Workspace:** Dedicated `simple/` directory for Simple language development
3. **Convenience:** Symlinks provide easy access to binaries and docs
4. **Organization:** Standard library and tests co-located in `simple/std_lib/`
5. **Clarity:** Root directory focuses on compiler implementation

## Backward Compatibility

The old `lib/` and `test/` directories remain for now to avoid breaking existing workflows. They will be removed in a future cleanup commit once all references are verified updated.

## Questions?

See:
- `simple/std_lib/README.md` - Standard library documentation
- `CLAUDE.md` - Updated development guide
- `doc/architecture.md` - Design principles


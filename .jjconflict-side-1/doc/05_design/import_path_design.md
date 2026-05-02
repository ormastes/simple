# Import Path Design - Simple Language

**Status:** In Progress (Current implementation is all-relative)
**Date:** 2026-02-04

## Design Goals

1. **Clear distinction** between absolute and relative imports
2. **No confusion** with file paths (no `/` allowed)
3. **Consistent syntax** across the language

## Syntax Rules

### 1. Absolute Imports (No Prefix)

**Format:** `use module.submodule`

Resolves from project root:

```simple
use testing.{describe, it, expect}      # From root: testing module
use compiler.parser_types.*             # From root: compiler/parser_types.spl
use std.collections.HashMap             # From root: std/collections.spl
```

**Resolution:**
- Start from project root
- Use `.` to separate module hierarchy
- Maps to file path: `module.submodule` → `module/submodule.spl`

### 2. Relative Imports (Prefix: `.`)

**Format:** `use .module_name`

Resolves from current directory (same level only):

```simple
# In src/compiler/linker/smf_header.spl
use .smf_enums (Platform, Arch)         # Same dir: src/compiler/linker/smf_enums.spl
use .obj_taker.*                        # Same dir: src/compiler/linker/obj_taker.spl
```

**Resolution:**
- Start from current file's directory
- Only works for modules in the same directory
- Cannot traverse subdirectories: `.subdir.module` is INVALID

### 3. Parent Imports (Prefix: `..`)

**Format:** `use ..module_name` or `use ..parent.module`

Resolves from parent directory:

```simple
# In src/compiler/linker/smf_reader.spl
use ..monomorphize.metadata.*           # Parent: src/compiler/monomorphize/metadata.spl
use ..ast (FunctionDef)                 # Parent: src/compiler/ast.spl
```

**Resolution:**
- Start from parent directory
- Can use `.` for parent's subdirectories
- `..` goes up one level only (no `../..` - use absolute instead)

## Invalid Syntax

❌ **Using `/` (file path style):**
```simple
use std/testing                  # WRONG - use std.testing
use ./linker/smf_header          # WRONG - use .smf_header or ..linker.smf_header
```

❌ **Mixing styles:**
```simple
use .subdir.module               # WRONG - relative can't traverse subdirs
use src.compiler.parser          # WRONG - "src" shouldn't be in path (implied root)
```

❌ **Double parent:**
```simple
use ../../grandparent.module     # WRONG - use absolute instead
```

## Examples

### Example 1: Test File Imports

**File:** `src/compiler/linker/test/smf_enums_spec.spl`

```simple
# Correct:
use ..smf_enums.*                # Parent dir: src/compiler/linker/smf_enums.spl
use testing.{describe, it, expect}  # Absolute: testing module

# Wrong:
use ../smf_enums.*               # ❌ Too many dots
use std/testing.*                # ❌ Using /
use .smf_enums.*                 # ❌ Not in same directory
```

### Example 2: Header File Imports

**File:** `src/compiler/linker/smf_header.spl`

```simple
# Correct:
use .smf_enums (Platform, Arch)  # Same dir: src/compiler/linker/smf_enums.spl

# Wrong:
use smf_enums.Platform           # ❌ Missing . prefix for relative
use ./smf_enums.*                # ❌ No / allowed
```

### Example 3: Writer File Imports

**File:** `src/compiler/smf_writer.spl`

```simple
# Correct:
use compiler.monomorphize.partition.*   # Absolute from root
use .linker.smf_header (SmfHeader)      # Relative to compiler/ dir

# Wrong:
use src/compiler/monomorphize.*  # ❌ Don't include "src"
use linker/smf_header.*          # ❌ Missing . and using /
```

## Current Status

**⚠️ Current Implementation:** All paths are treated as relative.

This means:
- No distinction between absolute and relative
- Confusing resolution behavior
- Import paths don't match the design

## Migration Plan

See `doc/todo/import_path_migration.md` for detailed plan.

## Parser Warning

The parser now warns when `/` is detected in import paths:

```
warning: Import path should not use '/' - use '.' for modules
```

## Summary Table

| Import Type | Prefix | Example | Resolves From |
|-------------|--------|---------|---------------|
| Absolute | None | `use testing.*` | Project root |
| Relative | `.` | `use .module` | Current directory |
| Parent | `..` | `use ..module` | Parent directory |
| **Invalid** | `/` | `use a/b` | ❌ Not allowed |

## Design Rationale

1. **`.` prefix = relative** - Clear visual indicator
2. **No prefix = absolute** - Most common case is simplest
3. **`..` = parent** - Familiar from file systems, but limited to one level
4. **No `/`** - Avoids confusion with file paths
5. **`.` separator** - Consistent with most languages (Python, Java, Rust)

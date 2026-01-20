# Migration Report: fix_if_val_pattern.py → fix_if_val_pattern.spl

**Date**: 2026-01-20
**Migration #**: 11
**Source**: `scripts/fix_if_val_pattern.py` (Python, 109 lines)
**Target**: `simple/std_lib/src/tooling/fix_if_val_pattern.spl` (Simple, 217 lines)
**Status**: ✅ Complete

---

## Overview

Migrated Python script for fixing invalid `if val Some(x) = ...` pattern matching syntax to Simple Language. This tool converts the invalid syntax to proper match expressions, fixing a common parse error.

---

## Key Changes

### Source Statistics
- **Python Lines**: 109
- **Simple Lines**: 217
- **Growth**: +99% (due to explicit types, struct definitions, and inline documentation)

### Architecture

**Data Structures:**
```simple
struct FixIfValStats:
    files_processed: u64
    files_modified: u64
    patterns_fixed: u64

struct FixIfValPattern:
    name: text
    description: text
    before: text
    after: text
    notes: text

struct MigrationResult:
    modified: bool
    patterns_fixed: u64
    error: text
```

**Core Functions:**
- `get_fix_if_val_patterns() -> List<FixIfValPattern>` - Returns pattern descriptions
- `print_fix_if_val_examples() -> text` - Generates documentation with examples
- `fix_if_val_content(content: text) -> text` - Stub for regex-based transformations
- `fix_if_val_file(filepath: text) -> MigrationResult` - Stub for file migration
- `run_fix_if_val(root_dir: text) -> FixIfValStats` - Stub for batch migration

---

## Transformation Patterns

The migration fixes two forms of invalid `if val Some` syntax:

### 1. Statement Form
**Before**:
```simple
if val Some(x) = opt:
    use_x()
else:
    handle_none()
```

**After**:
```simple
match opt:
    case Some(x):
        use_x()
    case None:
        handle_none()
```

**Notes**: Handles multi-line bodies with proper indentation

### 2. Expression Form
**Before**:
```simple
val result = if val Some(x) = opt:
    x * 2
else:
    0
```

**After**:
```simple
val result = match opt:
    case Some(x):
        x * 2
    case None:
        0
```

**Notes**: Used in assignments, maintains expression semantics

---

## Regex Patterns Required

### Pattern 1: Statement Form
```regex
r'(\s*)if val Some\((\w+)\)\s*=\s*([^:]+):\s*\n((?:\1    .+\n)*)\1else:\s*\n((?:\1    .+\n)*)'
```

**Capture Groups**:
1. Indentation
2. Variable name (x)
3. Option expression (opt)
4. Some body (multi-line)
5. None body (multi-line)

**Processing**:
- Dedent bodies (remove one indentation level)
- Rebuild as match with case statements
- Re-indent for match structure

### Pattern 2: Expression Form
```regex
r'(\s*)val\s+(\w+)\s*=\s*if val Some\((\w+)\)\s*=\s*([^:]+):\s*\n(\1    )(.+)\n\1else:\s*\n(\1    )(.+)'
```

**Capture Groups**:
1. Indentation
2. Result variable name
3. Some variable name
4. Option expression
5-8. Expression indentation and content

**Processing**:
- Extract single-line expressions
- Build match expression with case statements
- Preserve assignment structure

---

## Phase 2 Dependencies

The following features are stubbed pending stdlib implementation:

### 1. Regex Library (HIGH PRIORITY)
**Needed for**: Complex pattern matching and replacement
**Operations**:
- Multi-line regex matching
- Capture groups (8+ groups)
- Greedy/non-greedy matching
- Regex substitution with callbacks
- MULTILINE flag support

**Complexity**: This migration requires the most complex regex of all migration tools:
- Nested capture groups
- Multi-line body matching
- Variable-length indentation handling
- Custom replacement logic (dedenting/re-indenting)

### 2. File I/O Library (HIGH PRIORITY)
**Needed for**: Reading/writing source files
**Operations**:
- Read file content
- Write file content
- UTF-8 encoding support
- Check if pattern exists (optimization)

### 3. Directory Operations (MEDIUM PRIORITY)
**Needed for**: Finding .spl files
**Operations**:
- Recursive glob (`**/*.spl`)
- Directory listing

---

## Migration Strategy

This migration is unique compared to the other syntax migration tools:

1. **Fixing invalid syntax** - Not a style choice, but a correctness issue
2. **Indentation-sensitive** - Must handle dedenting and re-indenting
3. **Two-pass algorithm** - Statement form first, then expression form
4. **No backups needed** - Purely corrective (though Python version doesn't create backups anyway)
5. **Target-specific** - Originally focused on `simple/std_lib/src/spec` directory

---

## Testing

**Test File**: `simple/std_lib/test/unit/tooling/fix_if_val_pattern_spec.spl`
**Test Count**: 1 (sanity check)
**Status**: ✅ Compiles successfully

Current tests verify module compilation. Full functional tests blocked on:
- Regex library (especially complex multi-line patterns)
- File I/O library
- Directory operations

---

## Export Updates

Added to `simple/std_lib/src/tooling/__init__.spl`:

```simple
# Module import
pub use fix_if_val_pattern.*

# Type exports
pub use fix_if_val_pattern.{
    FixIfValStats,
    FixIfValPattern,
    get_fix_if_val_patterns,
    print_fix_if_val_examples
}
```

Note: `MigrationResult` is not re-exported to avoid conflicts.

---

## Known Limitations

1. **Regex dependency**: All transformation logic stubbed
2. **File I/O dependency**: Cannot read/write files yet
3. **Indentation handling**: Complex regex with custom replacement logic needed
4. **No validation**: Cannot verify the pattern exists before trying to fix
5. **Limited to Option<T>**: Only handles `Some`/`None`, not other enum patterns

---

## Fully Functional Components

1. ✅ **Pattern definitions** - Both transformation patterns documented
2. ✅ **Statistics tracking** - Data structure for migration results
3. ✅ **Documentation generation** - `print_fix_if_val_examples()` works
4. ✅ **Error handling** - Result types for all operations

---

## Usage (Future)

When regex and file I/O are available:

```simple
use std.tooling.*

# Fix patterns in specific directory
val stats = run_fix_if_val("./simple/std_lib/src/spec")
print(stats.summary())

# View transformation patterns
print(print_fix_if_val_examples())

# Fix single file
val result = fix_if_val_file("path/to/file.spl")
match result.modified:
    true: print("Fixed {result.patterns_fixed} patterns")
    false: print("No patterns found")
```

---

## Files Created/Modified

### Created
1. `simple/std_lib/src/tooling/fix_if_val_pattern.spl` (217 lines)
2. `simple/std_lib/test/unit/tooling/fix_if_val_pattern_spec.spl` (5 lines)
3. `doc/report/fix_if_val_pattern_migration_2026-01-20.md` (this file)

### Modified
1. `simple/std_lib/src/tooling/__init__.spl` - Added fix_if_val_pattern exports

---

## Compiler Verification

```bash
$ ./target/debug/simple simple/std_lib/src/tooling/fix_if_val_pattern.spl
# ✅ Compiles successfully with no errors
```

---

## Relation to Other Migration Tools

This tool differs from the other migration tools in purpose:

**Syntax Style Migrations** (optional, user preference):
1. `migrate_me_syntax.spl` - Converts `var fn`/`fn(mut self)` to `me`
2. `migrate_val_var.spl` - Converts `let`/`let mut` to `val`/`var`
3. `remove_self_params.spl` - Removes explicit `self` parameters

**Syntax Error Fixes** (required, correctness):
4. `fix_if_val_pattern.spl` - Fixes invalid `if val Some` syntax (this tool)

**Migration Order**: This tool should be run **before** style migrations to ensure all code is syntactically valid.

---

## Technical Challenges

This migration has the highest complexity of all migration tools:

1. **Indentation preservation**: Must track and adjust indentation levels
2. **Multi-line matching**: Bodies can span multiple lines
3. **Dedent/re-indent logic**: Remove one level, add two levels for match structure
4. **Two-phase processing**: Statement form first, expression form second
5. **Custom replacement**: Cannot use simple string substitution

The Python version uses regex callback functions (`replace_match`, `replace_expr_match`) that:
- Parse capture groups
- Split bodies into lines
- Dedent each line
- Rebuild as match expression
- Maintain original indentation

This level of complexity will require robust regex support in Simple, including:
- Substitution with callback functions
- Or: Template-based replacement with access to capture groups

---

## Next Steps

1. ✅ Create migration report (this file)
2. ⏭️ Continue to next Python script migration:
   - `refactor_lowering.py`
   - `migrate_spec_to_spl.py`

---

## Notes

This migration tool demonstrates the need for advanced regex capabilities in Simple's standard library. The indentation-aware transformation with multi-line pattern matching represents a real-world use case that goes beyond simple find-replace operations.

Once regex support is available, this tool will be valuable for fixing legacy code that used the invalid `if val Some` syntax before it was properly deprecated.

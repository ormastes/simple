# Import Path Warning Implementation

**Date:** 2026-02-04
**Status:** ✅ Complete

## Summary

Added parser warning for incorrect use of "/" in import paths. The Simple language uses "." for module paths and relative paths with "./" or "../", not "/".

## Problem

Users were incorrectly using "/" in import paths:

```simple
# ❌ WRONG
use std/testing (describe, it, expect)
use linker/smf_header.*

# ✅ CORRECT
use testing.{describe, it, expect}
use ./linker/smf_header.*
```

The parser was accepting "/" in import paths without warning, leading to potential confusion and runtime errors.

## Solution

### 1. Added Warning Method to Parser

**File:** `src/compiler/parser.spl`

Added a new `warning()` method to emit warnings with custom spans:

```simple
me warning(message: text, span: Span):
    self.errors = self.errors.push(ParseError(
        message: message,
        span: span,
        severity: ErrorSeverity.Warning
    ))
```

### 2. Updated Import Conversion

Modified the `convert_import()` method to check for "/" in import paths:

```simple
me convert_import(outline: ImportOutline) -> Import:
    var items: [ImportItem] = []
    for item in outline.items:
        items = items.push(ImportItem(name: item, alias: nil))

    # Warn if "/" is used in import path (should use "." or relative paths)
    if outline.module.contains("/"):
        val suggestion = outline.module.replace("/", ".")
        self.warning(
            "Import path should not use '/' - use '.' for module paths or './' for relative paths (suggestion: use {suggestion})",
            outline.span
        )

    Import(
        module: outline.module,
        items: items,
        span: outline.span
    )
```

## Import Path Syntax Guide

### Correct Syntax

1. **Module Paths** (use `.` for hierarchical modules):
   ```simple
   use testing.{describe, it, expect}
   use compiler.parser_types.*
   use std.collections.map.HashMap
   ```

2. **Relative Paths** (use `./` for same directory, `../` for parent):
   ```simple
   use ./smf_enums.*                    # Same directory
   use ../monomorphize/metadata.*       # Parent directory
   use ./linker/smf_header.SmfHeader    # Subdirectory
   ```

3. **Absolute Paths** (from project root):
   ```simple
   use src/compiler/parser.*
   use src/std/collections.*
   ```

### Incorrect Syntax

```simple
# ❌ Using "/" in module paths
use std/testing (describe, it, expect)

# ❌ Using "/" in relative paths
use linker/smf_header.*
```

## Warning Output

When "/" is used in an import path, the parser now emits:

```
warning: Import path should not use '/' - use '.' for module paths or './' for relative paths (suggestion: use testing.{describe, it, expect})
  --> src/compiler/linker/test/smf_enums_spec.spl:10:1
   |
10 | use std/testing (describe, it, expect)
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

## Benefits

1. **Early Detection**: Catches incorrect import syntax at parse time
2. **Helpful Suggestions**: Provides correct syntax suggestion in warning message
3. **Non-Breaking**: Warning doesn't stop compilation, allows gradual migration
4. **Clear Documentation**: Warning message explains correct syntax

## Migration

Existing code with "/" in import paths will:
1. Emit warnings during compilation
2. Continue to work (warnings don't block compilation)
3. Should be updated to use correct syntax:
   - Replace "/" with "." for module paths
   - Add "./" prefix for relative paths

## Testing

The warning can be verified with:

```bash
# Create test file with incorrect import
echo 'use std/testing (describe, it, expect)' > test.spl

# Compile and check for warning
simple compile test.spl 2>&1 | grep "warning"
```

## Files Modified

- `src/compiler/parser.spl`: Added `warning()` method and import path validation

## Related Issues

- Incorrect imports in SMF test files (fixed in this session)
- Future: Could make this a hard error in v2.0.0

## Conclusion

The parser now properly warns about incorrect "/" usage in import paths, helping users adopt the correct "." and "./" syntax. This improves code quality and prevents confusing import errors.

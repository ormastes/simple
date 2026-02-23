# Import Errors in Pure Simple - Analysis & Solutions

**Date:** 2026-02-07
**Status:** Analysis Complete

## Executive Summary

Import errors in Pure Simple occur due to misunderstandings about module loading behavior. The core issue: **`use module_name` loads the module but doesn't expose its functions**. You must explicitly import function names.

## Critical Import Rules

### ✅ CORRECT Patterns

```simple
# Pattern 1: Explicit function import (RECOMMENDED)
use app.io.{file_exists, file_delete, rt_timestamp_now}

# Pattern 2: Import with wildcard (use sparingly)
use app.io.*

# Pattern 3: Explicit module path
use app.io.mod.{file_exists, file_delete}

# Pattern 4: Import from submodule
use lib.database.core.{StringInterner, SdnTable}
```

### ❌ INCORRECT Patterns

```simple
# ❌ WRONG: Loads module but functions NOT accessible
use app.io

# This will fail:
file_exists("test.txt")  # ERROR: function not found

# ❌ WRONG: Using deprecated 'import' keyword
import std.spec  # Generates deprecation warning

# ❌ WRONG: Trying to use functions without importing them
use app.io  # Module loaded, but...
print file_exists("x")  # ERROR: file_exists not found!
```

## Why This Happens

### Module Loading Behavior

When you write `use app.io`:

1. ✅ The module `app.io.mod` is loaded
2. ✅ The module's code is executed
3. ❌ **Functions are NOT added to your namespace**
4. ❌ You cannot call any of the module's functions

This is different from Python's `import app.io` which creates a module object you can access with `app.io.function()`.

In Simple, there's no module object - you must explicitly import names:

```simple
# This loads AND imports functions:
use app.io.{file_exists, file_write}

# Now you can use them:
if file_exists("data.txt"):
    file_write("output.txt", "hello")
```

## Common Import Error Categories

### 1. Module Path Resolution

**Problem:** Cannot find module

```
Error: module not found: lib.database
```

**Solution:** Check module path structure

```simple
# For src/lib/database/core.spl:
use lib.database.core.{StringInterner}

# For src/lib/database/mod.spl (directory module):
use lib.database.{something}
```

**Module Search Paths:**
- Current directory: `.`
- Library directory: `./lib`
- Standard library: `./src/lib/src`
- Application directory: `./src/app`

### 2. Function Not Found After Import

**Problem:** Module imported but function not accessible

```simple
use app.io  # ❌ Wrong!
file_exists("test")  # ERROR: function not found
```

**Solution:** Explicitly import function names

```simple
use app.io.{file_exists}  # ✅ Correct!
file_exists("test")  # Works!
```

### 3. Import vs Use Keyword

**Problem:** Deprecation warning

```
warning: Deprecated: 'import' keyword
Use 'use' instead of 'import'
```

**Solution:** Replace `import` with `use`

```simple
# Old (deprecated):
import std.spec

# New (correct):
use std.spec.*
```

### 4. Wildcard Import Issues

**Problem:** Using `*` doesn't import everything as expected

```simple
use lib.database.*  # May not import nested modules
```

**Solution:** Be explicit about what you need

```simple
# Better:
use lib.database.core.{StringInterner, SdnTable}
use lib.database.bug.{BugDatabase, Bug}
```

## Module Structure & Exports

### How Exports Work

Modules must explicitly export their public API:

```simple
# In src/app/io/mod.spl:

# Define function
fn file_exists(path: text) -> bool:
    shell_bool("test -f '{path}'")

# Export it
export file_exists

# Can export multiple at once
export file_write, file_read, file_delete
```

### Directory Modules

For a directory to be a module, it needs either:
- `__init__.spl` file
- `mod.spl` file

Example structure:
```
src/lib/database/
  ├── mod.spl          # Directory module (defines exports)
  ├── core.spl         # Submodule
  ├── bug.spl          # Submodule
  └── feature.spl      # Submodule
```

Import from directory module:
```simple
# From mod.spl:
use lib.database.{something_from_mod}

# From submodule:
use lib.database.core.{StringInterner}
```

## Fixing Import Errors - Step by Step

### Step 1: Identify the Error

```
Error: function 'file_write' not found
```

### Step 2: Find the Module

```bash
# Search for the function definition
grep -r "fn file_write" src/
# Result: src/app/io/mod.spl
```

### Step 3: Check Exports

```bash
# Check if function is exported
grep "export.*file_write" src/app/io/mod.spl
# Result: export file_exists, file_read, file_write, ...
```

### Step 4: Fix Import

```simple
# Add explicit import:
use app.io.{file_write}
```

## Migration Guide

### Fixing Existing Code

**Pattern 1: Fix module-only imports**

```simple
# Before (broken):
use app.io
file_write("test.txt", "data")  # ERROR!

# After (fixed):
use app.io.{file_write}
file_write("test.txt", "data")  # Works!
```

**Pattern 2: Replace deprecated `import`**

```bash
# Find all uses:
grep -r "^import " test/

# Replace:
sed -i 's/^import \(.*\)$/use \1.*/' file.spl
```

**Pattern 3: Add missing function imports**

```simple
# Before:
use lib.database

# After:
use lib.database.core.{StringInterner, SdnDatabase}
use lib.database.bug.{BugDatabase}
```

## Best Practices

### ✅ DO

1. **Always import explicitly:**
   ```simple
   use module.{func1, func2, Class1}
   ```

2. **Group related imports:**
   ```simple
   use std.spec.{describe, it, expect}
   use app.io.{file_read, file_write, file_exists}
   ```

3. **Use relative paths for local modules:**
   ```simple
   use .utils.{helper_function}
   ```

4. **Check exports before importing:**
   ```bash
   grep "^export" src/app/io/mod.spl
   ```

### ❌ DON'T

1. **Don't use bare module import:**
   ```simple
   use app.io  # ❌ Functions won't be accessible
   ```

2. **Don't use deprecated `import`:**
   ```simple
   import std.spec  # ❌ Use 'use' instead
   ```

3. **Don't assume wildcard imports everything:**
   ```simple
   use lib.database.*  # May not include submodules
   ```

4. **Don't import without checking exports:**
   ```simple
   use module.{NonExistentFunction}  # Will fail if not exported
   ```

## Testing Import Patterns

### Verify Import Works

```simple
# test_import.spl
use app.io.{file_write, file_read, file_exists}

fn test_import():
    file_write("test.txt", "hello")
    val content = file_read("test.txt")
    val exists = file_exists("test.txt")
    print "Import test: {exists && content == 'hello'}"

test_import()
```

Run with:
```bash
bin/simple_runtime test_import.spl
```

### Debug Import Issues

```simple
# 1. Check if module loads
use app.io.*
print "Module loaded successfully"

# 2. Try to call function
try:
    file_exists("test")
    print "Function callable"
except:
    print "Function not found - check import"
```

## Known Issues & Workarounds

### Issue 1: Module var exports broken

**Problem:** Exported `var` variables not accessible outside module

**Workaround:** Use functions to access/modify vars:
```simple
# In module:
var internal_counter = 0

fn get_counter() -> i64:
    internal_counter

fn increment_counter():
    internal_counter = internal_counter + 1

export get_counter, increment_counter
```

### Issue 2: Imported class constructors fail

**Problem:** `ClassName(field: value)` fails for imported classes

**Workaround:** Define helper function in importing module:
```simple
use lib.database.core.{StringInterner}

fn make_interner() -> StringInterner:
    StringInterner(str_to_id: {}, id_to_str: {}, next_id: 0)

val interner = make_interner()
```

### Issue 3: Import alias contains module exports

**Problem:** Import with alias doesn't expose module contents

```
Error: variable `sp` not found
```

**Workaround:** Import functions directly, not module:
```simple
# Instead of:
use std.spec as sp  # ❌ Doesn't work

# Do:
use std.spec.{describe as sp_describe, it as sp_it}  # ✅ Works
```

## Summary Table

| Pattern | Works? | Notes |
|---------|--------|-------|
| `use app.io.{func}` | ✅ | Recommended |
| `use app.io.*` | ✅ | Imports all exports |
| `use app.io` | ❌ | Loads but doesn't expose |
| `import app.io` | ⚠️  | Deprecated, use `use` |
| `use .local.{func}` | ✅ | Relative import |
| `use mod.{Type}` | ✅ | Import types |
| `use mod as alias` | ❌ | Alias doesn't expose exports |

## Action Items

### For Users

1. Replace all bare `use module` with explicit imports
2. Replace `import` keyword with `use`
3. Check module exports before importing
4. Use explicit import lists for clarity

### For Compiler

1. Add lint rule: warn on bare `use module` without `.*` or `{...}`
2. Better error messages for "function not found" → suggest import
3. Auto-fix for deprecated `import` → `use`
4. Module introspection: `simple info module app.io` to show exports

## References

- **Memory Notes:** `.claude/memory/MEMORY.md` - Import bug documentation
- **CLAUDE.md:** "CRITICAL: Module Import & Type Conversion Bugs"
- **Module Evaluator:** `src/app/interpreter.module/evaluator.spl`
- **Import Helper:** `src/app/interpreter.helpers/imports.spl`
- **SFFI Module:** `src/app/io/mod.spl` - Main SFFI exports

---

**Next Steps:**
1. Add lint rule to catch bare module imports
2. Update documentation with import best practices
3. Add auto-fix for common import patterns
4. Create module export introspection tool

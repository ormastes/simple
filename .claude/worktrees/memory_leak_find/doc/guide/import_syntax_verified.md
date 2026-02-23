# Import Syntax - Verified Patterns (2026-02-08)

This guide documents the **verified working** import patterns for Simple modules.

## Summary

✅ **Both syntaxes work for mod.spl files**
✅ **Curly braces `{}` preferred** for consistency
✅ **Imports must be at module level**

## Syntax Comparison

### Curly Braces (Recommended)

```simple
use app.io.{env_get, env_set, shell}
use app.cli.dispatch.{find_command, dispatch_command}
use std.spec.{describe, it, expect}
```

**Advantages:**
- Consistent with all other imports
- Standard syntax used throughout codebase
- Shorter, cleaner

### Parentheses (Alternative)

```simple
use app.io.mod (env_get, env_set, shell)
use app.cli.dispatch.mod (find_command)  # Only if dispatch has mod.spl
```

**When to use:**
- When you want to be explicit about importing from `mod.spl`
- Debugging import issues (helps identify which file is being imported)

## Verified Examples

### Test Case: import_syntax_spec.spl

All 5 tests passing:

```simple
use std.spec.{describe, it, expect}

# Both syntaxes work:
use app.io.{env_get, env_set, shell}          # Curly braces ✅
use app.io.mod (file_exists, cwd)             # Parentheses ✅

describe "Import Syntax":
    it "curly braces work":
        val result = env_get("PATH")
        expect result.len() > 0

    it "parentheses work":
        val result = file_exists("test/file.spl")
        expect result == true
```

**Result:** 5/5 tests passing

## Common Patterns

### Standard Library

```simple
# SSpec framework
use std.spec.{describe, it, expect, context}

# String utilities
use std.text.{trim, split, join}

# Math functions
use std.math.{sin, cos, sqrt}
```

### Application Modules

```simple
# I/O operations
use app.io.{file_read, file_write, shell}

# CLI dispatch
use app.cli.dispatch.{find_command, dispatch_command}

# Database
use lib.database.core.{StringInterner, SdnDatabase}
```

### Module with Explicit .mod

```simple
# When you want to be explicit
use app.io.mod (env_get, env_set)

# Equivalent to curly braces
use app.io.{env_get, env_set}
```

## Rules and Limitations

### ✅ DO

- **Import at module level** (top of file)
- **Use curly braces** for consistency
- **List specific functions** - explicit is better than implicit
- **Group related imports** by module

```simple
# Good
use std.spec.{describe, it, expect}
use app.io.{file_read, file_write, shell}

describe "My Tests":
    it "works":
        # ...
```

### ❌ DON'T

- **Import inside functions/blocks** - won't work
- **Use bare imports** - `use app.io` doesn't expose functions
- **Use wildcard imports** - `use app.io.*` (avoid, hard to track dependencies)

```simple
# Bad - imports inside function
describe "My Tests":
    it "fails":
        use app.io.{shell}  # ❌ Won't work
        # ...

# Bad - bare import
use app.io  # ❌ Functions not accessible
```

## Troubleshooting

### "function not found" error

**Problem:** Import inside function block
```simple
it "test":
    use app.io.{shell}  # ❌ Fails
    shell("echo hi")
```

**Solution:** Move import to module level
```simple
use app.io.{shell}  # ✅ Works

it "test":
    shell("echo hi")
```

### "module imports as dict type"

**Problem:** Trying to use bare import
```simple
use app.io  # Loads module but doesn't expose functions

it "test":
    shell("echo hi")  # ❌ function not found
```

**Solution:** Use explicit function list
```simple
use app.io.{shell}  # ✅ Explicitly import shell

it "test":
    shell("echo hi")
```

## Migration Guide

### Old (Incorrect Assumption)

```simple
# We thought this was needed:
use app.io.mod (env_get, env_set)
```

### New (Correct Pattern)

```simple
# Both work, curly braces preferred:
use app.io.{env_get, env_set}
use app.io.mod (env_get, env_set)  # Also works
```

### Update Your Code

**Before:**
```simple
use app.io.mod (file_read, file_write)
use app.io.mod (shell)
use app.io.mod (env_get, env_set)
```

**After:**
```simple
use app.io.{file_read, file_write, shell, env_get, env_set}
```

## Verification

Run the import syntax test suite:

```bash
bin/simple_runtime test/integration/import_syntax_spec.spl
```

Expected output:
```
Import Syntax for mod.spl Files
  Curly braces syntax: use app.io.{...}
    ✓ imports env_get with curly braces
    ✓ imports env_set with curly braces
    ✓ imports shell with curly braces
  Parentheses syntax: use app.io.mod (...)
    ✓ imports file_exists with parentheses
    ✓ imports cwd with parentheses

5 examples, 0 failures
```

## References

- **Test Spec:** `test/integration/import_syntax_spec.spl`
- **Memory:** `MEMORY.md` - Import System section
- **Session Report:** `doc/report/test_fix_session_2026-02-08.md`

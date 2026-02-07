# Import Errors - Quick Fix Guide

**TL;DR:** Import errors happen because `use module` loads the module but doesn't expose its functions. **Always import explicitly.**

## The Problem

```simple
# ❌ THIS DOESN'T WORK
use app.io
file_write("test.txt", "data")  # ERROR: function not found!
```

**Why?** `use app.io` loads the module but doesn't add functions to your namespace.

## The Solution

```simple
# ✅ THIS WORKS
use app.io.{file_write}
file_write("test.txt", "data")  # Success!

# ✅ OR import multiple functions
use app.io.{file_write, file_read, file_exists}

# ✅ OR import everything
use app.io.*
```

## 3 Rules for Imports

1. **Always use explicit imports**: `use module.{func1, func2}`
2. **Never use bare imports**: `use module` (without `.*` or `{...}`)
3. **Use `use` not `import`**: `import` is deprecated

## Common Patterns

### File I/O
```simple
use app.io.{file_read, file_write, file_exists, file_delete}
```

### Testing
```simple
use std.spec.{describe, it, expect}
# Or:
use std.spec.*
```

### Database
```simple
use lib.database.core.{StringInterner, SdnTable, SdnDatabase}
use lib.database.bug.{BugDatabase, Bug}
```

## Quick Fixes

| Error | Fix |
|-------|-----|
| `function 'X' not found` | Add: `use module.{X}` |
| `Deprecated: 'import'` | Change `import` → `use` |
| `module not found` | Check file path and structure |
| `variable 'X' not found` after import alias | Import functions directly, not module |

## Tools

- **Quick Reference**: `doc/guide/import_quick_reference.md`
- **Full Analysis**: `doc/report/import_errors_analysis_2026-02-07.md`
- **Checker Script**: `script/check_imports.spl`

## Check Your Code

```bash
# Find problematic imports
grep -n "^use [a-z]" src/file.spl | grep -v "\.{\|\.\\*"

# Find deprecated imports
grep -n "^import " src/file.spl

# Find module exports
grep "^export" src/module.spl
```

## Most Common Mistakes

1. **Bare module import** (`use app.io` without `.*` or `{...}`)
2. **Using `import` instead of `use`**
3. **Forgetting to import functions** (assumes they're available)
4. **Importing non-exported functions** (check `export` statements)

---

**Remember:** In Simple, `use module.{functions}` is the way. Always be explicit!

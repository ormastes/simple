# Import Quick Reference - Simple Language

**Last Updated:** 2026-02-07

## TL;DR - Common Patterns

```simple
# ✅ CORRECT - Explicit import (recommended)
use app.io.{file_exists, file_write, file_read}

# ✅ CORRECT - Import all exports
use app.io.*

# ✅ CORRECT - Import from submodule
use lib.database.core.{StringInterner, SdnTable}

# ❌ WRONG - Bare module import (functions not accessible!)
use app.io  # Loads module but functions unusable!

# ❌ WRONG - Deprecated keyword
import std.spec  # Use 'use' instead
```

## Most Common Modules

### I/O Operations (`app.io`)

```simple
# File operations
use app.io.{file_exists, file_read, file_write, file_delete, file_copy}
use app.io.{file_append, file_atomic_write, file_size, file_hash_sha256}

# Directory operations
use app.io.{dir_create, dir_list, dir_walk, dir_remove, is_dir}

# Process operations
use app.io.{process_run, shell, ProcessResult}

# Environment
use app.io.{env_get, env_set, cwd, home}

# System info
use app.io.{getpid, hostname, cpu_count, host_arch, host_os}

# Time
use app.io.{rt_timestamp_now, current_time_ms, time_now_unix_micros}
```

### Testing (`std.spec`)

```simple
# Basic test functions
use std.spec.{describe, it, expect, context}

# Additional matchers
use std.spec.{check, check_msg}

# Or import everything
use std.spec.*
```

### Database (`lib.database`)

```simple
# Core types
use lib.database.core.{StringInterner, SdnTable, SdnRow, SdnDatabase}

# Bug tracking
use lib.database.bug.{BugDatabase, Bug, BugSeverity, BugStatus}

# Feature tracking
use lib.database.feature.{FeatureDatabase, Feature, FeatureStatus}

# Test tracking
use lib.database.test.{TestDatabase, TestResult, TestStatus}
```

## Error Messages & Fixes

### "function 'X' not found"

**Error:**
```
Error: function 'file_write' not found
```

**Fix:**
```simple
# Add explicit import:
use app.io.{file_write}
```

### "variable 'X' not found" (after import)

**Error:**
```
Error: variable 'sp' not found
```
```simple
use std.spec as sp  # This doesn't work!
sp.describe(...)    # ERROR: sp not found
```

**Fix:**
```simple
# Import functions directly:
use std.spec.{describe, it, expect}
describe "test":
    it "works":
        expect(true).to_equal(true)
```

### "Deprecated: 'import' keyword"

**Warning:**
```
warning: Deprecated: 'import' keyword
Use 'use' instead of 'import'
```

**Fix:**
```simple
# Change:
import std.spec

# To:
use std.spec.*
```

### "module not found"

**Error:**
```
Error: module not found: lib.database
```

**Fix:** Check module path and file structure
```bash
# List available modules:
find src/lib -name "*.spl" -o -name "mod.spl" | head

# Module structure must be:
src/lib/database/
  ├── mod.spl (or __init__.spl)
  └── core.spl

# Import as:
use lib.database.core.{StringInterner}
```

## Common Mistakes & Fixes

### Mistake 1: Bare Module Import

```simple
# ❌ WRONG
use app.io
file_write("test.txt", "data")  # ERROR: function not found

# ✅ CORRECT
use app.io.{file_write}
file_write("test.txt", "data")
```

### Mistake 2: Forgetting to Import

```simple
# ❌ WRONG
describe "test":  # ERROR: describe not found
    it "works":
        expect(1).to_equal(1)

# ✅ CORRECT
use std.spec.{describe, it, expect}
describe "test":
    it "works":
        expect(1).to_equal(1)
```

### Mistake 3: Import Without Export

```simple
# In module.spl:
fn my_function():
    print "hello"

# No export statement!

# In other file:
use module.{my_function}  # ERROR: my_function not exported
```

**Fix:** Add export to module
```simple
# In module.spl:
fn my_function():
    print "hello"

export my_function  # ✅ Now it's available
```

### Mistake 4: Wildcard on Directory Module

```simple
# ❌ WRONG (may not import submodules)
use lib.database.*
StringInterner(...)  # May not work

# ✅ CORRECT
use lib.database.core.{StringInterner}
StringInterner(...)
```

## Import Styles

### Style 1: Grouped by Category (Recommended)

```simple
# Testing framework
use std.spec.{describe, it, expect, check}

# I/O operations
use app.io.{file_read, file_write, file_exists}

# Database
use lib.database.core.{StringInterner, SdnDatabase}
use lib.database.bug.{BugDatabase}
```

### Style 2: One Import Per Line

```simple
use std.spec.{describe}
use std.spec.{it}
use std.spec.{expect}
```

### Style 3: Wildcard (Use Sparingly)

```simple
# Only for small modules with clear namespace
use std.spec.*
use app.io.*  # Imports many functions - can cause conflicts
```

## Checking Module Exports

### Method 1: Grep

```bash
# Find exports in a module
grep "^export" src/app/io/mod.spl

# Output:
# export file_exists, file_read, file_write, ...
```

### Method 2: Search for Function

```bash
# Find where function is defined
grep -r "fn file_write" src/

# Output:
# src/app/io/mod.spl:fn file_write(path: text, content: text) -> bool:
```

### Method 3: Module Info Tool

```bash
# (Future feature)
bin/simple info module app.io
# Would show all exported functions
```

## Module Search Paths

Simple searches for modules in these directories:

1. Current directory: `.`
2. Library directory: `./lib`
3. Standard library: `./src/lib/src`
4. Application directory: `./src/app`

Example:
```simple
use lib.database.core     # Looks for: ./src/lib/database/core.spl
use app.io                # Looks for: ./src/app/io/mod.spl
use std.spec              # Looks for: ./src/lib/src/spec.spl
```

## Import Resolution

### File Module

```
src/app/io/mod.spl
```

Import as:
```simple
use app.io.{function_name}
```

### Directory Module

```
src/lib/database/
  ├── mod.spl
  ├── core.spl
  └── bug.spl
```

Import as:
```simple
use lib.database.{something_from_mod}        # From mod.spl
use lib.database.core.{StringInterner}       # From core.spl
use lib.database.bug.{BugDatabase}           # From bug.spl
```

### Relative Imports

```simple
# In src/app/cli/main.spl:
use .utils.{helper_function}  # Looks for: src/app/cli/utils.spl

# In src/lib/database/core.spl:
use .atomic.{AtomicFile}      # Looks for: src/lib/database/atomic.spl
```

## Quick Checklist

When adding imports:

- [ ] Use `use` keyword (not `import`)
- [ ] Import functions explicitly: `use module.{func1, func2}`
- [ ] Check module exports with `grep "^export" module_file.spl`
- [ ] Verify module path matches file structure
- [ ] Group related imports together
- [ ] Use wildcard (`.*`) sparingly

## Getting Help

### Error?
1. Check this guide for the error message
2. Read full analysis: `doc/report/import_errors_analysis_2026-02-07.md`
3. Check memory notes: `.claude/memory/MEMORY.md`

### Can't Find Function?
```bash
# Search for it:
grep -r "fn function_name" src/

# Check exports:
grep "export.*function_name" $(grep -l "fn function_name" src/**/*.spl)
```

### Module Not Found?
```bash
# List available modules:
find src -name "mod.spl" -o -name "__init__.spl"

# Check structure:
ls -R src/path/to/module/
```

## Reference

- **Full Analysis:** `doc/report/import_errors_analysis_2026-02-07.md`
- **Language Guide:** `doc/guide/syntax_quick_reference.md`
- **Memory Notes:** `.claude/memory/MEMORY.md` (section: Module Import Bugs)
- **CLAUDE.md:** Project instructions (section: Critical Prohibitions)

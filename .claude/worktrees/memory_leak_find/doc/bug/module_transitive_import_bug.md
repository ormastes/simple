# Module System Bug: Transitive Imports Broken

**Severity:** P0 - Blocks modular code development
**Status:** Confirmed
**Discovered:** 2026-02-05
**Reproducible By:** test_minimal_transitive_import

---

## Summary

The Simple module system fails to preserve imports when modules are loaded transitively. When module A imports module B, and module B imports module C, **module B loses access to C's exports at runtime**.

---

## Minimal Reproduction

### Setup

Create three modules:

**File:** `test/lib/module_c.spl`
```simple
export helper_function

fn helper_function() -> text:
    "works"
```

**File:** `test/lib/module_b.spl`
```simple
use test.lib.module_c.{helper_function}

export call_helper

fn call_helper() -> text:
    helper_function()  # ERROR: function not found at runtime
```

**File:** `test/lib/test_transitive.spl`
```simple
use test.lib.module_b.{call_helper}

describe "Transitive import test":
    it "calls through module chain":
        val result = call_helper()
        assert result == "works"
```

### Result

```
✗ calls through module chain
  semantic: function `helper_function` not found
```

Module B can see `helper_function` when run directly, but loses access when imported by module A.

---

## Real-World Impact

### MCP Server Blocked

The MCP server cannot start because:
1. `src/app/mcp/bugdb_resource.spl` imports `lib.database.bug`
2. `lib.database.bug` imports `app.io` for file operations
3. When MCP server imports bugdb_resource, the bugdb_resource loses access to app.io functions

### Database Fixtures Broken

Test helper modules cannot import utility functions:
1. `test/intensive/helpers/database_fixtures.spl` imports `app.io.{file_exists}`
2. `test/intensive/database/query_intensive_spec.spl` imports `database_fixtures`
3. Fixtures lose access to `file_exists` at runtime

### Additional Parse Bug

In `test/intensive/helpers/` directory specifically, curly-brace imports from `app.io` cause parse errors:
```simple
use app.io.{file_exists}  # ERROR: Unexpected token: expected pattern, found Exists
```

This parse error does NOT occur in `test/lib/` directory with identical code.

---

## Current Workarounds

### 1. Inline All Code (Working)

Don't use modules - copy all code into single files:
```simple
# test/intensive/database/query_intensive_spec.spl
# No imports - all helpers inlined
fn cleanup_test_file(path: text):
    # implementation here

fn generate_simple_bug(id: text) -> Bug:
    # implementation here

describe "Tests":
    it "works":
        cleanup_test_file("/tmp/test")
        # ✅ Works - no module loading
```

**Status:** ✅ Working - 7/7 query tests passing with inlined helpers

### 2. Direct Extern Declarations (Working)

Declare extern functions directly in the module that needs them:
```simple
# test/lib/database_fixtures.spl
use lib.database.bug

# Workaround: declare externs directly
extern fn rt_file_exists(path: text) -> bool
extern fn rt_file_delete(path: text) -> bool

fn file_exists(path: text) -> bool:
    rt_file_exists(path)

fn file_delete(path: text) -> bool:
    rt_file_delete(path)

fn cleanup_test_file(path: text):
    if file_exists(path):
        file_delete(path)
```

**Status:** ✅ Working - 7/7 query tests passing with extern workaround

### 3. Fixed Values Instead of Runtime Functions (Working)

Use compile-time constants instead of runtime function calls:
```simple
# Instead of:
created_at: rt_timestamp_now()  # Requires extern function

# Use:
created_at: "2026-02-05T00:00:00"  # Fixed string
```

**Status:** ✅ Working - All tests use fixed timestamps

---

## What Works vs What Doesn't

### ✅ Working Import Patterns

**Single-level imports:**
```simple
# file_a.spl imports from file_b.spl directly
use lib.database.bug.{BugDatabase}  # ✅ Works
val db = BugDatabase(...)           # ✅ Functions available
```

**Type imports (always work):**
```simple
use lib.database.bug.{Bug, BugSeverity, BugStatus}  # ✅ Works
val bug = Bug(...)                                   # ✅ Types available
```

**Same directory imports:**
```simple
# test/lib/database_spec.spl
use lib.database.bug.{create_bug_database}  # ✅ Works when run directly
val db = create_bug_database("/tmp/test")   # ✅ Works
```

### ❌ Broken Import Patterns

**Transitive imports:**
```simple
# Module A imports Module B, Module B imports Module C
# → Module B loses access to C's exports
```

**Curly-brace imports from app.io in test/intensive/helpers/:**
```simple
use app.io.{file_exists}  # ❌ Parse error in helpers/ directory
```

**Runtime extern functions through imports:**
```simple
# database_fixtures.spl
use app.io.{rt_timestamp_now}  # ❌ Not found at runtime when fixtures imported
```

---

## Testing Status

### Query Tests: 7/7 PASSING ✅

Using extern workaround + fixed timestamps:
```
✓ retrieves all bugs
✓ retrieves open bugs
✓ gets bug statistics
✓ filters bugs by severity manually
✓ filters bugs by file field
✓ handles retrieving 1K bugs
✓ handles mixed status queries with 500 bugs
```

### Other Intensive Tests: Not Yet Fixed

- `core_intensive_spec.spl` - Needs same workaround applied
- `persistence_intensive_spec.spl` - Needs same workaround applied
- `bug_tracking_scenario_spec.spl` - Needs same workaround applied

---

## Root Cause Analysis

### Hypothesis

The module loader does not recursively carry imported symbols through the module chain:

1. Runtime loads `test_a.spl`
2. Encounters `use test.lib.module_b.{function_b}`
3. Loads `module_b.spl` and registers `function_b` in test_a's namespace
4. When loading `module_b.spl`, encounters `use test.lib.module_c.{function_c}`
5. **BUG:** Loads `module_c.spl` but does NOT register `function_c` in module_b's namespace
6. Result: `function_b` can't call `function_c` even though it imported it

### Likely Location

File: `rust/simple-compiler/src/interpreter/interpreter_module/module_evaluator.rs`

The module evaluation logic likely:
- ✅ Registers direct imports correctly
- ❌ Does not preserve imports when a module is loaded as a dependency of another module

---

## Fix Required

The compiler needs to ensure that when loading a module, all of its imports are evaluated and registered in that module's scope, regardless of whether the module is being loaded directly or as a dependency.

### Suggested Fix

In `module_evaluator.rs`, when processing a module's imports:

1. Before registering the module's exports in the parent scope
2. First ensure the module's own imports are fully resolved and available
3. Then evaluate the module's function bodies with access to those imports
4. Finally export the module's symbols to the parent

---

## Impact on Project

### Blocked Features

- ❌ MCP server startup (all resources and prompts)
- ❌ Modular test helpers
- ❌ Code reusability across modules
- ❌ Clean separation of concerns

### Forced Workarounds

- ✅ Inline all helpers (works but unmaintainable)
- ✅ Duplicate extern declarations (works but violates DRY)
- ✅ Use fixed values instead of runtime functions (works but inflexible)

---

## Recommendation

**Priority:** P0 - Critical compiler bug

This blocks all modular code development. Until fixed, Simple programs must either:
1. Be monolithic single-file applications
2. Use extensive code duplication
3. Rely on extern function declarations in every module

**Next Steps:**
1. Create minimal failing test case in Rust test suite
2. Add to compiler integration tests
3. Fix module import chain resolution
4. Verify all intensive tests pass without workarounds
5. Re-enable MCP server

---

## Related Issues

- MCP server parse errors (separate issue)
- Directory-specific parse bugs in `test/intensive/helpers/`
- Inconsistent module resolution between directories

---

**End of Report**

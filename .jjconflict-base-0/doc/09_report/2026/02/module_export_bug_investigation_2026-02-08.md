# Module Export Bug Investigation - 2026-02-08

## Executive Summary

**Root Cause Found:** The Simple runtime's `__init__.spl` re-export mechanism is broken. Functions imported in `__init__.spl` using `from X import {fn}` and then re-exported with `export fn` are not accessible to external modules.

**Impact:** Blocks 23+ test failures across async_runtime modules (actor_heap, actor_scheduler, lexer).

**Workaround:** Import directly from submodules instead of through parent `__init__.spl` files.

## Investigation Steps

### 1. Initial Hypothesis

Tests were failing with "function not found" errors for factory functions like `HeapConfig__default()`, `RunQueue__new()`, etc. Initial hypothesis was that exports were missing or in wrong location.

### 2. Testing Approach

Created minimal test cases to isolate the issue:

**Test Case 1: Working Module (std.spec)**
```simple
use std.spec.{describe, it, expect}
# Result: ✅ WORKS - Functions accessible
```

**Test Case 2: Broken Module (actor_heap)**
```simple
use app.interpreter.async_runtime.actor_heap.{HeapConfig__default}
# Result: ❌ FAILS - "function not found"
```

**Test Case 3: Through __init__ (async_runtime)**
```simple
use app.interpreter.async_runtime.{HeapConfig__default}
# Result: ❌ FAILS - "function not found"
```

### 3. Key Discovery

Created minimal reproduction case with custom module:

```bash
/tmp/test_module/
  __init__.spl  # from submod import {hello}; export hello
  submod.spl    # fn hello() -> text; export hello
```

**Test A: Import through __init__**
```simple
use test_module.{hello}
val msg = hello()  # ❌ FAILS - "function not found"
```

**Test B: Import directly from submodule**
```simple
use test_module.submod.{hello}
val msg = hello()  # ✅ WORKS - Returns "Hello from submod"
```

## Root Cause

**CONFIRMED: Dotted directory names break export registration!**

The runtime's module loader has a critical bug with dotted directory names:

1. **Normal directories work** - `src/test_modules/simple_test/helper.spl` exports correctly ✅
2. **Dotted directories fail** - `src/test_modules/dotted.module/helper.spl` exports don't register ❌
3. **All `interpreter.*` directories affected** - `interpreter.async_runtime`, `interpreter.call`, `interpreter.core`, etc.
4. **Imports succeed but exports fail** - Modules load without error, but exported functions are inaccessible
5. **Re-exports also broken** - The `__init__.spl` re-export pattern compounds the issue

### Test Results

| Directory Structure | Import Statement | Result |
|---------------------|------------------|--------|
| `src/test_modules/simple_test/helper.spl` | `use test_modules.simple_test.helper.{fn}` | ✅ Works |
| `src/test_modules/dotted.module/helper.spl` | `use test_modules.dotted.module.helper.{fn}` | ❌ Fails |
| `src/app/interpreter.async_runtime/actor_heap.spl` | `use app.interpreter.async_runtime.actor_heap.{fn}` | ❌ Fails |
| `/tmp/test_module/submod.spl` | `use test_module.submod.{fn}` | ✅ Works |

The pattern is clear: **Any directory with a dot in its name** breaks export registration.

## Affected Modules

All modules using `__init__.spl` re-export pattern:

- `app.interpreter.async_runtime` (actor_heap, actor_scheduler, mailbox)
- `compiler.lexer` (if accessed through parent)
- Any other directory-based modules with `__init__.spl`

## Working Modules

Modules that work correctly:

- `std.spec` - Single file module (no `__init__.spl`)
- `src/app/interpreter.async_runtime/actor_heap.spl` - When imported directly
- All submodules - When accessed directly, not through parent `__init__.spl`

## Fix Required

**CRITICAL: Directory names must not contain dots!**

The only proper fix is to rename all dotted directories to use underscores or nested paths:

### Affected Directories

```bash
src/app/interpreter.async_runtime/    → src/app/interpreter_async_runtime/  or  src/app/interpreter/async_runtime/
src/app/interpreter.call/             → src/app/interpreter_call/             or  src/app/interpreter/call/
src/app/interpreter.collections/      → src/app/interpreter_collections/      or  src/app/interpreter/collections/
src/app/interpreter.control/          → src/app/interpreter_control/          or  src/app/interpreter/control/
src/app/interpreter.core/             → src/app/interpreter_core/             or  src/app/interpreter/core/
src/app/interpreter.expr/             → src/app/interpreter_expr/             or  src/app/interpreter/expr/
src/app/interpreter.extern/           → src/app/interpreter_extern/           or  src/app/interpreter/extern/
src/app/interpreter.ffi/              → src/app/interpreter_ffi/              or  src/app/interpreter/ffi/
src/app/interpreter.helpers/          → src/app/interpreter_helpers/          or  src/app/interpreter/helpers/
src/app/interpreter.lazy/             → src/app/interpreter_lazy/             or  src/app/interpreter/lazy/
src/app/interpreter.memory/           → src/app/interpreter_memory/           or  src/app/interpreter/memory/
src/app/interpreter.module/           → src/app/interpreter_module/           or  src/app/interpreter/module/
src/app/interpreter.perf/             → src/app/interpreter_perf/             or  src/app/interpreter/perf/
src/app/interpreter.utils/            → src/app/interpreter_utils/            or  src/app/interpreter/utils/
```

### Recommended Structure

**Option A: Nested Directories (Cleaner)**
```
src/app/interpreter/
  ├── __init__.spl
  ├── async_runtime/
  │   ├── __init__.spl
  │   ├── actor_heap.spl
  │   └── actor_scheduler.spl
  ├── call/
  ├── collections/
  └── ...
```

**Option B: Underscore (Minimal Changes)**
```
src/app/
  ├── interpreter_async_runtime/
  ├── interpreter_call/
  ├── interpreter_collections/
  └── ...
```

### Migration Steps

1. Rename directories (use `mv` or `jj mv`)
2. Update all import statements across codebase
3. Update test imports
4. Verify all modules load correctly

**Note:** This is NOT a workaround - it's the REQUIRED fix. Dotted directory names are fundamentally incompatible with the runtime's module system.

## Test Fixes Required

All test files importing from `app.interpreter.async_runtime` need to change imports from:
```simple
use app.interpreter.async_runtime.{HeapConfig__default, ...}
```

To:
```simple
use app.interpreter.async_runtime.actor_heap.{HeapConfig__default, ...}
use app.interpreter.async_runtime.actor_scheduler.{RunQueue__new, ...}
```

## Files Affected

Tests needing import updates:
- `test/app/interpreter/async_runtime/actor_heap_spec.spl` (19 failures)
- `test/app/interpreter/async_runtime/actor_scheduler_spec.spl` (4 failures)
- `test/compiler/async_desugar_integration_spec.spl` (9 failures, needs lexer import fix)

Implementation files (no changes needed):
- `src/app/interpreter.async_runtime/actor_heap.spl` - Exports are correct
- `src/app/interpreter.async_runtime/actor_scheduler.spl` - Exports are correct
- `src/compiler/lexer.spl` - Exports are correct

## Runtime Bug Details

The bug appears to be in the module evaluation code (seen in warnings):

```
simple_compiler::interpreter::interpreter_module::module_evaluator::evaluation_helpers:476:
Export statement references undefined symbol name=<symbol>
```

This suggests the runtime's export handling doesn't properly register symbols that were imported from other modules.

## Recommended Actions

1. **Immediate:** Update test imports to use direct submodule paths (workaround)
2. **Short-term:** Document this limitation in CLAUDE.md and memory notes
3. **Long-term:** Fix runtime's `__init__.spl` re-export mechanism or deprecate this pattern

## Verification Commands

Test the bug with minimal case:
```bash
# Create test module
mkdir -p /tmp/test_module
cat > /tmp/test_module/submod.spl << 'EOF'
fn hello() -> text: "Hello"
export hello
EOF

cat > /tmp/test_module/__init__.spl << 'EOF'
from submod import {hello}
export hello
EOF

# Test direct import (works)
echo 'use test_module.submod.{hello}
fn main(): print hello()' > /tmp/test1.spl
SIMPLE_LIB=/tmp bin/bootstrap/linux-x86_64/simple /tmp/test1.spl

# Test through __init__ (fails)
echo 'use test_module.{hello}
fn main(): print hello()' > /tmp/test2.spl
SIMPLE_LIB=/tmp bin/bootstrap/linux-x86_64/simple /tmp/test2.spl
```

## Conclusion

This is a **critical runtime bug** caused by dotted directory names (`interpreter.async_runtime`). The module loader interprets dots in directory names as module path separators, but fails to properly register exports from these directories.

### Impact Assessment

- **23+ test failures** across async_runtime tests
- **Potentially hundreds more** in interpreter.* modules
- **Blocks all development** in affected modules until fixed

### Priority: CRITICAL

This bug must be fixed before:
1. Adding new async_runtime features
2. Expanding interpreter modules
3. Running full test suite

### Fix Options

1. **Rename directories** (Recommended) - 2-4 hours of work, permanent fix
2. **Fix runtime** (Complex) - Requires Rust changes to module loader
3. **Workaround** (Not viable) - Direct imports don't work either due to same bug

**Recommendation:** Rename all dotted directories to use nested structure (`interpreter/async_runtime/`) or underscores (`interpreter_async_runtime/`). This is the only practical solution.

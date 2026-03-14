# Bug: Module-level array `.len()` called twice corrupts variable (import only)

**Severity:** Critical
**Component:** Interpreter / Module Variable Binding
**Date:** 2026-03-13
**Status:** Fixed in source (deep-copy locals in mir_interpreter.spl:454-470), needs binary rebuild

## Summary

When a module is **imported** via `use`, calling `.len()` on a module-level
array variable **twice** in the same function corrupts the variable — it
becomes `i64(0)`. No mutation, no assignment needed. The second `.len()` call
sees the corrupted value and fails.

The bug occurs both when importing via `use` AND when running directly.
A single `.len()` call corrupts the variable for ALL subsequent operations
(`.push()`, `.slice()`, etc.), not just subsequent `.len()` calls.

## Minimal Reproducer

```simple
# file: src/lib/nogc_sync_mut/cli_output/_test_mut.spl
var arr: [text] = []

fn call_len_once() -> i64:
    arr.len()             # OK: returns 0

fn call_len_twice() -> i64:
    val a = arr.len()     # first call: OK, returns 0
    arr.len()             # second call: ERROR — arr is now i64(0)
```

```simple
# Import and call:
use std.cli_output._test_mut.{call_len_once, call_len_twice}
print call_len_once()    # OK: prints 0
print call_len_twice()   # ERROR: method `len` not found on type `i64`
```

## Key Findings

| Scenario | Result |
|----------|--------|
| `.len()` called once (return value only) | Works |
| `.len()` called twice in same fn | **Second call sees i64(0)** |
| `.len()` then `.push()` in same fn | **`.push()` sees i64(0)** — single `.len()` corrupts for ALL ops |
| Direct execution (no import) | **Also fails** — bug is NOT import-specific |
| Import via `use` | **Corrupts on second access** |
| `.push()` then `.len()` | Works (`.push()` does not corrupt) |
| `.push()` then `.push()` | Works |
| `.len()` across separate function calls | Works (each call is isolated) |
| One `.len()` per array, multiple arrays | Works |
| Cache `.len()` in local val, reuse val | Works (workaround) |
| `[i64]` arrays | Same behavior |
| `[text]` arrays | Same behavior |

## Root Cause

The MIR interpreter (`src/compiler/95.interp/mir_interpreter.spl`) stores ALL
variables (module-level AND function-local) in a single `self.locals` dict.

When a method call like `arr.len()` happens:

1. The receiver (`arr`) is read from `self.locals` via `get_operand()`
2. `.len()` is dispatched via `_call_function()`
3. `_call_function()` saves `self.locals` to CallFrame, then does `self.locals = {}`
4. The callee executes with fresh locals
5. `_pop_call_stack()` restores `self.locals` from the saved frame

**The bug:** The saved `frame.locals` is a **shallow reference**. When step 3
does `self.locals = {}`, it may interact with the same object that was saved
in the frame (dict assignment semantics). After the first `.len()` call, the
module-level variable slot is lost. The second `.len()` finds `i64(0)` (the
default from `self.locals[local.id] ?? 0`).

**Why it works on direct execution:** Without import, execution takes a
different code path that doesn't use the same `_call_function` mechanism for
built-in method calls.

**Fix:** Deep-copy `self.locals` before saving to CallFrame in `_call_function()`.
See `doc/research/module_var_len_corruption_research.md` for full analysis.

## Workaround

**Option A — Cache `.len()` in a local val (use once per var per function):**

```simple
fn works():
    val arr_len = arr.len()   # only call once
    if arr_len == 0: return
    val x = arr_len           # reuse cached value
```

**Option B — Manual length counters (avoid `.len()` entirely):**

Used in `buffer.spl`. Track array lengths with separate `i64` counters:

```simple
var _lp_buffer: [text] = []
var _lp_buf_len: i64 = 0       # manual counter

fn log_print(msg: text):
    if _lp_count > 0:          # check counter, not .len()
        _lp_buffer.push(msg)
        _lp_buf_len = _lp_buf_len + 1
```

## Affected Code

- `src/lib/nogc_sync_mut/cli_output/buffer.spl` — log point API
- `src/lib/nogc_sync_mut/log.spl` — log module (same pattern)
- Any imported module with module-level arrays accessed by `.len()` more than once

## TODO

- [x] Fix: Deep-copy `self.locals` in `_call_function()` before saving to CallFrame (applied in source)
- [ ] Rebuild `bin/release/simple` to pick up the fix
- [ ] Consider: Separate module-level storage (`self.globals`) from function locals
- [ ] Consider: Compile-time lint to warn on multiple `.len()` calls on module arrays

## Related

- Research doc: `doc/research/module_var_len_corruption_research.md`
- Intensive test spec: `test/system/module_import/module_var_len_corruption_spec.spl`
- Minimal reproducer fixture: `test/system/module_import/fixtures/var_mutation_corrupts_adjacent.spl`
- System spec: `test/system/module_import/module_import_new_submodule_spec.spl`
- Shared test module: `test/system/module_import/fixtures/len_test_module.spl`

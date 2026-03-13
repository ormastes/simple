# Research: Module Variable `.len()` Corruption in Interpreter

**Date:** 2026-03-13
**Status:** Open
**Severity:** High — silent data corruption on imported modules
**Component:** MIR Interpreter (`src/compiler/95.interp/mir_interpreter.spl`)

---

## Bug Summary

In the Simple language interpreter, calling `.len()` on a module-level array variable **twice** in the same function corrupts the variable when the module is **imported** via `use`. The second `.len()` call sees `i64(0)` instead of the array. Running the file directly works fine.

---

## Minimal Reproducer

```simple
# module.spl (in src/lib/)
var arr: [text] = []

fn call_len_once() -> i64:
    arr.len()              # OK

fn call_len_twice() -> i64:
    val a = arr.len()      # OK
    arr.len()              # ERROR: method `len` not found on type `i64`
```

---

## Root Cause Analysis

The MIR interpreter at `src/compiler/95.interp/mir_interpreter.spl` stores ALL variables (module-level AND function-local) in a single `self.locals` dict (`{i64: i64}` mapping LocalId.id -> value).

When a method call like `arr.len()` happens:

1. The receiver (`arr`) is read from `self.locals` via `get_operand()`
2. The `.len()` method is looked up and called via `_call_function()`
3. `_call_function()` saves `self.locals` to CallFrame, then does `self.locals = {}` (CLEARS everything)
4. The callee (`.len()`) executes with fresh locals
5. After return, `_pop_call_stack()` restores `self.locals` from the saved frame

The problem: the saved `frame.locals` is a **shallow reference**. When step 3 does `self.locals = {}`, it overwrites the SAME dict that was saved in the frame (since Simple's dict assignment is by-reference, not by-value). So when step 5 restores, it restores the EMPTY dict, not the original one.

After the first `.len()` call, the module-level variable is gone. The second `.len()` finds `i64(0)` (the default from `self.locals[local.id] ?? 0`).

### Update: Bug Also Occurs Without Import

Intensive testing revealed that the bug **also occurs on direct execution** (no
import). The earlier hypothesis that import-only was affected is incorrect.
Additionally, a single `.len()` call corrupts the variable for ALL subsequent
operations (`.push()`, `.slice()`, etc.), not just subsequent `.len()` calls.

---

## Interpreter Code Flow

Key locations:

- `src/compiler/95.interp/mir_interpreter.spl:107-113` -- `set_local()` and `get_local()` use `self.locals` dict
- `src/compiler/95.interp/mir_interpreter.spl:454-461` -- `_call_function()` saves `self.locals` to CallFrame then clears with `self.locals = {}`
- `src/compiler/95.interp/mir_interpreter.spl:523-533` -- `_pop_call_stack()` restores `self.locals = frame.locals`

---

## Fix Options

### Option A: Deep Copy on Save (Recommended, Simplest)

In `_call_function()`, deep-copy `self.locals` before saving to CallFrame:

```simple
# Before:
val frame = CallFrame(locals: self.locals, ...)

# After:
var saved_locals = {}
for key in self.locals.keys():
    saved_locals[key] = self.locals[key]
val frame = CallFrame(locals: saved_locals, ...)
```

This ensures the frame preserves the original dict even after `self.locals = {}`.

**Pros:** Minimal code change, directly addresses the root cause.
**Cons:** Adds a copy on every function call. For deeply nested dicts or large local scopes, this could have performance impact, though for typical use cases it should be negligible.

### Option B: Separate Module Variable Storage

Store module-level variables in `self.globals` instead of `self.locals`. The `globals` field already exists but is unused. This requires changes to:

- MIR lowering to emit different instructions for module vs local variables
- `get_local()` / `set_local()` to check scope

**Pros:** More architecturally correct. Module variables and local variables have different lifetimes and should not share storage.
**Cons:** Larger change surface. Requires coordination between the MIR lowering pass and the interpreter.

### Option C: Don't Clear, Use Scoped Overlay

Instead of `self.locals = {}`, create a new scope overlay:

- Push a new dict onto a scope stack
- Function locals go in the top scope
- Module variables stay in a lower scope
- Pop on return

**Pros:** Clean separation of scopes without changing MIR lowering.
**Cons:** Requires refactoring `get_local()` / `set_local()` to walk the scope stack. Moderate complexity.

---

## Compile-Time Prevention

A static analysis lint could detect:

1. Module-level `var` declarations with array types
2. Functions that call methods on those vars more than once
3. Emit a warning: "multiple method calls on module-level array may trigger corruption"

This is a **workaround**, not a fix. The real fix is Option A or B above.

---

## Runtime Detection

Add a diagnostic mode to the interpreter that:

1. Tracks which LocalIds correspond to module-level variables
2. After each `_pop_call_stack()`, verifies module-level variables still have their expected types
3. On type change, emit: `[WARN] Module variable {name} changed type after method call`

---

## Workaround (Until Fix Is Applied)

Cache all `.len()` results in local variables. Never call `.len()` on the same module-level array more than once per function:

```simple
# BAD:
fn broken():
    if arr.len() == 0: return    # first call
    val x = arr.len()             # second call: CRASH

# GOOD:
fn works():
    val arr_len = arr.len()       # only call once
    if arr_len == 0: return
    val x = arr_len               # use cached value
```

---

## Affected Code

- `src/lib/nogc_sync_mut/cli_output/buffer.spl` -- log point API
- `src/lib/nogc_sync_mut/log.spl` -- log module (same pattern)
- Any imported module using module-level arrays with repeated `.len()` calls

---

## Test Coverage

- `test/system/module_import/module_import_new_submodule_spec.spl` -- system spec
- `test/system/module_import/fixtures/` -- reproducer fixtures

---

## Recommendation

**Option A (Deep Copy on Save)** should be applied immediately as it is the smallest, safest fix. Option B (Separate Module Variable Storage) should be considered as a follow-up refactor to improve the interpreter architecture and prevent similar classes of bugs in the future.

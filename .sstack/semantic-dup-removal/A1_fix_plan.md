# A1 Fix Plan: `me` free-function field reassignment not propagated to caller

**Date:** 2026-04-28
**Author:** investigator agent (read-only pass)
**Status:** ready for implementation

---

## Root Cause

Two separate sites in the interpreter both discard updated `self` after calling a
`me` free function. Neither site performs writeback when the callee is `is_me_method=true`
and the first argument is an Object.

### Path 1 — explicit free-function call: `moduleloader_unload(self, path)`

File: `src/compiler_rust/compiler/src/interpreter_call/mod.rs` line ~99

```rust
// Priority 4: Check regular functions (user-defined)
if let Some(func) = functions.get(name).cloned() {
    return core::exec_function(&func, args, env, functions, classes, enums, impl_methods, None);
}
```

`exec_function` returns only `Value`. Any field mutations to the local `self` copy
inside the callee are discarded because `self` was passed by value (cloned into the
callee's `local_env`). The caller's `self` variable in `env` is never updated.

### Path 2 — UFCS dot-dispatch: `self.moduleloader_unload(path)`

File: `src/compiler_rust/compiler/src/interpreter_method/mod.rs` line ~1105

```rust
// UFCS Fallback: Try to find a free function with the method name
if let Some(func) = functions.get(method).cloned() {
    let result = exec_function_with_values(&func, &arg_values, env, functions, classes, enums, impl_methods)?;
    return Ok((result, None)); // UFCS calls don't mutate self  <-- BUG HERE
}
```

`find_and_exec_method_with_self` does not find `moduleloader_unload` because it is
not registered in `class_def.methods` or `impl_methods["Loader"]` — it is a
top-level free function. Control falls to the UFCS fallback, which explicitly
returns `None` for the updated-self slot, even though `func.is_me_method == true`.

The caller (`eval_call_expr` in `calls.rs` line 55) receives `None` and skips the
writeback: `if let Some(new_self) = updated_self { ... }`.

### Why `is_me_method` is `true` for free functions

The parser (`src/compiler_rust/parser/src/parser_impl/functions.rs` line 69)
sets `is_me_method = true` whenever the `me` keyword leads the function declaration,
regardless of whether it is inside an `impl` block or at the top level. So
`me fn moduleloader_unload(self: Loader, ...)` already has `is_me_method = true`
in the `FunctionDef`. The information needed to gate writeback is available at
both call sites.

### Why in-place dict mutation (`me load`) is unaffected

`self.modules[path] = m` mutates the dict value in place via `Arc` interior
mutation. The dict object is shared by reference between the caller's `self`
and the callee's local `self` copy (both hold `Arc::clone` of `fields`). No
field reassignment occurs, so no writeback is needed. `moduleloader_unload`
replaces the field pointer with a new dict (`self.modules = self.modules.without(path)`),
which only changes the local copy's pointer — the caller's copy still holds the
old pointer.

---

## Fix Sketch

Two surgical changes are required, one per path.

### Change 1 — Path 1: free-function call site

**File:** `src/compiler_rust/compiler/src/interpreter_call/mod.rs`

At priority 4, after calling `exec_function`, check whether the callee is
`is_me_method=true` and whether the first evaluated argument is an Object.
If both are true, write the callee's final `self` value back to the caller's env
variable.

The mechanism already exists: `exec_function_with_self_return` in
`interpreter_method/special/execution.rs` runs the function, extracts `local_env["self"]`
after the call, and returns `(Value, Value)`. A new variant that works from
positional args (not pre-bound `class`/`fields`) is needed, or the priority-4
block can be extended to:

1. Check `func.is_me_method`.
2. If true and first argument evaluates to `Value::Object { class, fields }`,
   call `exec_function_with_self_return` (passing class + fields) instead of
   `exec_function`.
3. Identify which variable name the first arg resolves to (`Argument.value` is
   `Expr::Identifier(var_name)` in the common case; also handle
   `Expr::FieldAccess` for `self.field`).
4. Write `updated_self` back to `env[var_name]` (and to `MODULE_GLOBALS` if
   present, mirroring the pattern already used for `MethodCall` at calls.rs:56-63).

Edge case: if the first arg is not an `Identifier` or `FieldAccess` (e.g., a
literal struct expression), there is no L-value to write back to — silently skip
writeback. This is consistent with how `MethodCall` handles non-identifier receivers.

**Estimated LOC:** ~30-40 lines added/modified in `mod.rs`, plus a thin helper.

### Change 2 — Path 2: UFCS fallback in `evaluate_method_call_with_self_update`

**File:** `src/compiler_rust/compiler/src/interpreter_method/mod.rs`

At the UFCS fallback block (line ~1105), check `func.is_me_method`. If true,
call `exec_function_with_self_return` with the receiver object and return
`(result, Some(updated_self))` instead of `(result, None)`.

```rust
// UFCS Fallback: Try to find a free function with the method name
if let Some(func) = functions.get(method).cloned() {
    let mut arg_values = vec![recv_val.clone()];
    for arg in args {
        arg_values.push(evaluate_expr(&arg.value, env, ...)?);
    }
    if func.is_me_method {
        // Use self-returning variant so field reassignments propagate back
        let (result, updated_self) = exec_function_with_self_return_from_values(
            &func, &arg_values, env, functions, classes, enums, impl_methods,
            &class, &fields,
        )?;
        return Ok((result, Some(updated_self)));
    }
    let result = exec_function_with_values(&func, &arg_values, env, ...)?;
    return Ok((result, None));
}
```

The comment `// UFCS calls don't mutate self` becomes incorrect for `me` free
functions — it should only apply to regular `fn` functions. Remove or qualify it.

**Estimated LOC:** ~15-20 lines in `mod.rs`.

### Semantic rule being implemented

> When a `me` free function is called and its first parameter is an Object
> (regardless of whether the call is explicit `f(self, ...)` or UFCS
> `self.f(...)`), the caller must write the callee's final `self` value back to
> the L-value the first argument resolved from, provided that L-value is an
> `Identifier` or `FieldAccess` expression.

This is exactly symmetric with what `MethodCall` + `evaluate_method_call_with_self_update`
already does for registered impl methods.

---

## Risk Assessment

**Blast radius — `me` free functions in the codebase:**
All `me fn` top-level functions currently work correctly for in-place mutations
(dict insert/index assign) because those don't need writeback. The fix adds
writeback only when `func.is_me_method == true`. Any existing caller passing an
Object first-arg will now have its variable silently updated after the call.
This is the intended semantic. No caller is expected to rely on the absence of
writeback — that would be a latent bug.

Grep estimate: there are relatively few `me fn` free functions in the codebase
(loader area has `moduleloader_load`, `moduleloader_unload`, `moduleloader_reload`).
Before submitting the fix, the implementer should run:

```bash
grep -rn '^me fn\|^me fn ' src/ --include='*.spl' | wc -l
```

to size the blast radius. If there are many, run the full test suite before
and after to detect regressions.

**Other tests that might break:**
- Any spec that calls a `me` free function whose first arg is an Object and
  currently (accidentally) relies on no writeback. Probability: low.
- The existing `moduleloader_load` delegation tests should remain green — no
  writeback is harmful for in-place mutation; the write-back just redundantly
  updates the env with the same Arc-sharing Object value.

**Does NOT touch:**
- `codegen/instr/` (owned by parallel C1+C2 agent)
- `hir/lower/expr/` (owned by parallel D agent)
- `hir/lower/tests/`
- Any `.spl` source file

---

## Test Impact

**Expected outcome once fix lands:**

The 6 failing it-blocks in `test/unit/compiler/loader/module_loader_spec.spl`
(lines 353-534, Phase 4 A1 additions) should turn green:

```
✓ impl-method unload clears modules entry for the path
✓ impl-method unload drops global symbols owned by that module
✓ impl-method unload clears loaded_metadata for the path
✓ impl-method unload clears jit_cache entries for symbols of the module
✓ impl-method double-unload is idempotent: second call is a no-op
✓ impl-method unload and free-function unload produce identical module-table state
```

All 22 it-blocks were passing before the A1 delegation attempt with the original
38-line body, confirming the test assertions are correct. The fix restores the
semantics the tests assert.

**Qualifier:** "expected", not confirmed — tests were not re-run in this
investigation pass.

---

## Estimated Effort

**Medium.** Core changes are ~50-60 LOC across two Rust files. The logic pattern
already exists (`exec_function_with_self_return`, the writeback idiom in
`calls.rs`) — this is adaptation, not invention.

A helper function `exec_function_with_self_return_from_values` may be needed if
`exec_function_with_self_return` only accepts `&[Argument]` (not pre-evaluated
`&[Value]`). Check the existing signature before writing. If it already accepts
values, the LOC count drops.

No bootstrap rebuild is required — the fix is in the Rust seed interpreter, not
in a new `rt_*` extern.

**Pure-Simple parity:** The pure-Simple compiler (`src/compiler/`) has its own
`is_method` machinery (seen in `20.hir/hir_definitions.spl`). The tests run
against the Rust seed interpreter, so the Rust fix is sufficient for the 6
it-blocks to go green. Pure-Simple compiler parity (for compiled mode) should be
tracked as a follow-up, not bundled.

---

## Sequencing

1. **This fix** lands in its own commit, with a focused test run verifying:
   - All 22 module_loader_spec it-blocks pass.
   - No regression across the broader interpreter test suite.

2. **A1 dedup** (collapsing the 38-line `me unload` body into a one-line
   delegator) lands in a separate subsequent commit, after the fix is confirmed
   green.

Do NOT bundle. The fix is a semantics correction; the dedup is a code quality
change. Mixing them complicates bisect and review.

---

## Files To Modify (Rust seed only)

| File | Change |
|------|--------|
| `src/compiler_rust/compiler/src/interpreter_call/mod.rs` | Priority 4 block: detect `is_me_method` + first-arg Object, call self-returning exec variant, write back to env |
| `src/compiler_rust/compiler/src/interpreter_method/mod.rs` | UFCS fallback (~line 1105): if `func.is_me_method`, return `Some(updated_self)` instead of `None` |
| `src/compiler_rust/compiler/src/interpreter_method/special/execution.rs` | (possibly) add `exec_function_with_self_return_from_values` taking `&[Value]` if not already present |

---

## Key Reference Locations

- Parser sets `is_me_method`: `src/compiler_rust/parser/src/parser_impl/functions.rs:69`
- `FunctionDef.is_me_method` field: `src/compiler_rust/parser/src/ast/nodes/definitions.rs:48`
- Self-returning execution helper: `src/compiler_rust/compiler/src/interpreter_method/special/execution.rs:78` (`exec_function_with_self_return`)
- Free-fn call site (Path 1): `src/compiler_rust/compiler/src/interpreter_call/mod.rs:99`
- UFCS fallback (Path 2): `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1105`
- Writeback pattern to mirror: `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:55-63`

# BUG: Codegen method-dispatch self-recursion

Status: RESOLVED (2026-05-19; verified 2026-05-29)

**Date:** 2026-05-18
**Severity:** High (silent stack overflow at runtime)
**Status:** RESOLVED (2026-05-19; verified 2026-05-29)

## Summary

When a module-level function `fn foo(s: text, ...) -> T` calls `s.foo(...)` (a
method with the same name as the function), Cranelift codegen resolves the method
call back to the enclosing function, causing infinite recursion and stack overflow.

## Reproduction

```spl
fn str_ends_with(s: text, suffix: text) -> bool:
    s.ends_with(suffix)   # resolves to str_ends_with(s, suffix) -> infinite loop
```

GDB backtrace shows 1500+ frames of `frontend.core.types.str_ends_with` calling
itself.

## Affected functions

Any free function whose name **exactly matches** a method name and calls
`s.<method>(...)` where `s` is `text`:
- `str_ends_with` -> `s.ends_with()` — UFCS finds `ends_with` in `src/lib/text.spl`
- `str_starts_with` -> `s.starts_with()` — similar
- `str_contains` -> `s.contains()` — similar
- `str_index_of` -> `s.index_of()` — similar
- `str_trim` -> `s.trim()` — similar
- `str_replace` -> `s.replace()` — similar
- `ends_with` (in `src/lib/text.spl`) -> `s.ends_with()` — resolves to itself directly

Also affects `last_index_of` in `src/lib/text.spl` (no runtime extern available).

## Root cause (corrected)

The bug is **not** in Cranelift codegen. It is in the UFCS method resolver at:

**`src/compiler/35.semantics/resolve_strategies.spl`, `try_ufcs` method (line 229)**

The UFCS resolution logic:
1. Calls `self.symbols.lookup_function(method)` — exact name lookup, not suffix match
2. Checks that the found function's first parameter type is compatible with the receiver
3. Returns `MethodResolution.FreeFunction(func_sym_id)` if compatible

It never checks whether the matched function is the **same as the currently-resolving
function**. So `fn ends_with(s: text, suffix: text)` calling `s.ends_with(suffix)`
looks up `"ends_with"`, finds itself (exact match, first param `text` matches), and
produces `FreeFunction(ends_with_id)` — causing self-recursion at runtime.

The Cranelift codegen and interpreter correctly dispatch to whatever `func_id` the
resolver provides. The bug-doc's original "name suffix matches" framing was incorrect;
`lookup_function` does exact-name match, not suffix match.

**Fix site:** `src/compiler/35.semantics/resolve_strategies.spl::try_ufcs`

**Required change:**
1. Add `current_fn_sym: SymbolId?` field to `MethodResolver` struct (`resolve.spl`)
2. Set it before resolving each function's body in `resolve_function`
3. In `try_ufcs`, before returning `FreeFunction`, guard:
   ```spl
   if self.current_fn_sym.? and func_sym_id.unwrap() == self.current_fn_sym.unwrap():
       return nil  # skip self — fall through to error or Unresolved
   ```

This is out of scope for the `70.backend` / `src/compiler_rust/compiler/src/codegen/`
fix wave. The workaround (direct `rt_string_*` extern calls) remains correct.

## Workaround applied

Replaced method calls with direct `rt_string_*` extern calls in:
- `src/compiler/10.frontend/core/types.spl` (6 functions)
- `src/lib/text.spl` (1 function)

## Fix applied (2026-05-19)

**`src/compiler/35.semantics/resolve.spl`**
- Added `current_fn_sym: SymbolId?` field to `MethodResolver` class (nil by default)
- All three construction paths (`new`, `with_trait_solver`, `create_method_resolver`) initialise it to `nil`
- `resolve_function` sets `self.current_fn_sym = Some(func.symbol)` before resolving the body; the field is `nil` during constant resolution, preventing stale comparisons

**`src/compiler/35.semantics/resolve_strategies.spl`**
- In `try_ufcs`, after type-compatibility check passes, added guard:
  ```spl
  val resolved_id = func_sym_id.unwrap()
  if (self.current_fn_sym.? and
      self.current_fn_sym.unwrap().id == resolved_id.id):
      return nil
  ```
  This causes a same-named free function to fall through to `Unresolved` instead of resolving to itself, breaking the self-recursion cycle.

The Cranelift codegen's `else` branch (calls.rs line 2686) already has a builtin
remap table (`"ends_with" => Some("rt_string_ends_with")`) that would catch
dotted-form calls, but by the time MIR reaches codegen the call name is already the
free-function name (e.g., `"ends_with"`), not a dotted form — so the remap table
is never reached for this bug. Fixing codegen alone is insufficient.

Relevant files:
- `src/compiler/35.semantics/resolve_strategies.spl` — fix site
- `src/compiler/35.semantics/resolve.spl` — `MethodResolver` struct definition
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs` — downstream (no fix needed)

## Verification (2026-05-29)

Fix code confirmed present in source:
- `current_fn_sym: SymbolId?` field in `MethodResolver` at `resolve.spl:118`
- All three construction paths initialise to `nil` (lines 127, 138, 162)
- `resolve_function` sets `Some(func.symbol)` at line 240
- Self-recursion guard in `try_ufcs` at `resolve_strategies.spl:258-260`

Fix committed in: `4c9e74d8dc` "feat: Wave 15 — UFCS self-recursion fix" (2026-05-19)

Reproduction test run (interpreter mode, live `.spl` resolver execution):

```spl
fn ends_with(s: text, suffix: text) -> bool:
    s.ends_with(suffix)

fn starts_with(s: text, prefix: text) -> bool:
    s.starts_with(prefix)

fn main():
    val r1 = ends_with("hello world", "world")   # must be true
    val r2 = ends_with("hello world", "xyz")      # must be false
    val r3 = starts_with("hello world", "hello")  # must be true
    val r4 = starts_with("hello world", "xyz")    # must be false
```

Command: `bin/simple run /tmp/ufcs_repro3.spl`

Output:
```
ends_with true-case: PASS
ends_with false-case: PASS
starts_with true-case: PASS
starts_with false-case: PASS
```

No stack overflow. Both true and false cases resolve correctly — confirms the guard
causes self-named calls to fall through to the `rt_string_*` builtin rather than
looping. Workaround in `types.spl` and `text.spl` remains in place (safe, no need
to remove).

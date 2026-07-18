# Bug: HIR Lowering Ignores Nested fn Declarations — "Unknown variable: decorator while lowering skip"

**ID:** hir_nested_fn_not_lowered_as_variable
**Severity:** P2 (blocks JIT for all spec files importing std.spec.decorators)
**Date:** 2026-06-13
**Status:** WORKAROUND APPLIED (pure-Simple fix in decorators.spl)

## Symptom

Every `bin/simple run <spec>.spl` logs:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown variable: decorator while lowering skip
```

(Also seen: `Unknown type: TargetOptContext`, `Unknown type: Lexer` — separate instances of the same underlying pattern.)

Spec files never JIT-compile; they always fall back to the interpreter.

## Root Cause (AC-1)

**File:** `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`, line 606–609

```rust
Node::Function(_f) => {
    // Nested function definitions are ignored in native lowering for now.
    Ok(vec![])
}
```

When a nested named `fn` is declared inside a function body, the Rust HIR lowering **silently emits no HIR statements** for it. The function name is never added to the local scope. When the enclosing function then references that name as a variable (e.g., `decorator` at the end of `skip()`), the HIR lowering fails with `Unknown variable: decorator while lowering skip`.

The pattern in `src/lib/nogc_sync_mut/spec/decorators.spl` was:

```simple
fn skip(...) -> fn(text, fn()):
    val condition = create_skip_condition(...)
    fn decorator(name: text, block: fn()):   # <-- IGNORED by HIR lowering
        ...
    decorator   # <-- Unknown variable: "decorator" not in scope
```

The error format `{name} while lowering {func_name}` comes from `hir/lower/expr/mod.rs` line 315.

## Fix Applied (Pure Simple — AC-2)

**File:** `src/lib/nogc_sync_mut/spec/decorators.spl`

Changed all 4 nested `fn decorator(...)` declarations to `val` bindings:

```simple
# Before (HIR fails — fn ignored, decorator is unknown variable):
fn decorator(name: text, block: fn()):
    ...
decorator

# After (HIR succeeds — val creates a local binding with Lambda RHS):
val decorator = fn(name: text, block: fn()):
    ...
decorator
```

`val x = fn(...)` is parsed as a `Node::Let` with a Lambda expression on the RHS, which the HIR lowering handles correctly via `stmt_lowering.rs` line 63 (`Node::Let`). The Lambda expression itself is lowered by the expression lowerer, which does support anonymous functions.

**Functions fixed:** `skip()`, `ignore()`, `only_on()`, `skip_if()` — all 4 in decorators.spl.

## Formatter Note

The Simple formatter (`src/compiler/90.tools/formatter/main.spl` via `compiler.tools.formatter.main`) may normalize `val f = fn(params):` back to `fn f(params):` in some contexts. If this workaround is reverted by a future formatter run, the formatter rule needs to be updated to preserve `val = fn` bindings inside function bodies.

## Remaining Rust Seed Bug (Open)

The underlying Rust seed bug — `Node::Function` inside a function body being silently ignored rather than registered as a local variable — remains unfixed. A proper fix requires the HIR lowering to:

1. Register the nested `fn` name as a local variable binding
2. Lower the function body as a Lambda/closure value
3. Bind it to the local index

**Affected file in seed:** `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` line 606–609

**Do NOT patch the Rust seed** (per project policy: fix .spl not Rust).

## Other Unknown Type Errors (Separate Issues)

- `Unknown type: TargetOptContext` in `riscv64_cross_module_abi_spec.spl` — separate HIR issue, different type
- `Unknown type: Lexer` — occurs in specs that import JS/HTML parser modules with `Lexer` types that the HIR type resolver can't find

These are separate bugs; the `decorator` fix does not address them.

## Verification

After fix, the following specs show no `decorator` JIT fallback and pass:
- `test/01_unit/lib/http_server/parser_limits_spec.spl` — 4+7+4+2+2 examples, 0 failures
- `test/01_unit/lib/http_server/path_safety_spec.spl` — 5+4+2+2+2 examples, 0 failures
- `test/01_unit/os/fs_exec_fallback_contract_spec.spl` — 9+3+3+3+3 examples, 0 failures
- `test/01_unit/compiler/codegen/riscv64_cross_module_abi_spec.spl` — 15 examples, 0 failures (decorator fallback gone; TargetOptContext fallback is pre-existing separate bug)

`bin/simple check src/lib/nogc_sync_mut/spec/decorators.spl` — OK

## Timing (AC-3)

Medians over 3 runs (wall clock):

| Spec | Before (ms) | After (ms) | Delta |
|------|-------------|------------|-------|
| parser_limits_spec | 225 | 224 | ~0 |
| path_safety_spec | 187 | 172 | -15ms |
| fs_exec_fallback_contract_spec | 192 | 179 | -13ms |

The specs still run in interpreter mode (JIT fallback to interpreter was the old path; now they JIT partially but still interpreter-execute the test bodies due to other HIR limitations). The ~10-15ms improvement comes from eliminating the failed JIT attempt overhead on the decorator module. JIT does not make these specs faster in practice since test execution is I/O-bound, not compute-bound.

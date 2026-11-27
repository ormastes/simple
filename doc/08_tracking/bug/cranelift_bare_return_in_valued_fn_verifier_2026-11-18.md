# Bare `return` in a value-returning function fails the Cranelift verifier

- id: `cranelift_bare_return_in_valued_fn_verifier_2026-11-18`
- status: compiler fix landed (seed-spec verified, NOT yet verified on a rebuilt Stage 2); source workaround landed and verified natively
- found: Phase 3 bootstrap, Stage 2 `integ9` compiling the Stage 3 closure with `--backend cranelift`

## Symptom

```
cranelift: AOT define_function error: Verifier errors:
- inst8170 (return): arguments of return must match function signature
unit: compiler.hir.hir_lowering._Items.module_import_registration
Failed to compile function: ...HirLowering.register_imported_symbol_inner
```

One module of 114 in MIR shard claim 0 failed, sealing the whole shard.

## Minimal shape

`test/fixtures/bare_return_in_valued_fn/main.spl`:

```simple
fn pick(name: text, other: text) -> text:
    var selected = "none"
    if name == other: return        # bare return, declared `-> text`
    selected = "picked"
    selected
```

Per lane, before the fix:

| lane | result |
|---|---|
| Stage 2 cranelift | build rc=1, `inst44 (return): arguments of return must match function signature` |
| Stage 2 llvm | build rc=0, runs; the bare return yields a fabricated `ret i64 0` (silent wrong value) |
| seed interpreter | runtime `nil is forbidden by the non-optional return contract of 'pick'` |

The same verifier error hits `-> T?` functions (`fn num(n: i64) -> i64?:` with
`if n == 0: return`), where the seed returns nil.

The real site was `register_imported_symbol_inner(...) -> text` at
`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl`
(`if local_name == qualified_local: return`).

## Root cause

`lower_return_expr` (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`),
bare-return branch: `br_void.terminate_return(None)` was emitted
unconditionally, with no check of the function's MIR signature. The backend
then saw `Ret(None)` against a signature with one result. The implicit-tail
path (`function_lowering.spl`, E-SFFI-016 "missing return in non-unit
function") already refused this; the explicit bare `return` did not.

## Fix

In `lower_return_expr`, a bare `return` in a function whose MIR signature is
not Unit (and that is not `main`):

- declared `-> T?`: lowered as `return nil` (a typed `NilLit` through the
  normal value path, so the Ret carries the canonical Option handle);
- any other declared value type: fatal `E-SFFI-016: bare `return` in non-unit
  function '<name>'` -- a per-module MIR lowering error raised before codegen
  instead of a backend verifier ICE or an LLVM zero.

Spec: `test/01_unit/compiler/50.mir/bare_return_in_valued_fn_spec.spl`
(red 2/3 before, green 4/4 after, seed interpreter).

## Workaround

`module_import_registration.spl` now returns `selected_category` at that site
(tagged `@workaround bug=cranelift_bare_return_in_valued_fn_verifier_2026-11-18`).
The path was unreachable-without-error on the seed (nil return contract), so no
working behaviour changes.

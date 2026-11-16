# Phase 2 LLVM: field read on an untyped match-bound local becomes a `void` call operand

- **ID:** phase2_llvm_untyped_match_local_field_void_2026-11-16 - status open (not reproduced on current source).
- **Seen with:** frozen "Phase 2" compiler (pin 18a1f28937c2) compiling the compiler with the LLVM backend.

## Symptom
`src/compiler/70.backend/backend_plugin/dynamic_loader.spl`, `load_dynamic_backend_plugin_lease`:

```
var library = match loaded:           # loaded: Result<DynLib, text>
    case Ok(value): value
    case Err(detail):
        staged.close()
        return Err(DynamicBackendPluginLoadError.LoadFailed(detail))
...
dynlib_symbol_address_v1(library.handle, NAME)   # handle: i64 field of class DynLib
```

emitted `call i64 @...dynlib_symbol_address_v1(void %l72, ptr %l73)`; llc: "void type only
allowed for function results". The `library.handle` GetField result carried a Unit MIR type.

## Analysis of current source (origin/release/1.0.0 11c73d067d8)
- The if/match merge lowering already excludes diverging arms and retypes the result slot
  from the live arms (`lower_if`, `mir_lowering_stmts.spl` ~4323; enum match merge,
  `_MirLoweringExpr/switch_operators_calls.spl` ~5700-5800; existing specs
  `if_divergence_merge_spec.spl`, `enum_match_divergence_spec.spl`).
- The GetField result type is `declared owner-struct field type`, else the HIR field
  expression's `type_` (`_MirLoweringExpr/expr_dispatch.spl` ~7970-7990, `Field` arm). If the
  base local's struct owner is not resolvable (match-bound local, no annotation) the
  fallback is `lower_type(expr.type_)`, i.e. whatever HIR assigned the field expression.
  Not reproduced: the seed cannot parse current compiler sources
  (`driver_compile_options.spl:63`, multi-line array literal after a match), so MIR specs
  cannot be executed on it, and no current pure-Simple binary was available.
- Backend defect, fixed by this change: the LLVM call emitter (`core_codegen.spl`, call
  argument loop) printed `void %lN` for a Unit-typed operand. It now records a
  `codegen_error` naming module, function, callee and argument index (fail-closed, no IR).

## To close
Re-run the Phase 2 LLVM compile of `dynamic_loader.spl` with a compiler built from current
source; if the new diagnostic fires, the named function/argument identifies the local whose
Unit type must be traced back through the match/field HIR typing.

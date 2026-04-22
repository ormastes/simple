# Compiler Module-Scoped HIR Lowering - System Test Plan

## Request

Cover `FR-COMPILER-004`: lowering one module must not leave same-named type symbols in scope for a later module.

## Test

`test/system/compiler_module_scoped_hir_lowering_spec.spl`

## Assertions

- Module `a` can define `CompileOptions`.
- A later consumer with `use b.{CompileOptions}` resolves `CompileOptions` to module `b`.
- The prior lowering of module `a` does not shadow the later explicit import.

## Verification Command

`bin/simple test test/system/compiler_module_scoped_hir_lowering_spec.spl`

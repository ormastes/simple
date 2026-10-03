# Curated Loader Runtime Export Origins

Source: `test/01_unit/compiler/loader/runtime_export_origins_spec.spl`

## Scenarios

1. Compiler and JIT types route to their physical defining modules.
2. Sweeper and resource types route to their physical defining modules.
3. Module loader and mapper types route to their physical defining modules.

The spec pins the source owner contract for ten invalid export origins seen in
the CLI HIR log. Full source-bound LLVM and Cranelift CLI builds remain the
runtime acceptance gate; this source contract does not claim those builds pass.

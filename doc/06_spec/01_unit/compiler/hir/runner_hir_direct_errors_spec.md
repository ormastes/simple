# Runner Closure Direct HIR Error Specification

Source: `test/01_unit/compiler/hir/runner_hir_direct_errors_spec.spl`

## Scenarios

1. The frozen surface alignment helper is imported from its package owner.
2. MIR lowering uses the already imported optional environment facade.
3. Finally transfer emission declares its unit return.
4. Seven async array helpers declare their actual result types.

This is a production source contract for the grouped HIR failures. A full
source-bound Stage2 runner build remains necessary to prove closure admission;
this spec does not claim that build has passed.

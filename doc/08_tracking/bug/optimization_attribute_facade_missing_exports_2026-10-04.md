# Optimization types missing from the attributes facade

Status: facade repair validated through HIR; native execution blocked by downstream MIR errors.

The provisional Phase 3 manager authority build reaches 205 source modules, then HIR lowering rejects three imports in `compiler.hir.generated.hir_codec`: `OptimizationReq`, `OptimizationReqLevel`, and `OptimizationBackend`. The generated codec and `compiler.hir.portable_body_semantics` import them from `compiler.common.attributes`, but the facade's explicit export list omits them even though `_Attributes.decl_attrs` defines all three.

Export the existing types through the facade used by its callers. Do not edit the generated codec or add duplicate type definitions. The native fixture imports all three through the facade, constructs a requirement, and checks both enum fields. Evidence: `C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/pr2385-validation-managed-parallel-os/provisional-v1/authority-images/logs/provisional-authority.attempt1.stderr.log`.

Validation: the pure LLVM-produced compiler parsed and lowered all 53 modules
in the fixture closure successfully (53 HIR succeeded, 0 failed), including
this facade and the importing fixture. Monomorphization also completed.
Native generation then failed in existing dependency bodies: ambiguous bare
`Assign` in the attributes helper, unresolved `VariantKind`/`TypeKind` uses,
and unresolved SymbolTable methods. No executable or runtime PASS is claimed.
The complete diagnostic is retained in
`windows-restart-20261004/attribute-facade-validation/single-build.log`.
The separate 40-job coordinated run remains independent evidence and was not
stopped or counted as a success. This repair changes only the facade exports;
it does not modify those downstream MIR failures.

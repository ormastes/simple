# MIR transforms erased enum declaration provenance

Status: fix implemented; native constructor regression passed; full imported
pass integration remains unrun. Severity: P1 (semantic metadata lost before
serialization/fingerprinting and downstream consumers).

Eight function-transform owners rebuilt `MirModule` without its existing
`enum_semantic_declarations` field. The constructor default silently replaced
retained declarations with an empty array. These passes do not own enum
redefinition. Preserve the original field exactly, as XRay policy already does.

Affected sources:
- `src/compiler/80.driver/driver_pipeline_aop.spl`
- `src/compiler/50.mir/mir_debug_trace_injection.spl`
- `src/compiler/60.mir_opt/mir_opt/_AutoVectorize/recipe.spl`
- `src/compiler/60.mir_opt/mir_opt/_AutoVectorize/rewrite.spl`
- `src/compiler/60.mir_opt/mir_opt/_Inline/driver.spl`
- `src/compiler/60.mir_opt/mir_opt/simd_lowering.spl`
- `src/compiler/60.mir_opt/mir_opt/storage_projection_lowering.spl`
- `src/compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl`

Validation: admitted pure-Simple producer SHA
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`
compiled 183 actual production MIR type records and the eight exact constructor
expressions with `--runtime-bundle core-c`. Native execution passed 24 checks:
each expression retains owner/source/runtime/variant fields, preserves the
empty default, and its old omitted-field counterpart reproduces metadata loss.
Compile/run exited zero. `/tmp/aop-enum-native-20261114/` retains extraction,
source hashes and logs. This proves construction behavior, not complete passes.

The actual AOP/debug/SIMD/vectorization integration regression is
`test/02_integration/compiler/mir_transform_enum_provenance_spec.spl` (UNRUN).
No full compiler/lib/MCP smoke or phase3 qualification is claimed. The separate
new initializer metadata field remains its feature owner's integration work.

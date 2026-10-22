# Stale composite field reference blocks Linux Phase2

Status: source repair authored and independently reviewed; native qualification pending.

Frozen source `34dcb8896912f1441c6b8300d65e73ce3dc7585b` completed native inventory with 1292 modules compiled and one failure in `src/compiler/50.mir/_MirLowering/module_lowering.spl`. The diagnostic was `cannot infer field type while lowering MirLowering.register_composite_field_metadata_types_v1: struct 'ANY' field 'type_'`. The canonical run took 2355.795 seconds, peaked at 1258024 KiB RSS, and exited 1 with terminal quiescence. This was not a memory-limit failure.

The refactored wrapper projects each `HirField.type_` into `declaration_types`. The receiving helper checks parallel array lengths and binds `field_type: HirType = declaration_types[fi]`. Its Function branch still referenced `field.type_`, although `field` exists only in the preceding wrapper. Pass the current typed `field_type` to `function_signature_ownership_proof`, retaining the complete function signature and canonical ownership calculation. No inference relaxation or replacement ownership model is needed.

Independent inspection found no other executable stale `field` references in the helper. Existing `native_function_field_signature_owner` and `native_array_return_function_field_owner` fixtures cover provider/consumer owner collisions and function-valued fields; their execution with the repaired compiler remains pending. Do not count source review as those native tests passing.

Failed evidence and successful object cache are retained under `/root/simple-block-repair-canonical-reserved-20261012`. The initial three repair cycles stopped and were reported. Any continuation must preserve that failed evidence and use supported cache validity checks, without relabeling prior results as qualification of this source.

# match_array_literal_patterns_multiple_wildcard_arms

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: B5b: match has multiple wildcard arms (arm 1 in SpirvBuilder.create): array-literal patterns case [1, 0] are lowered as wildcards.

Workaround (tagged `@workaround bug=match_array_literal_patterns_multiple_wildcard_arms_2026-10-24`): explicit if/elif on vk_version[0]/[1], list values (src/plugins/backend_vulkan/vulkan/spirv_builder.spl).

Root fix location: src/compiler/50.mir/_MirLowering/module_lowering.spl and _MirLoweringExpr/expr_dispatch.spl: lower array-literal patterns to length and element tests. Source also mixed tuple and list arm values for an [i64] field.

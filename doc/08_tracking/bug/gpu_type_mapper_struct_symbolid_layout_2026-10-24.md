# GPU type mappers lost struct layout when MirTypeKind.Struct became SymbolId

**Status:** open

- Symptom: after d4a71cd66df, `VulkanTypeMapper`/`CudaTypeMapper` `size_of`/`align_of` return 8 for every `Struct(_)`; Vulkan std430 struct layout and CUDA by-value struct size were dropped.
- Root cause: `MirTypeKind.Struct(symbol: SymbolId)` carries no fields (mir_types.spl:191); fields live in `MirModule.types: Dict<SymbolId, MirTypeDef>` (`MirTypeDefKind.Struct([MirFieldDef])`). The mappers had no access to that table.
- Fix: both mappers hold `type_defs` (default `{}`), set via `with_type_defs(module.types)`; `CudaBackend` calls it where it already loads `self.type_defs`. Old algorithms restored: Vulkan = std430 aligned offset walk (no tail round-up, as before), max-field alignment; CUDA = sum of field sizes, max-field alignment.
- Residual workaround (tagged `@workaround bug=gpu_type_mapper_struct_symbolid_layout_2026-10-24`): a symbol absent from the table, or non-struct typedef, still yields 8. The Vulkan backends (`compiler/70.backend/backend/vulkan_backend.spl`, `plugins/backend_vulkan/vulkan_backend.spl`) do not yet pass the table (their `compile` is not `me`); callers needing layout must use `with_type_defs`.
- Spec (unexecuted): test/01_unit/plugins/gpu_type_mapper/struct_symbolid_layout_spec.spl

## 2026-11-05 (work/mirp2-D) — rescoped
- Mapper fix is on origin/release/1.0.0 (`with_type_defs` in cuda/vulkan mappers; `cuda_backend.spl:150` passes `module.types`).
- Spec `test/01_unit/plugins/gpu_type_mapper/struct_symbolid_layout_spec.spl` now EXECUTED: 3/3 green (interpreter, `bin/simple.exe run`).
- Remaining open scope only: the two Vulkan backends still do not call `with_type_defs` (their `compile` is not `me`). Next step: make `compile` `me` (or thread `module.types` into a local mapper) and add a Vulkan std430 struct-size spec.

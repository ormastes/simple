# Storage Layout Feature Expert

## Authoritative sources

- `src/lib/common/structural/storage_layout/`
- `src/compiler/60.mir_opt/mir_opt/storage_access_analysis.spl`
- `src/compiler/60.mir_opt/mir_opt/storage_projection_lowering.spl`
- `src/compiler/70.backend/backend/native/isel_x86_64.spl`
- `doc/03_plan/language/parallel_memory_mdsoc_plus_parallel_agents_2026-08-12.md`

## Landed

- Frozen `StorageLayoutPlanV1` and overflow-safe AoS/SoA/AoSoA projector.
- Bounded fixed-record conversion oracle with exact round trips.
- Compiler-owned revisioned typed-view binding and affine AoS/SoA recipe.
- Custom x86 native lowering for `mir.storage.project_address.v1`.
- Exact function/base-local rewrite from `mir.storage.project_field.v1`.
- Module-qualified `CompileContext` registry, MIR-coupled eviction, late atomic
  rewrite, and complete sorted binding identity in native cache scope.

## Still proposed or incomplete

- Automatic typed `T[]` allocation and view binding.
- Complete logical field load/store rewriting and other host backends.
- Grouped, tiled, packed, and factored physical mappings.
- Address-observation inference, PGO/cost inputs, view cache, and production pilots.

## Operational rules

1. Reuse `StorageLayoutPlanV1`; never create a backend-local layout enum.
2. Treat ordinary RuntimeValue arrays as legacy storage until explicitly bound.
3. Reject ABI-pinned/address-observed records and unknown schemas before lowering.
4. Never derive `noalias` from layout or incomplete WP-20 access facts.
5. Compare logical results against an independent oracle, not round trip alone.
6. Never let unresolved logical projection intrinsics reach a backend; unknown
   native intrinsics may otherwise degrade to NOP.
7. Require index-bound evidence and validate the maximum affine byte address
   against the bound allocation capacity.
8. Freeze registration before parallel codegen; never mutate bindings in a
   worker or store them in `MirModule`.
9. Admit only x86_64 custom-native 8-byte fields until other backend/width
   owners land; every unsupported route is an error.

The W^X store/load parity scenario requires a fresh runtime containing
`rt_ptr_read_u8`; a stale runner or unresolved-symbol stub is not evidence.

## Focused evidence

```text
bin/simple test test/01_unit/common/structural/storage_layout_contract_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/backend/native/storage_layout_native_projection_spec.spl --mode=interpreter
```

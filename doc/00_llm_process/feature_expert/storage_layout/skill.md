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

## Focused evidence

```text
bin/simple test test/01_unit/common/structural/storage_layout_contract_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/backend/native/storage_layout_native_projection_spec.spl --mode=interpreter
```

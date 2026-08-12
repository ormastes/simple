# Storage Layout Feature Expert

## Authoritative sources

- `src/lib/common/structural/storage_layout/`
- `src/compiler/60.mir_opt/mir_opt/storage_access_analysis.spl`
- `src/compiler/50.mir/mir_data.spl` (`MirOwnedRawAllocationFactV1` owner)
- `src/compiler/60.mir_opt/mir_opt/storage_projection_lowering.spl`
- `src/compiler/60.mir_opt/mir_opt/typed_storage_view_declaration.spl`
- `src/compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl`
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
- Atomic full-evidence module installation and one-way registry freeze before
  cache lookup; frozen authority survives MIR eviction.
- Compiler-private typed-view declaration admission for exact raw allocation
  provenance, source revision, fixed schema/capacity, and bounds evidence.
- Canonical same-block MIR producer gated by owned-allocation marker, constant
  bounds proof, exclusive temporaries, and atomic evidence output.
- Atomic MIR owned-raw allocator operation/fact, cross-bound to declarations by
  stable allocation identity and lowered to `rt_alloc` only after admission.

## Still proposed or incomplete

- Compiler emission/driver registration of declarations and public typed `T[]`
  allocation/view binding.
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
10. A producer must start from `CompilerOwnedRaw` declaration evidence. Never
    relabel a RuntimeValue array or external/pinned allocation as typed storage.
11. Resolve PROJECT_FIELD against final site LocalIds before generic MIR
    optimization; only optimize after it becomes backend-ready PROJECT_ADDRESS.
12. Create declarations from `MirOwnedRawAllocationFactV1`; a parameter, call,
    cast, RuntimeValue array, or free-form provenance string is not ownership proof.
13. Register producer evidence only through the driver batch/install owner;
    freeze before cache lookup or parallel codegen and reject later mutation.
14. Freeze owns a deep-copied, module-qualified site/evidence registry and the
    zero-site module universe. Never consult live registration rows after the
    one-way freeze or use delimiter-concatenated configurable text as identity.
15. Until an immutable MIR+storage capsule exists, compile storage-bearing
    modules on the driver owner thread. ParallelBuilder may handle ordinary
    modules, but capturing mutable CompileContext is not storage-worker proof.

The W^X store/load parity scenario requires a fresh runtime containing
`rt_ptr_read_u8`; a stale runner or unresolved-symbol stub is not evidence.

## Focused evidence

```text
bin/simple test test/01_unit/common/structural/storage_layout_contract_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/backend/native/storage_layout_native_projection_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.spl --mode=interpreter
```

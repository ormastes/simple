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
15. The native parent creates class-handle MIR+storage capsules before the
    builder branch. Worker callbacks may receive only the frozen batch/module
    name and must not capture CompileContext or BuildCache. Recompute complete
    MIR and storage identities around codegen; bind object size/hash in the
    result receipt; publish only through the parent completion hook. This
    proves branch transport parity only.
16. Never send in-memory capsule/class pointers to process workers. True
    process concurrency requires a complete canonical MIR+storage codec and
    identity validation; the functions-only MIR JSON wrapper is insufficient.

The W^X store/load parity scenario requires a fresh runtime containing
`rt_ptr_read_u8`; a stale runner or unresolved-symbol stub is not evidence.

## Focused evidence

```text
bin/simple test test/01_unit/common/structural/storage_layout_contract_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/backend/native/storage_layout_native_projection_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.spl --mode=interpreter
```

## Data-policy envelope (2026-11-06)

`src/compiler/35.semantics/perf/resolved_data_policy.spl` binds a `StorageLayoutPlanV1` to a resolved rule choice (`aos`/`soa`/... tokens from `resolved_layout_token_v1`, or `auto`) plus the schema digest. It refuses a well-formed plan that contradicts an explicit pin. It adds no layout enum; the planner stays the authority. Rule precedence follows plan section 8.4: `data_policy_resolve_rules_v1` in `src/compiler/00.common/data/data_schema_resolver.spl`.

Data plan W0/W1 (2026-11-06, `doc/03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md`): data observations are a SEPARATE versioned record family in `src/lib/common/trace/data/data_observation_contracts.spl` (64-byte LE record; its frame header is magic 0x4453/size/tag/version, so it can never parse as a V1 event whose schema u16 is 1; tag 1 = `DataObservationV1`, tags 256..511 reserved for optional adaptive-collection records such as `CollectionSummaryV1`, frame-skipped by readers that do not know them). They never reuse a `TraceEventKindV1` ordinal and bind to a V1 session by generation and to V1 selection by `(module_instance, site_id)`. `DataMetricV1` carries `Measured|NotMeasured|Unsupported|Dropped|Overflowed`; read counts only through `data_metric_value_v1`, which errors for every non-measured state. A subdirectory is used because `src/lib/common/trace/` reaches the 10-file limit once PR5's `xray_native_map_format_v1.spl` lands. Schema and policy resolution: `src/compiler/00.common/data/` (one SPL+SDN resolver; the SDN path uses `parse_with_spans_and_issues`, so duplicate keys fail instead of last-writer-wins) and `src/compiler/35.semantics/perf/resolved_data_policy.spl`, which composes `StorageLayoutPlanV1` and `CollectionPlanDecision` under `DataPolicyKindV1`. `ResolvedCollectionPolicyV1` (`resolved_collection_policy.spl`) is the collection row: it is keyed by `CollectionOriginV1`, and its digest excludes provenance, so equal source and SDN declarations give byte-identical digests. SDN `data_policy.profiles.*.events` is refused, because runtime selection goes only through aspect params. Trap: the 2026-11-04 seed interpreter mis-matches `case N:` on a `u64` scrutinee (fixed in-tree by `e36e4e9dfa4`). Take an i64 code in decoders, or assert through the enum-to-code direction.

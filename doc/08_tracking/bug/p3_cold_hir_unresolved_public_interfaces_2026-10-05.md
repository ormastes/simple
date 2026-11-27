# Phase 3 cold HIR public interfaces remain unresolved

Status: fix-implemented-verification-pending (waiting-for: Stage 3 native rebuild verification). Pure-backend workaround STAGE3-GATED.

The frozen 916be Phase 3 streaming packet completed all 1142 HIR shards and
validation with zero errors, then exited 1 during cold receipt creation. It did
not reproduce the earlier retained-HIR access violation. The owner build log
SHA-256 is `04bb63ef886be4b32101ad1019337bdf9c52206a8c95de269edcd177a47b1677`.

All four errors were `cold-hir-abi-unresolved:unresolved-inference:0:0`:

- compiler.common.cache_contract.virtual_source_store_v1
- lib.nogc_sync_mut.src.map
- lib.nogc_sync_mut.src.hash
- compiler.backend.verify.allocator_symbol_scan

Source-proven path: `lower_hir_const_decl` recognizes primitive literal types
but uses `Infer(0,0)` for an unannotated array initializer. The allocator module
exports `FORBIDDEN_ALLOCATOR_SYMBOLS` with such an initializer. Annotating its
existing text array preserves its contents and semantics while avoiding that
fallback. This is a workaround; general constant inference remains unfixed.

The other three declarations are not yet identified. Generic/default and flat
type conversion paths are investigation candidates, not proven causes. The ABI
encoder now attaches the containing public declaration kind/name to its first
error. Valid encoded payload bytes remain unchanged; unresolved interfaces are
still rejected. No inference is changed to Any and no module is omitted.

There is no dedicated safe cold-receipt bypass found. Existing warm compatibility
markers are authority inputs, not a diagnostic bypass; manufacturing them would
misrepresent the build. No such workaround was applied.

Regression specs exercise rejection and exact constant attribution, a resolved
text-array ABI, and exclusion of private inference without changing public ABI.
These Simple specs are UNRUN pending a suitable self-hosted test producer.
The current producer can use the explicit array annotation. Improved diagnostic
messages require the coordinated compiler rebuild; do not restart live packets.

Memory/performance review: the annotation has no new runtime allocation. Error
context adds one short string only on failure and stops encoding after the first
invalid declaration. Valid encoding traversal/payload remains unchanged. Runtime
RSS and latency are unmeasured. Full closure verification and the other three
root causes remain outstanding.

## Separate generic-default contract repair

`lower_type_param` read the plain desugared `ParserTypeParam.default` using
optional presence syntax and omitted `HirTypeParam.has_default`. It now uses and
preserves the explicit presence bit and supplies an inert Unit payload when
absent. Tests distinguish a present i64 default from an absent Infer sentinel
and a subsequent absent text payload. Native execution is UNRUN. This is a
source-proven contract repair, not proof of the three remaining packet failures.
It performs no new traversal/allocation and avoids lowering absent payloads;
runtime performance and memory measurements are still pending.


## Pure-Container Alias Workaround & Shard Registration (2026-11-27)

- **Workaround site:** `src/lib/common/contracts/container/pure_backend_v1.spl:23-27` (added explicit `: text` type annotations on `PURE_CONTAINER_BACKEND_V1` and `PURE_CONTAINER_ENGINE_V1` in commit `a2fc53df77e`, tagged `# @workaround bug=p3_cold_hir_unresolved_public_interfaces_2026-10-05`, **STAGE3-GATED** — retained intentionally for frozen Stage 2/3 binary compatibility until Stage 3 rebuild verification completes).
- **Shard:** `doc/08_tracking/bug/db/p3_cold_hir_unresolved_public_interfaces_2026-10-05.sdn` (`status=fix-implemented-verification-pending`, `waiting-for: Stage 3 native rebuild verification`).

## Cold-HIR Constant & Declaration Inference Fix (2026-11-27, W8-2)

- **Status:** `fix-implemented-verification-pending` (`waiting-for: Stage 3 native rebuild verification`).
- **Root causes fixed:**
  1. `ModuleSurfaceConst` (`src/compiler/20.hir/hir_lowering/module_surface_types.spl`) previously dropped initializer type information when a public constant lacked an explicit `: T` annotation, while imported unannotated constants must preserve `HirSymbol.type_ == None` (`has_declared_type(symbol) == false` per `hir_import_registration_cov_kinds_spec.spl`). Added surface-side inferred constant fields (`has_inferred_type_`, `inferred_type_`, `inferred_has_elem_hint`, `inferred_ref_names`, `inferred_array_depth`) without retaining AST `Expr`s.
  2. `src/compiler/20.hir/hir_lowering/module_surface_declarations.spl` now infers concrete surface types purely from constant initializer expressions and local dependency chains (scalars, unary `-`/`~`, integer binary ops, array concatenation, non-empty homogeneous array/repeat/tuple/dict literals, non-generic local records, typed calls) and records unresolved imported/ref-chain names (`_surface_const_leaf_ref`).
  3. `src/compiler/20.hir/hir_lowering/module_surface_registry_index.spl` (`_msri_propagate_inferred_const_types` called in `module_surfaces_freeze`) resolves single-hop and multi-hop cross-module imported-constant chains (including `export use` facade chains) across frozen surfaces without inserting `Any` fallbacks.
  4. `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl`, `types.spl`, and `context_helpers.spl` record surface-inferred types in parallel scalar arrays on `HirLowering` (`imported_const_inferred_ids` / `imported_const_inferred_types`) while keeping `HirSymbol.type_ == None` when unannotated.
  5. `src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl`, `module_declarations_bootstrap.spl`, and `module_build.spl` generalize `lowered_const_value_type` for any settled `SymbolKind.Const` (local or imported), add `ArrayRepeat`, non-empty `TupleLit`, and homogeneous non-empty `DictLit` inference, and run a bounded fixed-point pass (`settle_const_decls_v1`) via shared helper `lower_const_decls_with_settle_v1` so unordered same-module constant forward references settle without `Any` fallbacks. Genuinely ambiguous empty, mixed, cyclic, missing, generic-constructor, or untyped-call initializers continue to fail closed (`unresolved-inference:0:0:declaration=constant:<NAME>`).
- **Phase 3 target module findings (`--mode=interpreter`):**
  - `src/lib/common/contracts/container/pure_backend_v1.spl` (with `: text` removed from `PURE_CONTAINER_BACKEND_V1` / `PURE_CONTAINER_ENGINE_V1`) infers `"text"` across `backend_identity_v1.spl`. Workaround `: text` + `@workaround` at lines 23-27 remains **STAGE3-GATED** until Stage 3 native compiler rebuild.
  - `src/compiler/70.backend/verify/allocator_symbol_scan.spl` (with `: [text]` removed from `FORBIDDEN_ALLOCATOR_SYMBOLS`) infers `[text]` and encodes both `hir_abi_interface_encoded_v1` and `hir_codec_abi_interface_encoded_v1` as `OK`.
  - `src/compiler/00.common/cache_contract/virtual_source_store_v1.spl` encodes `OK` in both ABI encoders once paired with its imported surfaces (`errors_v1`, `snapshot_contract_v1`).
  - `src/lib/nogc_sync_mut/src/map.spl` and `src/lib/nogc_sync_mut/src/hash.spl` encode `OK` in both ABI encoders under the updated lowering.
- **Interpreter test verification (`--mode=interpreter`, `SIMPLE_LIB=src`):**
  - `test/01_unit/compiler/cache/cold_hir_const_interface_infer_spec.spl`: 4 passed, 0 failed
  - `test/01_unit/compiler/cache/cold_hir_semantic_seed_v1_spec.spl`: 15 passed, 0 failed (updated 3 stale error expectations missing `:declaration=constant:value` / `:declaration=constant:unresolved` from `d79c12f33ba`)
  - `test/01_unit/compiler/20.hir/coverage/trait_impl_lowering_mcdc_spec.spl`: 40 passed, 0 failed (updated line 508 `ARR_STRCONST` expectation from `"infer"` to `"array"`)
  - `test/01_unit/compiler/20.hir/hir_import_registration_cov_kinds_spec.spl`: 22 passed, 0 failed
  - `test/01_unit/compiler/bootstrap/module_surface_impl_retention_spec.spl`: 2 passed, 0 failed
  - `test/01_unit/compiler/hir/unannotated_module_const_type_spec.spl`: 1 passed, 0 failed
  - `test/01_unit/compiler/hir/unannotated_module_const_shape_type_spec.spl`: 4 passed, 0 failed
  - `test/01_unit/compiler/hir/unannotated_module_global_initializer_type_spec.spl`: 7 passed, 0 failed
  - `test/01_unit/compiler/hir/imported_global_declaration_identity_spec.spl`: 1 passed, 0 failed
  - `test/01_unit/compiler/hir/imported_global_storage_binding_spec.spl`: 4 passed, 0 failed
  - `test/01_unit/compiler/mir/imported_global_infer_storage_spec.spl`: 7 passed, 0 failed
  - `test/01_unit/compiler/mir/unannotated_module_global_static_type_spec.spl`: 14 passed, 0 failed
  - `test/01_unit/compiler/cache/cold_hir_admitted_entry_seed_spec.spl`: 7 passed, 0 failed
  - `test/01_unit/compiler/cache/cold_hir_typed_archive_capture_spec.spl`: 2 passed, 0 failed
  - `test/01_unit/compiler/cache/cold_hir_semantic_action_emission_v1_spec.spl`: 2 passed, 0 failed
  - `test/01_unit/compiler/hir/module_surface_owner_transient_spec.spl`: 2 passed, 0 failed
  - `test/01_unit/compiler/hir/module_surface_primitive_type_identity_spec.spl`: 5 passed, 0 failed
  - `test/01_unit/compiler/hir/module_surface_projected_type_shape_spec.spl`: 4 passed, 0 failed
  - `test/01_unit/compiler/hir/module_surface_selected_exports_v1_spec.spl`: 11 passed, 0 failed
  - `test/01_unit/compiler/type_infer/api_signature_projection_v1_spec.spl`: 7 passed, 0 failed
- **Pending gate:** Full Stage 3 native compiler rebuild + Phase 3 cold HIR receipt verification (`waiting-for: Stage 3 native rebuild verification`).

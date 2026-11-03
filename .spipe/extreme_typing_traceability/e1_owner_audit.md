# E1 production owner audit

Source-only audit, 2026-11-01. Worktree `D:/dev/simple-release-phase3-20261101`,
branch `work/trace-query-p0-20261101`, assigned base `a42fa36c7ca`. No compiler
source changed; no runtime/test/proof qualification. The parent reports no
admitted Stage 4 runtime. P0 traceability code is a separate lane.

## Decision

Implement the next E1 slice at the HIR/type-inference boundary, not in the
textual API tool. Production has **module-local symbol IDs and structural HIR
types**, not one demonstrated globally interned `TypeId`. Build the graph from
those existing owners and carry its completeness explicitly. Do not wire the
current textual `semantic_api` walker into robust admission.

## Existing production owners

| Concern | Exact source owner and usable data |
|---|---|
| Resolved types | `src/compiler/20.hir/hir_types.spl:672`: `HirType.kind: HirTypeKind`. Primitive cases are `Int(bits,signed)`, `Float(bits)`, `Bool`, `Char`, `Str`; composites include tuples, arrays/slices, Dict, Optional/Result, Function, Union, ownership/reference wrappers. `Named(SymbolId,args)` and `DynTrait(SymbolId)` require their owning symbol table. `Infer`, `Error`, `Projection`, `Any` cannot become Safe by default. |
| Identity | Same file:98 `SymbolId`; :109 `HirSymbol` carries `defining_module`, declaration name, kind, visibility, optional `HirType`. Numeric IDs alone are not cross-module identities. `20.hir/nominal_type_relocation.spl`, `HirNominalTypeRelocator.validate_symbol`, `existing_id`, `validate_type` already validate canonical declaration owner/name/kind and relocate local IDs. Reuse this authority, never type spelling or capitalization. |
| Effective routes | `20.hir/hir_lowering/module_surface_registry.spl:390`, `module_surfaces_from_modules`, builds the registry, calls `ModuleSurfaceBuilder.resolve_export_origins` at :463, then `finish`. `module_surface_export_index.spl:9` resolves direct/facade origins. `module_surface_types.spl` owns `ModuleSurface`, `ModuleSurfaceExportOriginIndex`, and frozen `ModuleSurfaceDeclarationAuthorityIndex`. These expose canonical physical/generation identity, owner routes and declared visibility, but declaration types are parser `Type`, not already-resolved `HirType`. |
| Reexport consumption | `20.hir/hir_lowering/_Items/module_reexport_materialization.spl`: `canonical_callable_dependency_candidate`, `find_reexport_source_walk`, `resolve_materialized_enum_payload_origin` consume frozen routes. A private import is explicitly not a transitive export. This is the root-resolution seam; `HirModule.exports: [text]` alone is insufficient. |
| Transparent aliases | `20.hir/hir_lowering/type_aliases.spl`: `register_type_alias_template`, `lower_alias_template_type`, `lower_named_symbol_kind`. Templates retain owner and parameters; lowering expands the underlying HIR shape, returns `Error` on active alias cycles, and restores caller bindings. Capture expansion provenance here before it is erased; do not create a second text alias registry. |
| Generic binders | `20.hir/hir_definitions.spl:139` `HirTypeParam` has binder `SymbolId`, bounds, default and span. `30.types/type_infer/generic_calls.spl:28` `instantiate_declared_call` builds both binder-ID and scoped-name substitution maps, uses `instantiate_type`, and later `finish_direct_function_bounds` checks obligations. `30.types/type_infer_types.spl:106` `Substitution.apply` resolves inference variables recursively. A `TypeParam` spelling alone is not binder identity. |
| Actual inference consumer | `80.driver/hir_typecheck_consumer_v1.spl:22`, `collect_module_typecheck_receipt_v1`, calls `HmInferContext.infer_module`, then retains only diagnostic arrays. `driver_hir_pipeline_passes.spl:103` invokes this for modules. Thus the later driver does not currently receive resolved substitutions as an authoritative surface. |

`30.types/type_infer/typed_module_owner_v1.spl:174` is an owned typed-HIR
precedent, **not** the full solution: its preflight rejects imports/exports,
generics, nominal declarations and all but a small primitive function profile.
Do not claim it supports E1 by calling it on general modules.

## Real execution and publication seams

`80.driver/driver_orchestration.spl` owns `compile`,
`compile_with_reverse_reference_owner_v1`, `stage_parse`, `stage_lower_hir`,
and dispatch to interpret/JIT/AOT/SMF. Its native no-op admission returns an
existing artifact before normal compiler work (:276); policy/surface identity
must therefore be included in cache admission or that route denied.

The retained HIR path is `driver_hir_pipeline_lowering.spl`: after module
publication and layout checks it calls `run_typecheck_warn_pass` at :2457.
That call is profile/env-gated and uses the existing robust warning policy;
it cannot itself be the unconditional named extreme-API rule. Streaming/cold
HIR routes also need the same per-module collector before releasing the body
lease; keep only bounded owned graph facts, not borrowed HIR roots.

There is **no** `driver_post_mono_publication_v1.spl` in this source tree.
Bounded searches of current driver/HIR/MIR/backend found no callable postmono
driver pass. Do not invent a hook or claim specialization parity. Current
native transformation/publication owners are:

- `driver_aot_pipeline.spl`: `aot_compile`, `stage_lower_mir`,
  `stage_emit_object`, `native_staged_codegen_flush_v1`. The staged flush
  optimizes, calls `weave_aop`, applies debug trace, calls `compile_to_native`,
  then evicts MIR. A final-only gate misses staged emission.
- `driver_pipeline_aop.spl`: `weave_aop_with_params` mutates MIR functions.
  Retain changed-export provenance/identity and invalidate admission before
  each corresponding emission; MIR alone cannot reconstruct erased nominal
  API semantics.
- `driver_pipeline_execution.spl`: `jit_compile_and_run` weaves then calls
  `k1_jit_lane_run_modules_v1`; `execute_smf` is a separate activation route.
- `driver.spl:107`: `interpret_pipeline` loops modules and calls
  `InterpreterBackendImpl.interpret_hir_module`. In
  `70.backend/backend/interpreter.spl:125` that method creates execution
  context, defines globals and calls `main`. Check the **whole candidate
  closure** before entering this loop, not after an earlier module executes.
- `driver_api_interpret.spl:25`: `interpret_file` first attempts
  `try_load_smf_cached`; source-path checking cannot cover this bypass alone.

REPL/dynload transaction ownership was not audited in this bounded slice.
These engines remain E4 work, not implicitly covered by the driver hook.

## Smallest real implementation sequence

1. Add compiler-owned exposure records in `00.common` containing owned graph
   indices, declaration provenance, completeness/Unknown reasons and result
   paths. Avoid importing HIR implementation into common. The producer lives
   in HIR/types/semantics and consumes `HirModule`, its `SymbolTable`, frozen
   `ModuleSurfacesByName`, and the actual inference substitution context.
2. Extend the actual inference consumer to project resolved signature facts
   **while its context is alive**. Join export routes to declaration IDs;
   cover callable signatures, public member/constructor positions, aliases,
   enum payloads, trait/associated/default positions and generics explicitly.
   Missing joins/types become Unknown. First establish this bridge and its
   owned lifetime before writing the SCC walker.
3. Implement the structural walker over these facts, including binder-ID
   substitutions, nominal public operations, all actual generic arguments
   (including phantom arguments), bounded SCC/fixpoint and explicit Unknown.
   Existing trait-bound syntax can carry a domain bound, but E1 must add a
   compiler-recognized semantic guarantee; an ordinary user-implementable
   trait with a matching name must not grant safety. Wire its obligations to
   `instantiate_declared_call`/`finish_direct_function_bounds`.
4. E2 then consumes this result through a distinct named-rule severity and
   unconditional guard before execution/emission, with a generation check
   after generated changes. Cover native no-op/SMF cached admission explicitly.
   Keep existing unrelated warning policies unchanged. No text tool grants
   admission.

## Decisive E3 blocker and remaining limits

`10.frontend/core/_ParserDecls/enum_module_body.spl:1894` lowers `newunit` to
a one-field struct named `value`, registers the custom primitive and suffix,
and comments that runtime suffix registration is handled by a Rust parser
path. Adjacent `newtype` lowering auto-derives comparison operators. This is
evidence of a frontend representation seam, not usable private construction
or typed-literal execution proof. E3 must carry explicit nominal/private
representation provenance and inspect generated constructors/getters/operator
signatures; otherwise treating every named struct as opaque permits leaks.

`00.common/api_surface_contract.spl` stores textual signatures, and
`35.semantics/lint/semantic_api/type_walk.spl` classifies text names. Neither
is E1 authority. No source-level assertion here establishes complete effective
visibility closure, production specialization, safe literal lowering,
cross-engine parity, accepted performance, or formal proof.

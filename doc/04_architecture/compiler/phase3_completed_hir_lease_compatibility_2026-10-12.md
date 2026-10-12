# Completed-HIR leases: lifetime proof and consumer compatibility

Status: source analysis and proposed implementation boundary. No production
lease route is activated, no body placeholders are created, and no native
job was run. The full CLI remains unqualified after attempt-3 RSS failure.

## Existing lifetime proof

`driver_hir_pipeline_lowering.spl:466`,
`lower_streaming_hir_shard_transaction_v1`, already provides the smallest sound
body-persistence lifetime boundary. It starts one transient scope and a reverse
reference transaction; loads a complete cache entry or parses and lowers the
real source; collects actual lowering errors; computes the typed ABI receipt;
and publishes the complete HIR through `hir_cache_store_in_owned_scope`.
Before reclamation it pauses, promotes diagnostics, phase-wide memos and
frontend owners, rolls back flat rows, resets lowerer module-local state and
clears the cache's warning alias. It does not promote the module or its symbol
table snapshot. Publication/ownership failures fail the worker instead of
continuing with dangling retained roots. Cached and freshly lowered bodies
follow this same lifetime. The transaction intentionally stops before later
semantic consumers; it is not a full-compiler memory solution.

Ordinary `hir_cache_load` at `driver_hir_cache.spl:197` promotes the complete
decoded graph. The alternative `hir_cache_load_in_owned_scope` at line 217
leaves it scoped. Consequently, a lease implementation must call the latter
inside its own scope and close that scope after the consumer. Rehydrating all
modules through the former before monomorphization restores the original peak.
Dropping dictionaries containing promoted graphs does not reclaim them on
this no-GC runtime.

## Exact consumers

| Consumer | Existing boundary | What must remain available |
| --- | --- | --- |
| Imported symbol/type lowering | Frozen `ModuleSurfacesByName` and per-module lowerer | Complete selected declaration signatures, defaults, nominal provenance and aliases. The current shard transaction already preserves this path. |
| Value-struct layouts | `driver_hir_pipeline_support.spl:275` | Struct fields and Struct symbol identities across all admitted modules. Existing layout snapshots omit unrelated function bodies. |
| Aggregate validation/advice | `driver_hir_pipeline_support.spl:328–346` | Layer-equality, effect, real-time criticality, aspect validation and advice weaving. This wrapper consumes the full HIR map; struct-only layout snapshots do not replace these checks. Body transformations must be persisted. |
| HM inference, frontend diagnostics, visibility | `driver_hir_pipeline_passes.spl:193` | One complete module at a time, including local/imported symbols and actual function bodies. Existing wrapper severity and diagnostics must be preserved. |
| Safety and transfer checks | `driver_hir_pipeline_passes.spl:273` | One complete module and checker state shared between its primary and transfer walks; configured parallel policy remains enforced. |
| Any escape and enum declarations | `driver_hir_pipeline_passes.spl:396` and line 438 | Actual module input, exact configured diagnostics and final aggregate receipt counts. Per-module visits must not claim an aggregate PASS before full inventory coverage. |
| Collection planning | `driver_collection_planner.spl:74` | Complete module/path membership, binding and typed-arity preflight before publication, then actual bodies for analysis. Partial module maps are explicitly rejected. |
| Monomorphization | `monomorphize_integration.spl:250` | Canonicalized generic function/class templates, global/imported-constant types, local call inference, deterministic requests, specialized bodies, rewriting and pruning. The current pass retains every rewritten module's functions plus templates and specializations. |
| Post-mono verification | `driver_hir_pipeline_passes.spl:158` | Every transformed real body and complete verification/error counters before MIR. |
| MIR lowering | `driver_pipeline_lowering.spl:614–645` | Cross-module struct-name prescan and provider lookup; each module call receives the full module-values array. This requires an interface/provider adapter, not a nil-body substitute. |

There is also an existing routing discrepancy: ordinary streaming lowering
returns after layout/aggregate validation and cold receipts, whereas the
retained-parser branch explicitly calls HM/safety/any-escape/enum wrappers at
`driver_hir_pipeline_lowering.spl:1754–1796`. Orchestration at line 309 of
`driver_orchestration.spl` dispatches to the streaming function directly. This
analysis does not turn that discrepancy into an exception: a new leased path
must account for every configured semantic validator and its aggregate counts.

## Smallest sound implementation boundary

The existing shard transaction can form a complete typed body archive, keeping
the full admitted source inventory and selected declaration surfaces resident.
It cannot be activated as an ordinary compilation route until the consumer
contract changes. A record representing completed HIR must contain identities
and body locations, never a persistent `HirModule` or local `SymbolTable`.
Its minimum authority is physical source/path and content digest, frozen full
inventory/variant/closure digest, exact producer and source revision, target,
linked runtime/provider identity, codec schema, semantic stage and body digest.
All entries must be admitted before reporting a complete semantic phase.

Resident typed summaries must be deliberately smaller than the 3004–7581-symbol
tables observed in the largest CLI cache entries. Keep declarations and stable
module/symbol identity, typed callable/nominal signatures, global and imported
constant type projections, layout/effect/aspect facts, and generic-template
locations. Function-local scopes, local variables, expression graphs and full
provider bodies remain only in archives or active leases. The existing public
ABI receipt alone is insufficient: private generic/provider declarations and
consumer-scope imported constant IDs are needed too. Parser declaration surfaces
also do not substitute for those typed identities.

A consumer visit opens a scope, admits and hydrates the complete module plus
the provider/generic bodies that its operation requires, performs the real
check/transformation, publishes transformed bytes before closing, and promotes
only its compact summaries, diagnostics and receipt. It must clear every
retained alias into the lease, including cache warnings and lowerer module-local
owners. No HIR object, symbol table, closure capturing a body, or diagnostic
span pointing into freed storage may escape. Because generic callback return
types cannot prove that no body graph escaped, an unrestricted callback lease
API would not be a sufficient lifetime proof; each consumer boundary needs an
enumerated escape set and native lifecycle evidence.

Transformed artifacts need a separate semantic-stage identity. Overwriting the
current pre-mono HIR cache key with method-resolved, advice-woven or specialized
bodies would poison the existing cache contract. Reuse existing source/header/
checksum/framing/decode gates and cold typed receipt admission, extending the
identity to bind runtime/provider and transformation-stage authority explicitly.
Native-object publication continues through the existing accepted capsule and
CAS gates, with exact module/objectless coverage. An absent required body,
identity mismatch, incomplete diagnostic receipt or oversized required group
fails closed; none authorizes source omission, stub bodies or a higher cap.

The dominant compatibility change is a disk-backed monomorphization worklist.
It must retain only template locations and scalar/type inference summaries,
hydrate actual template bodies for instantiation, persist rewritten roots and
specializations promptly, preserve deterministic request order/symbol IDs, and
run complete post-mono verification through leases. Keeping all generic bodies
in memory or materializing every module before mono does not supply the intended
bound. The MIR provider-array API and aggregate/advice passes then require
equivalent declaration-provider/body-lease boundaries.

## Finite next implementation and diagnostic

1. Execute the already prepared 25-guard phase-memo native lifetime fixture
   when the root grants a slot; it qualifies that helper only.
2. Implement and validate one real owned-scope archive/consumer transaction
   with an enumerated diagnostic/summary escape set, unchanged admitted source
   identity and runtime/provider binding. Use a real body with a deliberate
   declared-return mismatch, a cross-module generic provider, and an identity
   rejection. Verify diagnostics are retained, bodies remain actual, and
   repeated lease closure releases registered objects. Do not add a production
   flag until the selected consumer's global preflight and receipts are sound.
3. Migrate mono template collection/worklist and the remaining aggregate/MIR
   consumers before an ordinary bounded-HIR route can claim full semantics.
   Only then run the exact full inventory under the unchanged RSS cap.

No focused activating patch is sound against the current full-map APIs. The
source-proven shard lifetime is reusable, but the ordinary compiler still lacks
the required lease-aware semantic consumer feature. This is a compatibility
boundary, not evidence that batching repairs the terminal RSS failure.

<!-- codex-research -->
# Aspect Dynamic Loading: Local Research

**Date:** 2026-08-20  
**Scope:** prerequisites for dynamic facet acquisition, resident/no-I/O operation,
pack signing/compression, lifecycle/concurrency, and performance evidence.  
**Provenance:** highest-capability Codex completion audit
(`/root/audit_aspect_plan_completion`). Lower-model sidecars: **N/A** (the task
explicitly requested a single highest-capability audit). This was a static,
read-only investigation; no production source, test, bootstrap, or Git action
was performed.

## Question

Which parts of the aspect/dynamic-load plan are actually reachable in the
current product, and which decisions and prerequisites must be settled before
the lane can be called complete?

## Existing artifacts

- Lane plan: `doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md`
- Detail design: `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
- Infrastructure/blocker analyses:
  `doc/04_architecture/compiler/aspect_dynload/`
- Performance contract inventory:
  `doc/10_metrics/startup/aspect_pack_perf_contract_measurements_2026-08-19.md`
- Completion audit:
  `build/mini_builds/aspect_plan_audit/aspect_dynload_completion_audit_2026-08-20.md`

The repository did not contain canonical feature or NFR requirements for this
lane at the time of this research. The companion `*_options.md` documents are
therefore decision inputs, not selected requirements.

## Current execution map

| Area | Current implementation | Product reachability | Missing prerequisite/evidence |
|---|---|---|---|
| Static facet syntax | Parser, HIR, MIR, and `validate_static_facet_bindings` support `.try_facet<F>()`; the HIR driver invokes the validator. | Compiler path is live. MIR lowering resolves a compile-time route and constructs a tuple. | There is no dynamic catalog/loader acquisition on this path and no `facet<F>()` language contract. The unit spec is a compiler-shape slice, not executed runtime acquisition. |
| Pack registration | `ModuleLoader` recognizes the aspect-pack section and exposes `aspect_facet`/`aspect_try_facet`. | Registration is reachable while loading SMF. | No production caller invokes `apk_load_facet`; acquisition is exercised only by tests/benchmarks. |
| Pack I/O and index | `aspect_pack_io.spl` and `aspect_pack_index_cache.spl` implement mapped reads/cache primitives. | Not connected to production facet acquisition. | Same-size file replacement can evade the current size-keyed identity unless the caller invalidates. Need file identity/generation and a canonical owner. |
| Runtime lifecycle | Startup/manual activation, seal, pin, unpin, and unload APIs exist. | Definitions have no product caller. | Need selected state machine, generation/ownership rules, reference/quiescence policy, and product wiring. |
| Advice dispatch | `JoinpointSlotTable` and `AdviceBindingRegistry` exist and are tested. | Re-exported but not consumed by compiler/backend/runtime product code. | Need binding-plan IR, stable IDs, backend slot emission, publication semantics, and an end-to-end caller. |
| Native SMF loading | Canonical W^X mapper admits exact bytes, bulk-copies to RW memory, seals RX, and calls entry pointers. | The product startup path does not pass admitted bytes to it. | `dynsmf_session_load_impl` calls `smf_dlopen_checked`; that path always fails with “admitted smf bytes required”. `smf_dlopen_admitted` exists but is not wired into startup. |
| Concurrency | Aspect-pack CAS/activation helpers and concurrency scenarios exist. | Interpreter tests are not proof of real contention. | Rust interpreter task externs execute closures inline and return synthetic handles. Native Stage-4 contention evidence is required. |
| Bootstrap | Stage-2 receipts exist. | No admitted Stage-3/Stage-4 deployment. | The retained Stage-2 source hashes no longer match `src/lib/process.spl` and `src/lib/nogc_sync_mut/log.spl`; Stage-3 previously terminated after geometric RSS growth to about 17 GiB. |

## Prerequisite findings

### 1. Dynamic facet semantics are unspecified

The currently accepted surface is static `.try_facet<F>()` only
(`src/compiler/10.frontend/core/parser_expr.spl`,
`src/compiler/20.hir/hir_lowering/expressions.spl`, and
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`). The compiler
resolves a static route ID; it does not specify whether a missing facet should
load, wait, return nil, fail, or be forbidden by execution phase. The plan also
uses `facet<T>()` terminology without a corresponding implemented source
contract. A requirement must distinguish at least:

- compile-time/static binding from catalog-backed dynamic acquisition;
- mandatory acquisition from optional probing;
- first-use activation from resident-only lookup;
- synchronous wait, explicit future, or nonblocking failure;
- visibility of a newly published generation to concurrent callers.

### 2. Resident/no-I/O needs both static and temporal enforcement

The repository has source scanning for forbidden I/O and runtime operational
state, but no complete driver-to-runtime policy. A static call-graph diagnostic
can reject known I/O reachability; it cannot prove that an already-mapped
dynamic lookup will not fault into file-backed pages or that an indirect call
will not reach unknown code. A runtime phase guard can fail closed at the
boundary; it cannot replace source diagnostics. The requirements must decide
whether `@resident`, `@no_io`, `@realtime`, and operational sealing are one
union policy or separately composed guarantees.

### 3. Signing and zstd are policy work, not just parser work

Pack verification currently has fail-closed plumbing but no operational trust
root, key custody, rotation, revocation, or build-signing owner. Enabling a
signature flag before those exist would create a false security claim. Content
hashing remains useful for byte identity but is not publisher authentication.

The zstd pending item similarly needs a dictionary compatibility contract:
dictionary ID/profile binding, missing-dictionary behavior, decoder memory
limit, decompression bound, and whether verification precedes decompression.
The safest current production posture is explicit feature disablement until a
user-selected signing and compression policy is implemented end to end.

### 4. Lifecycle requires a real happens-before edge

The late-state API vocabulary exists, but there is no product state machine
connecting catalog discovery, verification, mapping, relocation, publication,
pinning, and unload. The desired “one activation under contention” property
requires a native once/CAS protocol whose successful publication happens-before
all observing calls. Inline interpreter task execution cannot validate races,
waiters, failure fan-out, or retry behavior.

Unload is a separate decision. It requires generation-aware handles, removal of
all relocated references or patchpoints, and an explicit quiescence mechanism.
Without those, “load once and pin for process lifetime” is the honest supported
contract.

### 5. The compiler-to-loader binding bridge is absent

`binding_plan_id_resolution_2026-08-19.md` correctly records the blocker: the
design does not define the assigner or namespace for binding-plan IDs, a
serializable binding summary, or the advice/joinpoint analogue of a facet plan.
Slot-table primitives alone do not provide compiler lowering or backend
emission. This bridge must be specified before late binding can be production
reachable.

### 6. Performance claims lack an admitted success path

Existing measurements are useful primitive baselines, but the aspect-pack
first-use/cache measurement observed `APK_MODULE_CORRUPT`, not successful
acquisition. There is no admitted Stage-4 product binary and no representative
evidence for:

- no-aspect startup overhead;
- successful first-use verify/decompress/map/relocate/publish latency;
- hot resident facet lookup and advice dispatch;
- cache-hit behavior without file I/O;
- maximum RSS for representative packs and concurrent waiters;
- loader/compiler/interpreter attribution when a target fails.

Numeric choices and a common measurement protocol are proposed in the NFR
options document; none is selected here.

## Recommended decision order (not a selection)

1. Select the dynamic/static acquisition and failure semantics.
2. Select resident/no-I/O composition and the operational-seal boundary.
3. Select lifecycle generation/unload and concurrency publication semantics.
4. Select signing and zstd profiles, including an explicit disabled state.
5. Define binding-plan IR and compiler/backend/product-loader ownership.
6. Repair admitted bootstrap provenance, then measure the selected NFR profile.

This ordering minimizes implementation whose externally observable semantics
would otherwise have to be rewritten after the fact.


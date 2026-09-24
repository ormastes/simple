# Kernel Plugin Fabric Detailed Design

**Status:** Proposed
**Date:** 2026-09-03

## Canonical Records

All ABI records begin with `abi_version: u32` and `struct_size: u32`. Generated assertions verify size, alignment, and offsets in Simple, C, Rust, and C++.

```text
Id128, Digest256
ProviderDescriptorV1, InterfaceDescriptorV1, ImportRequirementV1
MemoryContractV1, ConcurrencyContractV1, TrustContractV1
OperationRequestV1, OperationResultV1
AdmissionReceiptV1, ExecutionReceiptV1
DiagnosticV1, TextEditV1, AnalysisCoverageV1
```

Persistent provider/interface/operation/capability IDs are derived from canonical tuples and collision-checked by the sealer. Dense slots are generation-local and never persisted without the composition digest.

## Generated ABI

The `*.kpf.sdn` compiler canonicalizes schema, assigns IDs, computes schema digests and required-operation masks, validates POD/bounds/ownership, and emits:

- Simple static traits and wire records;
- canonical `simple_kernel_plugin_v1.h`;
- Rust `repr(C)` raw bindings plus safe owner/session wrappers;
- C++ C-ABI include plus move-only RAII wrappers;
- worker codecs and malformed-record fixtures;
- static registries, SCI projections, documentation, and optional WIT.

One symbol exposes native ABI major V1. Language exceptions, panics, closures, objects, allocators, and native futures cannot cross the boundary. New interfaces prefer caller-owned input/output arenas; legacy provider-owned output is compatibility-only.

## Runtime Data Structures

```text
GenerationalSlotMap<GenerationState>
GenerationalSlotMap<ProviderState>
GenerationalSlotMap<SessionState>
GenerationalSlotMap<RequestState>
BoundedRing<Submission>
BoundedRing<Completion>
BoundedRing<Event>
BoundedDeadlineQueue
FixedArena / admitted chunk pool
```

Handles encode generation, slot, and slot epoch. Every operation validates the handle in O(1). Cancellation is idempotent. Pin/unpin modifies one table entry. Full rings return typed backpressure without allocation.

## Lifecycle

```text
Declared -> Indexed -> Admitted -> Prepared -> Starting
         -> ShadowActive -> Published -> Draining -> Retired -> Unloaded
active state -> Faulted -> Disabled | RolledBack
```

Preparation resolves imports, allocates admitted resources, constructs capability leases, and caches operation tables. Publication swaps one compatible generation atomically. Unload requires zero sessions, requests, pins, callbacks, subscriptions, and borrowed buffers.

## Operation Model

Portable asynchronous semantics are `open_session`, `submit_batch`, `poll`, `cancel`, `quiesce`, and `close_session`. Generated wrappers may expose Simple futures, Rust futures, or C++ coroutines, but the ABI remains handle-based polling. Calls are coarse batches, never token/node-level FFI.

Static-direct generation bypasses encoding and permits inlining. Static-table performs a bounds check and one indirect call. Native/SMF performs admission lookup once then cached dispatch. Worker transport batches framed or shared-memory pages. Wasm uses the same logical schema with canonical ABI costs accepted explicitly.

## Memory Profiles

| Profile | Initialization | Sealed run phase |
|---|---|---|
| `StaticNoAlloc` | static/link-time | no heap/allocation |
| `ArenaOnly` | host-preallocated | bounded arena only |
| `NoGcBounded` | explicit admission/open allocation | no hidden growth; per-call allocation forbidden or budgeted |
| `NoGcGeneral` | explicit no-GC allocator | measured/capped allocation |
| `IsolatedManaged` | worker runtime may allocate/GC | bounded validated boundary |

Allocator interposition, forbidden-effect scans, capacity high-water marks, canaries, and long-run tests provide evidence. A no-GC declaration alone never proves no-allocation.

## Lint Design

Language providers expose stable snapshots and requested facts (`SourceText`, `Tokens`, `Syntax`, `Symbols`, `Types`, `CFG`, `DataFlow`, `Effects`, `Ownership`, `ProjectGraph`, `BuildConfiguration`). Portable rules consume normalized fact pages; language-native rules execute inside their provider.

`LintRunResultV1` includes requested/admitted/completed/skipped units, rules and phases; unavailable facts; provider/toolchain receipts; diagnostics; fixes; cancellation/deadline; and a verdict. Only complete required coverage with zero effective findings is clean. Fixes carry expected snapshot digests, applicability, and conflict groups and apply transactionally.

## IDE Design

`ToolingWorkspace` owns immutable document revisions, project/build models, language sessions, diagnostic/fix cache, command/test/debug facets, cancellation, progress, and receipts. LSP/DAP are edge adapters. Existing editor manifests map to KPF IDs, activation predicates, capability leases, sessions, subscriptions, and worker placement. Unknown placement/capability is an error, never an in-process default.

VS Code retains shell-specific views, editors, webviews, and UI. SVIM/Simple IDE retains editing/session authority. Both reject stale results by revision/digest and expose authoritative, degraded, or unavailable state explicitly.

## Extended Enum And MDSOC++

Extended enums represent sealed constructor families, with persistent constructor identity and generated required-operation tables. Static/Complete closure maps to dense generation tags; critical products reject `Dyn`. Provider/interface/capability identity remains descriptor-based.

MDSOC++ capsules declare provided/required facets, authority, memory, concurrency, lifecycle, persistence schema, upgrade compatibility, failure containment, and observability. Cross-capsule commands mutate one authority, queries are read-only, events are immutable, and mutable object references never cross the boundary. ECS is optional and capsule-private.

The real IDE/tooling pilot stores `{active deployment, active state, optional
draining deployment, draining state, inflight count}` under one owner. An
upgrade reserves three receipt slots, verifies the successor and migration,
constructs migrated state, and only then swaps the active/draining pair. The
receipt sequence is `StateMigrated -> Published -> Draining`, followed by zero
or more `Draining` progress records and one `Retired` record. A rollback swaps
the retained deployment/state back into active authority. No rollback may
resurrect a retired generation. Invalid drain counts and insufficient receipt
capacity leave product authority unchanged.

## Error Handling

All failures are typed: malformed schema, collision, missing/ambiguous provider, version/schema mismatch, capability denial, capacity exhaustion, stale handle, cancellation, deadline, malformed output, provider crash, partial coverage, and tool failure. No error path substitutes a clean result or silently changes placement.

## Requirement Traceability

| Requirements | Design evidence |
|---|---|
| REQ-KPF-001, 003, 006 | generated projections, SCI authority, cached dense dispatch |
| REQ-KPF-002, 004 | K0g boundary and fixed canonical records |
| REQ-KPF-005, 007 | memory profiles, bounded structures, generational lifecycle |
| REQ-KPF-008 | single schema generator and cross-language assertions |
| REQ-KPF-009 | coverage-bearing lint result and verdict predicate |
| REQ-KPF-010 | shared tooling workspace and thin clients |
| REQ-KPF-011 | constructor-only extended-enum integration |
| REQ-KPF-012 | capsule descriptors, sealing, upgrades and receipts |

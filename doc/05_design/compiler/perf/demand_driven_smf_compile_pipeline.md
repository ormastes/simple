# Detail Design — Demand-Driven SMF Compile Pipeline

## Core interfaces

- `ArtifactServiceProfileV1`: compiler/test/MCP/LSP profile, compatibility ID, pools, budgets.
- `BuildActionV1`: action ID, inputs, dynamic edges, outputs, pool, priority, snapshot revision.
- `SmfPackageIndexV1`: verified section directory and symbol-to-section lookup.
- `ImportMaterializationV1`: atomic state, owner action, waiters, failure receipt.
- `HirDemandSetV1`: requested symbols, operations, bodies, generic shapes, initializer/provider dependencies.
- `MirAdmissionV1`: proof that every required type/body/provider is concrete and snapshot-bound.
- `FileReadPolicyV1`: `auto_map`, `must_map`, `prefer_map`, or `buffered`.
- `ReadOnlyFileViewV1`: retained snapshot identity, selected policy/transport, size, asynchronous bounded `view(offset, length)`, prefetch hint, and close lifecycle independent of mapped or buffered transport.

## Import pipeline

1. Resolve import through package index.
2. Read verified SMF header/index when compatible.
3. Otherwise read a bounded source head to discover package/import declarations and schedule cold metadata generation.
4. Create metadata proxies for indexed symbols.
5. Type checking requests only referenced declarations.
6. Inlining/generic use requests the corresponding body chunk.
7. HIR demand closure records operations and dependencies.
8. Materialize SCC closure and admit it atomically to MIR.

If the bounded head contains syntax that prevents sound import discovery, stop head mode and schedule the normal parser for that file. Never guess an import edge.

## Scheduling

- One coordinator owns graph mutation; workers return immutable results.
- Pools: `io`, `parse`, `semantic`, `mir`, `cranelift`, `llvm`, `gpu-experimental`, `link`, `test`.
- CPU capacity follows host/jobserver limits; LLVM and linking have stricter memory pools.
- Stdio is framed and buffered per action, then committed in deterministic order.
- A cache hit completes an edge without starting the daemon solely for speculation.

## Generic implementation

Canonical `LayoutShapeId` groups types with compatible ABI, pointer maps, size/alignment, and operation dictionary. One baseline body is emitted per shape. Primitive/vector hot paths and profile-selected sites may publish specialized chunks. Both forms share source/HIR identity but have distinct implementation keys.

## Parser acceleration

- Stage 1: common async file I/O defaults to `auto_map`, capability-selecting read-only `mmap`/platform windows when beneficial and otherwise using chunked asynchronous buffered reads, exposed through `ReadOnlyFileViewV1` with ASCII lookup tables.
- Stage 2: SIMD scan for newline, quotes, delimiters, comment markers, and likely `use` tokens.
- Stage 3: independent-file parse tasks.
- GPU: notify that a candidate exceeded the configured size/crossover; use only an experimental pool after transfer-inclusive benchmark admission.

Mapped views use bounded windows rather than requiring whole-file mappings. The fallback maintains a small read-ahead ring, coalesces adjacent section requests, supports cancellation, and caches immutable chunks by snapshot/file identity. Mapping faults, address-space pressure, unsupported filesystems, and device/special files select or return through the buffered path without changing parser/SMF behavior.

`must_map` never silently falls back. `prefer_map` always attempts mapping before fallback. `auto_map` may avoid an attempted mapping when platform capability, file identity, size, access pattern, or resource budget already proves it unsuitable. All completion is represented through the normal Simple promise/task result so synchronous-looking callers do not need callback-style source code.

## Compatibility CLI

- `simple build|check|run|test`: nearest `simple.sdn` package.
- `simple build file.spl`: existing single-file semantics.
- `simple build ./...`: explicit recursive package selection.
- `--source PATH`: preserved explicit source root.
- `--entry` without a resolvable package: warning plus existing behavior during migration; later fail closed only after a documented compatibility release.

## Final dirty/mixed demand authority freeze

These interfaces are normative. Implementers must not rename them, weaken their
authority fields, substitute environment strings for typed values, or fabricate
digests or outputs to satisfy integration tests.

### `DirtyModuleRecordV1`

`DirtyModuleRecordV1` is the sole admitted source-side input for a dirty module.
`PackageIndexRouteV1` owns `dirty_modules: List[DirtyModuleRecordV1]`; a bare
source path is not compilation authority.

Required fields:

- `package_id`, `module_id`, and canonical `source_identity`
- `scv_revision`, `scv_tree_digest`, and `scv_inventory_digest`
- source content, semantic, export, initializer, and provider digests
- exact direct dependency module IDs and package IDs
- frozen source read-set facts, including byte-range or whole-file authority
- package-index generation, producer compatibility ID, and configuration variant

Construction fails with `DirtyModuleRecordErrorV1::{outside_snapshot,
identity_drift, inventory_mismatch, dependency_missing, dependency_ambiguous,
read_set_invalid, producer_mismatch, variant_mismatch}`. Records are immutable,
sorted by `(package_id, module_id)`, duplicate-free, and must reference only the
admitted SCV snapshot. Dirty closure is derived from these records; no directory
walk, live-file reopen, inferred dependency, or environment-only authority is
permitted.

### `CombinedMirEvidenceBuilder`

`CombinedMirEvidenceBuilder` merges archive evidence and
`DirtyModuleRecordV1` source evidence into one `MirAdmissionV1`. Its input is a
single route and one expected SCV identity. It rejects mixed revisions, trees,
inventories, variants, producers, duplicate symbols/modules, unresolved edges,
missing read-set facts, and archive/source semantic conflicts.

Errors are `CombinedMirEvidenceErrorV1::{empty_route, scv_identity_mismatch,
archive_authority_invalid, dirty_authority_invalid, duplicate_module,
duplicate_symbol, dependency_unresolved, dependency_conflict,
read_set_incomplete, admission_rejected}`. The builder is deterministic and
side-effect free. The resulting admission retains the complete SCV identity and
the union of archive and frozen-source dependency/read-set evidence.

### `RouteCapabilityScope`

`RouteCapabilityScope` exclusively owns every pinned archive/file capability
opened while evaluating one route. `register(capability)` transfers ownership;
`close_all()` is idempotent and consuming. Success, typed failure,
cancellation, timeout, panic-to-error conversion, and partial materialization
all execute `close_all()` exactly once before returning. Capabilities may not
escape except through an explicit ownership transfer recorded by the scope.

Errors are `RouteCapabilityScopeErrorV1::{already_closed, duplicate_capability,
invalid_transfer, close_failed}`. Close failures are retained in the route
diagnostic receipt and cannot turn a failed route into success.

### `SccCompileOutputsV1`

`SccCompileOutputsV1` is the only dirty-SCC publication payload. It contains the
actual compiler-produced package image, interface/action members, dependency
and read-set receipts, MIR admission digest, baseline artifact identity, and
diagnostics for every package/module in exactly one scheduled SCC.

Errors are `SccCompileOutputsErrorV1::{scc_identity_mismatch,
member_set_incomplete, unexpected_member, duplicate_member, output_missing,
output_placeholder, admission_mismatch, artifact_mismatch,
diagnostic_order_invalid}`. Publication accepts only complete outputs from
successful compiler actions, groups them by scheduled SCC, stages all members,
and exposes them through one `CasBatchTransactionV1` generation switch. Empty,
synthetic, path-only, or partially successful payloads are rejected.

### Required call sequence

1. Admit one immutable SCV snapshot and compatible package-index generation.
2. Build `PackageIndexRouteV1`, including complete `DirtyModuleRecordV1` rows.
3. Create one `RouteCapabilityScope`; open and register clean archive capabilities.
4. Materialize clean archive facts and dirty frozen-source facts without live fallback.
5. Build one combined admission through `CombinedMirEvidenceBuilder`.
6. Reject the route before MIR construction unless combined admission succeeds.
7. Compile each scheduled dirty SCC and construct `SccCompileOutputsV1` only from real outputs.
8. Publish complete SCC outputs through one atomic CAS batch; never publish on partial failure.
9. Close the route scope on every exit, then return deterministic diagnostics/receipt.

### Cross-interface invariants

- One route has exactly one SCV revision/tree/inventory identity.
- Every MIR dependency is proven by either admitted archive evidence or one dirty record.
- Mixed routes include both clean and dirty dependency evidence; neither side may be omitted.
- No dirty-only route requires an archive capability or fabricates archive evidence.
- No clean-only route opens source.
- No capability is leaked, reopened by path, or used after scope close.
- No archive mapping becomes visible until every output in the SCC is complete and verified.
- Backend promotion and archive publication consume the same `MirAdmissionV1` digest.

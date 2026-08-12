<!-- codex-architecture -->
# Mission-Critical Infrastructure Hardening V2 Architecture

Status: proposed for implementation
Selected requirements: `C1 + O1 + R2 + M2 + N2`
Date: 2026-08-11

## 1. Purpose and assurance boundary

This architecture turns the compiler/tooling, SimpleOS, rendering, and allocation
claims into one configuration-specific, fail-closed release decision. It does not
declare every Simple target mission critical. A claim is valid only for the exact
compiler, source tree, configuration, certified platform rows, rendering profile,
allocation profile, and evidence artifacts admitted by the release matrix.

The release boundary has five independently rejecting capsules:

1. exact-current compiler admission;
2. certified SimpleOS platform admission;
3. packed DrawIR-v3 rendering admission;
4. strict or explicitly relaxed allocation admission; and
5. aggregate evidence admission.

An unavailable capsule, stale evidence, unknown identity, skipped check, synthetic
handle, source-only inspection, or cached result without validated inputs produces
`BLOCKED` or `REJECTED`, never a weaker implicit PASS. The aggregate may narrow a
claim to the rows that passed, but it may not promote partial evidence to an
umbrella claim.

## 2. Architectural decisions

### 2.1 Pattern evaluation

| Concern | Considered pattern | Decision and reason |
|---|---|---|
| Cross-cutting evidence collection | Feature transform woven into every producer | Reject. It obscures control flow and can accidentally turn observation into authority. Producers emit typed receipts through explicit ports. |
| Release assurance across compiler, OS, renderer, and runtime | Virtual capsule | Adopt. Each capsule owns its checks and typed receipt; a common admission capsule composes receipts without reaching into sibling internals. |
| Platform/backend variability | Runtime adapter | Adopt only below stable contracts. Host, guest, compiler probe, and render backend adapters translate native facts to common receipts; they cannot relax policy. |
| Evidence persistence | Shared mutable registry | Reject. Use immutable, content-addressed evidence records and a single matrix builder. |
| Render construction | Growable command vectors or per-producer display lists | Reject for active generations. Adopt count-plan-admit plus one packed DrawIR-v3 generation arena. |
| Relaxed allocation | Global allocator mode | Reject. Adopt sealed per-domain arenas selected by a versioned profile; strict remains default. |
| Admission caching | Time-based “last green” cache | Reject. Adopt content-addressed memoization keyed by all authoritative inputs, with explicit freshness ceilings. |

### 2.2 MDSOC structure

The hardening feature is a virtual capsule assembled from contracts in common
layers and owner-private implementations. It is not a new universal framework and
does not move hot execution code into a generic assurance module.

```text
common assurance contracts
  |-- CompilerAdmissionReceiptV1
  |-- CertifiedPlatformManifestV1
  |-- RelaxedAllocationProfileV1
  |-- rendering generation/overflow receipts
  `-- HardeningEvidenceMatrix
          ^               ^               ^
          | typed ports   | typed ports   | typed ports
 compiler capsule   SimpleOS capsule   rendering/runtime capsule
          \______________ admission capsule ______________/
                            |
                     release claim receipt
```

Rules:

- `common` owns stable value contracts, enums, hashes, receipt schemas, parsing,
  canonical serialization, and structural validation only.
- Compiler, SimpleOS, rendering, and allocation siblings expose receipts through
  those contracts. They do not import another sibling's private implementation.
- The allocation runtime owns one canonical `DomainArenaV1` execution and two
  release lanes. Allocation emits `mci-allocation-domain-arena-evidence-v1`
  plus `allocation.unsigned.template`; fault injection emits
  `mci-fault-injection-domain-arena-evidence-v1` plus
  `fault-injection.unsigned.template`. The admission capsule owns their distinct
  scenario maps and parses each signed conversion as a separate required row.
- Policy belongs to the admission owner, not to adapters or evidence producers.
- Backend-specific execution remains beside its backend because its invariants and
  hot paths differ. Only its stable provenance/readback receipt moves upward.
- GUI and Web retain private semantic state. They lower through their canonical
  semantic/layout owners into the common DrawIR boundary; they never share a
  private display-list implementation.
- No capsule may infer PASS from absence of a failure record.

## 3. Layer and module ownership

The paths below are intended implementation ownership. Exact filenames may be
split during detail design, but sibling dependency directions are normative.

| Owner/layer | Intended path | Owns | May depend on |
|---|---|---|---|
| Common assurance contracts | `src/lib/common/assurance/` | The five named V1 contracts, receipt status/reason types, canonical hash/time/artifact identities | Fundamental value/hash/serialization modules only |
| Compiler identity facts | `src/compiler/00.common/assurance/` | Compiler identity, lineage, source/config hashes passed through compiler layers | Compiler common contracts |
| Compiler admission orchestration | `src/compiler/80.driver/assurance/` | Exact-current probe plan, clean-build comparison, artifact execution, `CompilerAdmissionReceiptV1` construction | Compiler pipeline plus common assurance; not private MCP/LSP modules |
| Tool evidence adapters | `src/compiler/90.tools/verify/` and application-owner adapters | Typed check results for lint, duplication, compiler/lib, MCP/LSP, runtime contracts, performance | Public tool/application entrypoints |
| SimpleOS manifest and guest receipt owner | `src/os/sosix/qemu_evidence/` | Manifest validation, selected-row correlation, guest filesystem/execution receipts | Common assurance and public OS/QEMU ports |
| SimpleOS platform adapters | Existing port-specific subtrees under `src/os/port/`, `src/os/lib/`, and host scripts | Boot/mount/list/execute/device facts for one target | Their own port internals plus the common receipt contract |
| Durable Draw IR contract | `src/lib/common/ui/draw_ir.spl` and packed-v3 companion modules under `src/lib/common/ui/` | Renderer-neutral immutable composition identity and packed generation layout | Common UI value types; never Engine2D caches/handles |
| GUI producer | Existing widget/scene owners | GUI semantic state, count plan, lease writing | Public DrawIR-v3 producer interface |
| Web producer | `src/lib/gc_async_mut/gpu/browser_engine/` semantic/layout owner | DOM/style/layout state, count plan, lease writing | Public DrawIR-v3 producer interface |
| Engine2D consumer | `src/lib/gc_async_mut/gpu/engine2d/` and OS compositor adapters | Validation, transient font batches, backend submission/readback/provenance | Sealed DrawIR-v3 generation and backend-private resources |
| Allocation policy | `src/lib/common/assurance/` contract; runtime owner beside allocator | Profile validation in common; arena lifecycle/quota/rollback in runtime | Runtime memory primitives; no renderer/compiler policy inference |
| Aggregate admission | A dedicated Simple application under `src/app/` selected in detail design | Matrix construction, freshness/integrity checks, claim projection, report serialization | Typed receipts only |

Shell checkers remain orchestration adapters during migration. They must invoke
compiled/cached Simple owners, use bounded capture, and emit a receipt that the
Simple aggregate parser structurally validates. Shell text is not itself the
authoritative contract.

## 4. Shared contracts

All contracts are immutable value records with an explicit `schema_version`,
canonical serialization, strict parsing (unknown required fields reject), and a
content hash over their canonical form. Status is one of `PASS`, `REJECTED`, or
`BLOCKED`; there is no `UNKNOWN => PASS` conversion.

### 4.1 `RelaxedAllocationProfileV1`

```text
RelaxedAllocationProfileV1
  schema_version = 1
  profile_id, profile_hash
  strict_default: bool                    # must be true
  domains: [AllocationDomainPolicyV1]
  forbidden_contexts: [CriticalContextV1]
  telemetry_policy, fault_injection_policy
  source_hash, configuration_hash

AllocationDomainPolicyV1
  domain_id
  arena_kind                              # sealed generation arena only
  hard_quota_bytes, alignment
  maximum_objects, maximum_generations_in_flight
  ready_seal_required: bool
  allowed_contexts
  rollback_strategy                       # discard unpublished generation
  owner_module, owner_thread_or_pool
```

Normative invariants:

- Absence of a valid profile selects strict zero-post-ready allocation.
- Kernel, ISR, storage commit, ownership publication, isolation transitions, and
  any additionally declared critical context are forbidden even if a domain is
  listed as relaxed.
- Each domain has physically/logically isolated capacity. It cannot borrow from
  another domain or a global fallback allocator.
- An arena is allocated before ready, then sealed. Active generations cannot
  grow. Exhaustion returns a typed error within the provoking operation.
- Publication occurs only after a complete generation validates. Failure discards
  the unpublished generation and preserves committed storage and the last valid
  generation.
- Telemetry records quota, current use, high-water, generation, rejection count,
  and fault-injection point. Telemetry atomics may not publish ownership,
  lifetime, readiness, or isolation state; relaxed atomics are out of scope.

### 4.2 Packed DrawIR-v3 generation arena

The arena is the physical representation behind the existing logical
`DrawIrComposition` boundary. It contains fixed, offset-addressed regions for
commands, batches, glyph references, image references, strings/bytes, hit/event
metadata, and producer-owned opaque IDs where approved. It never contains GPU or
window handles, device pointers, transient font atlases, glyph cache entries, or
backend command buffers.

```text
DrawIrV3GenerationHeader
  schema/layout version
  arena_id, generation_id, scene_id
  source/configuration/profile hashes
  total_capacity, admitted_bytes
  per-region offsets/counts/capacities
  producer lease table
  content hash, sealed flag

DrawIrV3AdmissionPlan
  requested per-region counts and bytes
  fixed queue depth and maximum in-flight generations
  arithmetic-validation receipt
  producer lease plan

DrawIrV3RejectionReceipt
  arena/generation/scene identity
  producer and region
  requested, admitted, hard capacity
  reason (overflow, quota, invalid offset, stale generation, queue full, etc.)
  prior valid generation identity
```

Construction is a four-stage transaction:

1. **Count:** canonical GUI/Web/WM owners count without emitting or allocating.
2. **Plan:** a checked prefix scan computes disjoint regions and leases. Integer
   overflow, count mismatch, queue saturation, or quota excess rejects here.
3. **Admit/write:** the arena owner admits the whole generation and producers
   write only within their leases. No reallocation, truncation, clamp, fallback,
   or child-composition flattening allocation is allowed.
4. **Verify/seal/publish:** counts, offsets, IDs, hashes, and initialized ranges are
   verified. Only a complete sealed generation is atomically published.

Engine2D accepts only sealed, current generations, validates identity before
submit/readback, and returns typed backend provenance. Text goes through
`draw_text`; an enabled vector face creates transient `FontRenderer` and
`FontRenderBatch` material owned by Engine2D outside Draw IR. Engine3D HUD/world
remains a separate lane and cannot bypass this GUI/Web/2D boundary.

### 4.3 `CertifiedPlatformManifestV1`

```text
CertifiedPlatformManifestV1
  schema_version = 2                    # sole accepted wire schema; V1 is the source API name
  manifest_id, manifest_hash
  release_source_hash, compiler_receipt_hash
  rows: [CertifiedPlatformRowV1]          # all 24 contract cells visible
  stress_profile_id, allocation_profile_hash, render_profile_hash

CertifiedPlatformRowV1
  row_id, host_identity, guest_identity, architecture, configuration_hash
  selected: bool
  required_capabilities
  boot/mount/list/execute receipt hashes
  compiler_lineage/source/run-correlation receipt hashes
  payload placement receipt hash
  stress receipt hash
  status, reason, artifact identities
```

The manifest is an allow-list, not discovery. A selected row must prove correlated
boot, mount, target-side directory listing, arbitrary filesystem program
execution, exact compiler lineage/source identity, and the same run nonce. The
guest payload receipt must prove and execute the required compiler/interpreter/
loader artifacts from guest storage, including `/usr/bin`, `/bin`, `/sys/apps`,
and `/SYS/SIMPLETOOL.SDN` placements. Host-side existence is insufficient.

All 24 matrix cells remain serialized. Unselected or unavailable rows carry a
reason and cannot support a broader claim. Duplicate row keys, missing selected
receipts, mismatched nonce/hash, zero-byte or fabricated executables, and weak
stubs reject the row. Platform adapters cannot mark themselves certified; only
the manifest admission owner can do so.

### 4.4 `CompilerAdmissionReceiptV1`

```text
CompilerAdmissionReceiptV1
  schema_version = 1
  receipt_id, receipt_hash
  compiler_binary_hash, resolved_path
  exact_source_hash, configuration_hash, dependency/toolchain hashes
  lineage = PURE_SIMPLE_EXACT_CURRENT
  bootstrap_parent identities
  clean_build_environment identities[2]
  reproducibility comparison
  discriminating fixtures: [ExecutedCompilerFixtureV1]
  bounded tool-check receipt hashes
  status, rejection reasons, timestamps

ExecutedCompilerFixtureV1
  fixture/source/config hashes
  emitted_artifact hash and executable format
  command identity, timeout, exit status
  stdout/stderr bounded-capture hashes
  semantic oracle identity and result
```

Admission resolves and hashes the actual invoked compiler, not a wrapper label.
It rejects Rust-seed, hybrid, stale, unknown, missing-function, non-executable, or
source-mismatched output. Every fixture must execute its emitted artifact and
check a discriminating semantic oracle. Two recorded clean-host builds must
reproduce before release PASS; inability to provision either environment is
`BLOCKED`. Cache hits may avoid rebuilding only when every input/environment/
tool identity matches and the receipt remains fresh, but emitted fixtures are
still executed for the candidate admission.

### 4.5 `HardeningEvidenceMatrix`

```text
HardeningEvidenceMatrix
  schema_version = 1
  matrix_id, matrix_hash, release_claim_id
  source/configuration/profile hashes
  compiler_receipt_hash
  platform_manifest_hash
  rendering/allocation/concurrency/tool receipt hashes
  requirements: [RequirementEvidenceRowV1]
  claim_projection, reviewer_identity
  created_at, freshness_deadline
  aggregate_status, reasons

RequirementEvidenceRowV1
  requirement_id
  applicable claim/profile/rows
  executable evidence identities
  negative-control/fault-injection identities
  timeout and observed duration
  artifact hashes/paths
  producer status, matrix status, reason
```

The matrix is the sole release-admission projection. It represents compiler,
library, MCP, LSP, bootstrap-essential-tool, lint, duplication, whole-test,
startup/latency/RSS, runtime-contract, direct-env, OS, rendering, allocation, and
concurrency evidence. Each REQ/NFR row must map to executable non-placeholder
SSpec evidence and a readable operator flow. A producer PASS is necessary but
not sufficient: the matrix independently checks schema, identity, freshness,
applicability, negative controls, time bounds, and artifact integrity.

## 5. Control flows

### 5.1 Release admission

```text
candidate source/config
  -> resolve exact compiler -> build twice -> execute fixtures
  -> construct CompilerAdmissionReceiptV1
  -> build guest payloads with admitted compiler
  -> execute selected CertifiedPlatformManifestV1 rows
  -> exercise packed rendering/allocation/concurrency profiles
  -> collect bounded tool and performance receipts
  -> validate identities + freshness + negative controls
  -> HardeningEvidenceMatrix
  -> PASS scoped claim | BLOCKED/REJECTED with complete reasons
```

The aggregate runs independent checks in a bounded runtime pool with fixed
in-flight admission. Subprocess stdout/stderr are captured to bounded files;
receipts retain hashes and selected diagnostic tails rather than unbounded text.
Timeout and cancellation are deterministic. Every kill/wait adapter rejects
`pid <= 0` before invoking the platform primitive. Cancellation cannot publish a
partial receipt.

### 5.2 Frame hot path

```text
semantic mutation
  -> GUI/Web/WM count (no allocation)
  -> checked global plan + queue admission
  -> producer leases in inactive preallocated generation
  -> verify + seal
  -> publish generation identity
  -> Engine2D validate/submit
  -> exact CPU/device readback and backend receipt where claimed
```

There are no full-tree scans, subprocesses, manifest parsing, evidence hashing of
unrelated files, arena growth, or report writes on this path. Fixed queues expose
backpressure before emission. Queue full rejects the proposed generation and
leaves the prior valid frame published.

## 6. Cache and invalidation strategy

Caches accelerate evidence production but never change authority.

| Cache | Key | Invalidated by | Forbidden reuse |
|---|---|---|---|
| Compiler build | exact source, compiler parent, target/config, dependency/toolchain/environment hashes | Any key change or schema change | Different host environment or unresolved identity |
| Tool/MCP/LSP check | binary/source/config/fixture/checker hashes | Any input change, freshness expiry | Hot request handler full-tree discovery |
| Platform image | admitted compiler receipt, source/config, payload manifest, base image/toolchain hashes | Any payload/manifest/base identity change | Another row or run nonce |
| DrawIR plan metadata | layout/profile version and immutable scene-shape identity | Semantic/layout revision, capacity/profile change | Across arena generations without identity validation |
| Render resources | backend/device/resource revision | Device loss, generation/resource revision, backend change | As durable Draw IR contents |
| Evidence matrix | all child receipt hashes and policy/schema/reviewer inputs | Any child or policy change, freshness deadline | As a “last green” release decision |

Invalidation is event/key driven. File modification time alone is never an
identity. Stale reports remain visible but are rejected; regeneration creates new
content-addressed receipts rather than mutating historical evidence.

## 7. Performance and resource budgets

Detail design records numeric budgets per certified profile before evidence is
accepted. Architecture requires these dimensions:

- warm CLI startup, MCP startup/request p95, LSP startup/request p95, and max RSS;
- compiler clean-build duration/RSS and emitted-fixture duration;
- per-gate timeout, bounded capture bytes, runtime-pool width, queue depth, and
  maximum in-flight subprocesses;
- DrawIR command/glyph/image/byte capacity, frame queue depth, in-flight
  generations, peak RSS, p95/p99 latency, and worst-case deadline;
- allocation hard quota, nominal stress high-water (at most 80%), rejection
  latency, rollback duration, and isolation result; and
- 24-hour bounded-resource stress receipt for every selected platform row.

A regression beyond the design budget blocks admission. Raising a budget changes
the profile/configuration hash and requires fresh evidence and review. Adaptive
growth during an admitted run is not a budget mechanism.

## 8. Observability and evidence integrity

Receipts record exact binary/source/configuration/profile hashes, host and guest
identity, monotonic run/generation IDs, wall-clock timestamps, command identity,
timeout, exit status, bounded-output artifact hashes, and artifact paths. Secrets
and credentials are excluded from both canonical receipts and diagnostic capture.

Rendering evidence additionally records:

- scene/generation/arena identity and overflow/rejection receipts;
- actual backend, adapter, physical device, driver, queue, submit, fence, and
  readback provenance where applicable;
- structured input dispatch, target, semantic state transition, and resulting
  pixels for HTML-backed UI; and
- valid RenderDoc capture identity/metadata for claims that require it.

Screenshots without interaction/provenance do not pass. CPU/device equality must
use exact readback where claimed; labels or synthetic handles do not substitute.
High-water/overflow telemetry is diagnostic evidence, not a synchronization or
publication channel.

## 9. Failure containment

- Checked arithmetic precedes every arena offset/capacity computation.
- Exhaustion and queue saturation reject before publication; no truncation or
  fallback changes semantics.
- An inactive generation is the rollback unit. The prior sealed generation stays
  readable until consumers release it.
- Domain arenas have independent quotas and owners; one domain cannot mutate or
  reclaim another domain's storage.
- Storage commit and ownership publication are strict contexts, never relaxed.
- Guest row failures remain local to that row and preserve artifacts for audit.
- Tool crashes/timeouts become typed rejected/blocked receipts. They cannot be
  interpreted as skipped success.
- Invalid provenance or receipt parsing invalidates the applicable claim even if
  the underlying operation appeared successful.

## 10. Requirement traceability

| Requirement | Architectural evidence owner |
|---|---|
| REQ-MCI-001, NFR-MCI-002 | `CompilerAdmissionReceiptV1` and compiler admission capsule |
| REQ-MCI-002, REQ-MCI-010, NFR-MCI-001/003/009 | `HardeningEvidenceMatrix` and aggregate admission capsule |
| REQ-MCI-003/004, NFR-MCI-008 | `CertifiedPlatformManifestV1` and SimpleOS platform capsule |
| REQ-MCI-005/006, NFR-MCI-006 | Packed DrawIR-v3 arena, Engine2D provenance/readback receipts |
| REQ-MCI-007/008, NFR-MCI-004/005 | `RelaxedAllocationProfileV1`, per-domain arena receipts, fault injection |
| REQ-MCI-009 | `nogc_sync_mut.mission_critical.bounded_process_policy`: generation-bound slot reservations; opaque owner leases binding run/execution/start identity, PID, PGID, and slot token; sequenced termination/reap states; checked incremental capture receipts. Unit controls reject stale races, replay, PID reuse, forged groups, last-slot competition, and chunk overflow. The native owned-process provider now supplies a mutex-synchronized fixed-slot registry, PID/start-identity binding, bounded capture, and `fork`/process-group/pidfd signal/registered-reap integration through the canonical facade ABI. **BLOCKED release evidence:** the Simple facade is synchronous and exposes no public cancel/terminate operation, the interpreter deliberately fails closed, and no admitted exact-current native Simple receipt yet proves the source-matched deployed ABI. |
| REQ-MCI-011 | Matrix requirement rows, executable SSpec evidence, operator flow |
| NFR-MCI-007 | Profile-specific CLI/MCP/LSP performance receipts |

## 11. Implementation sequence and compatibility

1. Land common V1 contracts, strict parsers, canonical serialization, hashes, and
   negative-control tests without changing runtime policy.
2. Implement compiler admission and aggregate existing tooling receipts. Do not
   admit releases until exact-current pure-Simple evidence passes.
3. Implement manifest-owned SimpleOS row and payload receipts; retain all 24
   visible rows and narrow claims to selected PASS rows.
4. Introduce packed DrawIR-v3 behind a typed v2-to-v3 compatibility adapter,
   migrate GUI/Web/WM count/write producers, then make Engine2D consume sealed v3
   generations. The adapter is transitional and must obey the same admission cap;
   it may not allocate a parallel display list.
5. Introduce strict allocation contexts, then opt named domains into
   `RelaxedAllocationProfileV1` only after quota, rollback, telemetry, and
   fault-injection evidence exists.
6. Make `HardeningEvidenceMatrix` the release gate only after negative controls
   prove stale, unknown, unavailable, forged, timed-out, and overflow cases fail.

Schema evolution creates V2 contracts and explicit converters; it never silently
widens V1 meaning. Existing evidence may be imported as historical diagnostics
but cannot PASS unless it satisfies the new identity and freshness contract.

## 12. Rejected shortcuts

- Treating the Rust seed or hybrid compiler as production because it bootstraps.
- Accepting successful parse/build without executing emitted artifacts.
- Certifying SimpleOS from host-side files, source inspection, or an uncorrelated
  serial log.
- Hiding unselected/unavailable platform cells or calling selected rows “all
  platforms.”
- Allocating or growing Draw IR arrays while an active generation is built.
- Placing transient font atlas/cache/backend handles in Draw IR.
- A global “relaxed allocation enabled” switch, domain borrowing, or malloc
  fallback on arena exhaustion.
- Relaxed atomics for ownership/publication under the allocation profile.
- Treating screenshots, labels, synthetic device handles, or stale RenderDoc
  files as rendering provenance.
- Reusing a cached PASS after source/configuration/toolchain/profile/freshness
  inputs change.
- Repeating full-tree scans or unbounded subprocess capture in startup or hot
  request paths.

## 13. Review and ownership

Parallel implementation lanes may own compiler admission, SimpleOS manifests,
packed rendering, and allocation/runtime independently only after adopting the
five contract names and invariants in this document. The aggregate matrix owner
is the merge owner. Sidecar-generated broad findings or evidence require review
by a normal/highest-capability reviewer; that reviewer identity is part of the
matrix. Architectural or profile changes that widen a claim require the same
review and fresh evidence.

## References

## Implementation delta — 2026-08-11 correction wave

Static adversarial review tightened the initial contracts without changing the
selected architecture:

- `CompilerAdmissionReceiptV1` is realized through the shared `Mci*V1/V2`
  values as a versioned collector receipt bound to run/source/config/toolchain/
  dependency/environment/input-bundle hashes, resolved executable identity,
  pure-Simple parent lineage, and a complete ordered fixture manifest. Caller
  booleans and aggregate function counts are not admission evidence.
- `CertifiedSimpleOsManifestV1` validates exact equality with the canonical
  `linux|windows|macos|freebsd × x86_32|x86_64|arm32|arm64|riscv32|riscv64`
  catalog. Structural validity, scoped claim admission, and umbrella admission
  are separate. Every selected receipt is release/compiler/run/hash/freshness
  correlated. Serialization schema 2 additionally hash-binds the canonical
  host identity in both the row and every target receipt; schema 1 is rejected.
  The `*V1` Simple type/function names remain source-compatibility names only;
  they do not identify the accepted wire schema. Receipt time checks compare
  ordering before subtraction, then enforce both age and capture-to-expiry
  lifetime at no more than 86,400 seconds.
- `DrawIrGenerationPlanV3` carries arena, generation, packed-layout identity,
  row width, counts, and totals. Admission recomputes totals and refuses forged
  plans. Failed seal requires explicit abort; terminal generation exhaustion
  refuses rather than wrapping.
- `DomainArenaV1` separates committed and staging generations. Checkpoints are
  bound to arena/domain and the active transaction; nested calls preserve the
  original rollback point. Rolling back staging preserves the prior committed
  generation and invalidates staging references.
- `HardeningEvidenceMatrix` is implemented as a deterministic required-order
  fold with explicit blockers for missing, duplicate, unexpected, stale,
  skipped, failed, wrong-run/source/configuration, and malformed-hash receipts.


- `doc/01_research/local/mission_critical_infra_hardening_v2.md`
- `doc/01_research/domain/mission_critical_infra_hardening_v2.md`
- `doc/02_requirements/feature/mission_critical_infra_hardening_v2.md`
- `doc/02_requirements/nfr/mission_critical_infra_hardening_v2.md`
- `src/lib/common/ui/draw_ir.spl`
- `src/lib/gc_async_mut/gpu/engine2d/`
- `src/os/sosix/qemu_evidence/matrix_contract.spl`
- `scripts/check/check-compiler-provenance.shs`
- `scripts/check/check-simpleos-hardening-evidence-matrix.shs`

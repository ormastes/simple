<!-- codex-design -->

# Environment-Optimized Dynamic Libraries — Detail Design

## Status and scope

**Selected pilot: Feature A + NFR N2 + target registry B + inspector input 1.** This design describes
interfaces and algorithms for implementation planning. None of the named V1
contracts, CLI examples, performance targets, parser providers, or GPU paths is
claimed complete until focused evidence passes. There is no new UI; explain output is a CLI/protocol concern.

## Contract placement

| Contract | Proposed owner | Consumers |
|---|---|---|
| `EnvironmentSnapshotV1` | common composition schema plus platform probe adapters | admission, JIT/AOT target projection, explain |
| `VariantDescriptorV1` | common composition schema/codec | catalogs, native/SMF/JIT/static adapters |
| `BindingPlanV1` | composition admission owner | frontend/codegen/compute/render/scene sessions |
| `FrontendFacetV1` | shared frontend contract module | compiler, interpreter, REPL, SDN, sosh adapters |

Keep records bounded and ABI-safe: fixed-width scalars, flags, digests, and
offset/count references into immutable arenas. Do not expose `text`, collections,
trait objects, AST/HIR layouts, allocator-owned pointers, or closures across an
independently loaded boundary.

## Data model

`EnvironmentSnapshotV1` contains snapshot ID/generation; execution triple and
ABI facts; hardware, OS-usable, and policy-allowed feature sets; execution-domain
ID; vector-state mode/length; loader permissions; and bounded GPU-device records.
Feature sets use generated stable IDs grouped by architecture, never a total
cross-architecture rank.

`VariantDescriptorV1` contains descriptor size/version; provider and variant
digests; contract ID/version and ABI digest; semantic/grammar/program digests;
placement and artifact identity/location; exact CPU/OS/device predicates;
effects, memory domains, limits, dependency ranges, numerical contract,
assurance receipt, and declared startup budget.

`BindingPlanV1` contains plan digest; environment/catalog/policy generations;
dependency-lock digest; pinned provider generations; dense typed facet slots;
selected variant IDs; and bounded rejection records. It is immutable after
publication.

`FrontendFacetV1` operations are:

```text
create_session(dialect, grammar_digest, source_snapshot, budget)
plan_regions(session, request, output_arena)
execute_batch(session, first_region, region_count, output_reservation)
inspect_receipt(session, operation_id, receipt_arena)
release_session(session)
```

Each returns a status/reason code and generation-qualified handles. Output is
count/scan/reserve/emit into disjoint ranges, then validation and atomic semantic
commit.

## Algorithms

### Environment acquisition

1. Read product-baseline-safe platform facts through the canonical probe owner.
2. Intersect hardware features with OS-usable state and administrator policy.
3. Establish a common allowed CPU set or a pinned execution domain.
4. Record scalable vector state/length constraints and enabled GPU features.
5. Seal and hash the immutable snapshot; unknown data remains unavailable.

No `/proc` parser or feature string alone is admission authority. Snapshot
refresh is explicit on affinity, device, policy, or vector-state changes.
Hosted Linux now provides the narrow affinity operation required by step 3 and
the Simple driver records native thread identity, selected CPU, independent
lease generation, environment/domain identities, and live/release state.
Invocation still returns a typed unsupported/stability error until capability
validation and the native call are joined under that live lease. A later schema
version adds the full CPU-set digest and independently owned snapshot-domain
generation; non-Linux adapters remain explicitly unsupported.

### Catalog admission

1. Decode with maximum record, string-arena, dependency-depth, and total-byte
   limits.
2. Reject duplicates, corrupt offsets, overflow, unknown required fields,
   impossible feature combinations, invalid paths/digests, and ABI mismatch.
3. Resolve dependency closure to immutable artifact identities.
4. Evaluate exact eligibility; collect stable rejection reason codes.
5. Rank only eligible candidates using request semantics and calibrated policy.
6. Inspect inert native metadata before mapping; then query typed descriptors.
7. Activate a generation and publish one immutable `BindingPlanV1`.

Selection is deterministic for identical snapshot, catalog, policy, request, and
calibration evidence.

### Hot invocation

At session creation, acquire one plan/generation pin and copy the dense facet
slot into the session. A batch invokes that slot directly. No hot call reparses
configuration, walks the catalog, probes hardware, opens a library, looks up a
symbol, spawns a process, benchmarks, or takes the lifecycle publication gate.

### Parser execution

The first adapter wraps the legacy frontend and preserves parse reset/append/
isolated semantics plus interpolation and placeholder transformations. The
canonical runtime then qualifies scalar behavior per dialect. SIMD executors
vectorize encoding, lexical masks, structural indexes, token compaction, and
independent-region work with safe tails/guard pages. Unsupported regions emit
typed CPU work tags. GPU execution stages private output and emits actual device
completion evidence before commit.

### JIT/AOT/native artifacts

Generated-code requests take `TargetCodegenProfile`, never the host parser
snapshot by implication. Legalization records requested and backend-accepted
features. Packaging verifies facade/initializer and transitive dependency ISA
boundaries. Artifact receipts separately report declared requirements, emitted
vector evidence, selected implementation, and executed implementation.

### GPU islands

The planner considers admitted node costs plus upload, synchronization,
readback, and ownership-transition edges. It chooses a resident island, not the
locally fastest provider per stage. The GPU service owns device/queue/program/
fence facts; Object VM/memory owners hold leases; SimpleRing carries bounded
async request/completion. Rendering-required profiles may not silently run scene
semantics on CPU.

## State and lifetime

```text
discovered -> metadata_validated -> eligible -> mapped -> callable
 -> self_checked -> active -> draining -> retired
```

Only the lifecycle owner changes state. Failed transitions retain the active
generation. Pins cover sessions, JIT direct references, callbacks, submitted
device work, buffers, pipelines, and completion records. New-session cutover is
the default; state migration needs a separately versioned schema.

## Error model

Errors carry phase, stable reason code, provider/variant identity when known,
environment/catalog generation, and safe diagnostic text. Required selection
fails explicitly. Prefer/auto may fallback only before semantic commit and must
record the rejected candidate. Malformed output, stale generation handles,
device loss, mismatched receipts, and timeout/budget exhaustion do not publish
partial semantic state.

## Configuration projection

Hardware/OS/trust restrictions are non-overridable. Within them: invocation API
or CLI > permitted process environment > project > user > administrator defaults
> built-in auto policy. Administrator restrictions intersect all levels.
Configuration parsing rejects unknown tiers and cross-architecture requests.
Selected `prefer`, `require`, and `max` semantics follow REQ-005; concrete CLI
and environment spellings remain proposed until their product surface is implemented.

## Explain and observability

Admission receipts report request, selected candidate, selection phase,
identities/generations, reason codes, usable features, target-codegen profile,
and whether GPU was initialized. Execution receipts add actual implementation,
work counts, input/output digests, fallback tags, timings, transfer bytes, and
completion evidence.

Counters/timers include catalog decode, eligibility candidates/rejections,
binding publication, cold/warm load, session pin lifetime, dispatch calls,
parser stages, cache hit/miss/invalidation, GPU initialization/submission/fence,
transfers, and quarantine. Debug explainability is cold-path only.

## Cache design

- semantic cache keys exclude backend identity only after equivalence
  certification, while provenance remains attached;
- artifact caches include source/IR, compiler/backend, exact target, ABI,
  optimization/numerics, and dependency locks;
- device/pipeline caches include resource layouts and compatible device/driver
  identity;
- selection evidence can rank but never admit a candidate;
- generation changes invalidate binding plans, not unrelated semantic results.

No request performs a full-tree scan or repeated artifact read. Startup uses an
installed bounded catalog/index; maintenance commands rebuild it explicitly.

## Performance and capacity design

Candidate caps, dependency depth, catalog bytes, pending loads, sessions,
outstanding operations, queues, and device allocations are configuration-bound.
Measure CPU-only cold/warm startup, representative request latency, p95/p99,
max RSS/mapped text, allocations, dispatch overhead, parser throughput, and
artifact size. GPU evidence additionally includes initialization/pipeline cost,
queue time, transfers, synchronization, CPU service time, and frame latency.

Selected NFR N2 targets are defined in
`doc/02_requirements/nfr/environment_optimized_dynamic_libraries.md`; baseline
measurement and qualified evidence remain missing. Earlier provisional targets
in the architecture are hypotheses only where they differ from NFR-001..010.

## System-test contract for later implementation

The architecture lead freezes these helper names before sidecar test work:

- `setup_environment_catalog(...)`
- `step_admit_variant(...)`
- `step_bind_provider(...)`
- `check_execution_receipt(...)`
- `setup_canonical_target_registry(...)`
- `step_start_atomic_inspector(...)`
- `check_atomic_inspector_terminal(...)`

Scenario step text should expose the operator flow: inspect environment, admit
compatible artifacts, bind the requested provider, execute a representative
batch, and verify actual execution evidence. Any unimplemented helper must call
`fail("environment optimized provider helper not implemented")`; placeholder
passes and `expect(true).to_equal(true)` are forbidden.

REQ-001..016 and NFR-001..010 are traced by the fail-fast system scaffold and
focused Stage-1/2 unit specs; all system evidence remains red/pending.
NFR-011 and NFR-012 have no executable scenario yet and must be added as
explicit fail-fast SSpec cases before implementation handoff. REQ-015
requires live-token consumption by target-profile, cache, binding-plan, and
receipt owners, not merely a registry lookup unit test. REQ-016 requires the
production Simple opaque V3 adapter to prove exact input/close/drain/reap
authority, not merely the runtime C self-check. Planned groups cover classification/OS state, catalog corruption,
override semantics, native/SMF parity, parser facade and differential behavior,
JIT/AOT host-target separation, lifetime/failure injection, truthful GPU/fence
evidence, rendering fallback, and measured performance envelopes.

## Security and safety review

- validate immutable artifact bytes and dependency closure before native load;
- use controlled loader search and no working-directory dependency substitution;
- contain untrusted native providers in a worker process;
- never grant arbitrary host pointers to device programs;
- validate arena bounds/alignment/generation and integer arithmetic;
- keep observer permissions distinct from semantic replacement;
- never use illegal-instruction trapping as the normal feature detector.

## Compatibility and migration

Versioned adapters preserve current provider query/generation entrypoints,
legacy frontend behavior, `SIMPLE_CPU_FEATURES` generated-target meaning, native
GPU registry ownership, SMF release identity, and packed DrawIR paths. New
strict requests fail when a backend treats requested features as no-ops. Removal
of rank-based tier authority and filename-driven loading occurs only after all
production callers migrate and structural gates cover them.

## Open design decisions

Implementation planning must still name the first qualified host/tier fixture,
trust-root mechanism, initial parser parity boundary, and whether a native
generated-library pilot accompanies the parser pilot. Feature A and NFR N2 are selected.

## GPU completion bridge refinement

Environment admission and Engine2D execution receipts remain separate records.
The adapter correlates them at a cold lifecycle boundary using an explicit
provider-completion authority containing queue/backend handles, queue/operation
generations, and submission/fence/completion/retirement identities. Provider,
program image, device, layout, and lease identities remain typed inputs; none
are packed into a generic integer handle.

Lifecycle mapping is exact:

```text
Engine2D gpu_finished -> variant fence_signaled
Engine2D completed    -> variant completed
Engine2D retired      -> variant retired
```

Only the final mapping satisfies the generic final-state validator. Earlier
states are valid bridge outputs but deliberately report the next missing fact.
The bridge cannot be invoked by the compatibility queue until a real backend
supplies qualifying device timestamps, negative-control evidence, and stable
provider tokens. This preserves current routing-only behavior.

## Parser SIMD artifact qualification refinement

Parser SIMD promotion consumes three distinct identities:

- the build-plan artifact identity selects the planned parser sibling;
- the emitted artifact digest identifies the inspected executable bytes;
- the selected/executed implementation identity proves the invoked provider.

The inspection receipt must name its tool and evidence digest and report a
nonzero observed vector-instruction count for a SIMD implementation. Generic
target flags or a nonzero generic instruction count are insufficient. The
scalar reference must have no requested/executed SIMD feature and no observed
vector instruction.

Current source evidence narrows the first real codegen pilot to the admitted
x86 AVX2 `f32x8` lowering path. AVX-512 and broad auto-vectorization remain
scaffolded and cannot be promoted. This codegen proof is separate from parser
semantic promotion, which still requires normalized legacy-versus-canonical
dialect parity.

The AVX2 proof join is deliberately three-layered: encoder golden evidence,
inspection of the exact emitted object bytes, and execution of that same
artifact in an OS-usable AVX2 domain with scalar-oracle equality. Passing a
pure join validator only establishes that supplied receipts are mutually
consistent. Promotion additionally requires the producer-side object inspector
and callable harness; synthetic unit fixtures are never execution evidence.

### External object-inspection owner

The production inspection owner consumes a live `BytesSealed` token, never a
path. It owns one admitted LLVM tool bundle (`llvm-readobj` plus
`llvm-objdump`) with exact executable/version digests and one bounded input
transport. Prefer an owned stdin-capable process lease; a temporary-file adapter
is allowed only when it creates a private file, writes and rehashes the retained
bytes, never exposes the path as authority, and deletes it before terminal
release.

```text
BytesSealed use
  -> acquire tool generation + bounded process/input lease
  -> llvm-readobj structured headers/sections/groups/symbols/relocations
  -> normalize and validate complete executable-section closure
  -> llvm-objdump raw-byte disassembly for matching section/address rows
  -> reject gaps, overlaps, unknown instructions, or byte mismatch
  -> publish immutable InspectionToken
  -> release process/input/tool uses in reverse order
```

`InspectionProjectionV2` binds artifact and BytesSealed authority, tool bundle
and generation, exact argv/schema version, target/object identity, executable
sections, relocation/symbol closure digest, decoded instruction rows, observed
required-feature set, unknown-instruction count, bounded output digests, and
cleanup state. SIMD promotion requires zero unknown instructions and at least
one instruction in the exact requested parser SIMD family. This is not
execution proof.

Readobj JSON and objdump text use separate versioned fail-closed codecs; no
line-number join is permitted. Correlation uses section identity, byte offset
or address, and exact raw bytes. Caps cover input, rows, output, wall time, and
concurrent tools. Tool disappearance, timeout, nonzero exit, truncation, schema
drift, duplicate rows, or cleanup failure leaves a non-projectable record.

The preferred live provider extends runtime-owned process V2 additively rather
than using raw PID-based piped calls. Its lifecycle is `Prepared → Spawned →
FeedingAndDraining → StdinClosed → Running/Terminating → Reaped → Collected`.
The runtime preflights memory and slots, uses three nonblocking pipes, closes
stdin on every terminal path, drains while partially writing, and retains
cleanup-pending state if termination or reap cannot complete. Output overflow,
partial input, EPIPE, timeout, cancellation, read/write error, identity drift,
or unreaped child makes inspection unavailable.

Tool authority binds immutable executable digest/generation, version digest,
fixed argv-template digest, and deterministic environment. PATH lookup, shell
execution, response files, plugins, caller working directories, and ambient
LLVM configuration are rejected. Prefer a verified executable descriptor or
platform-equivalent image authority; path revalidation alone remains TOCTOU.

The checked-in V1 normalized contract is the shared policy layer beneath either
input-provider choice. It requires terminal collected tool facts, complete
gap-free instruction coverage for each executable section, all-object section
identity for relocation targets, recognized instructions, exact requested to
observed SIMD support, bounded rows/output, and one canonical digest. It is not
an issuer: caller-constructed terminal or decoded rows cannot authorize
inspection until a registered process/tool owner supplies them.

The first checked-in readobj codec uses the canonical pure-Simple JSON parser
and validates exact executable section bytes. It intentionally stops before
symbols/groups/relocations; later codec versions extend the typed projection
without treating successful JSON parsing or a caller-provided `<stdin>` label
as tool provenance.

The relocation codec never treats LLVM's relocation-group `SectionIndex` as
the code section. It resolves the relocation section header first: `sh_info`
identifies the patched section and `sh_link` the unique symbol table. Symbol
indices, names, declared sections, addends, ordering, and section-relative
ranges are validated before rows reach the normalized inspection contract.

Do not consume LLVM's `Groups` JSON object: current multi-COMDAT output repeats
the `Group` key, so ordinary JSON parsing loses all but one group. Decode each
`SHT_GROUP` section's exact `SectionData` instead. Bind its declared size,
little-endian flag/member words, unique symbol-table link, signature-symbol
index/name, member ranges, and cross-group executable membership.

## Scalar parser promotion receipt

Scalar promotion is a corpus result, not a single matching parser call. Every
row binds source snapshot and generation, dialect, grammar, actions, schema,
semantic profile, and independent legacy/canonical implementation generations.
Normalized token, span, node, and diagnostic digests are compared separately;
the receipt hashes all four components. Total and covered region counts must be
nonzero and equal, with zero unsupported regions. Partial coverage cannot yield
a default-promotable receipt.

The existing structural runtime hash is useful only as a lexical component: it
is a deterministic 32-bit summary and does not identify a full AST/HIR. Simple,
SDN, and sosh need dialect-specific normalization adapters once immutable full
result APIs exist. Until then the qualifier validates supplied evidence but no
production parser is promoted.

## CPU-only startup isolation receipt

Help and version may observe an inert catalog but must map/select no provider,
initialize neither GPU registry nor device, and perform no application or
provider compilation. Reference compilation may map exactly one identified CPU
provider and perform exactly one requested application compilation; it still
must perform zero optional-provider compilations. This distinction prevents the
requested compile from being mislabeled as forbidden hidden startup work.

The receipt records invocation and optional catalog identity, mapped-provider
count, application and provider compilation counts, GPU registry/device facts,
and selected CPU provider generation. A pure qualifier over supplied counters
does not prove startup isolation; production command instrumentation must
produce those counters without itself initializing optional GPU services.

## Pure configuration resolver

The product adapters pass text from CLI, process environment, project, and user
configuration into one pure resolver. Ordinary precedence is CLI, environment,
project, user, then default. Administrator inputs are restrictions applied
after parsing and cannot be widened by an ordinary layer.

Parser preference, parser requirement, host CPU maximum, frontend offload, and
fallback remain distinct typed fields. Effective-source provenance changes to
`admin` whenever a restriction changes a value. The policy digest includes
requested/effective values, the offload-auto bit, all exact administrator
restrictions, and effective sources. Generated target-codegen features are not
inputs to this host-execution policy.

The catalog projection requires an explicit registry authority mapping abstract
`scalar`/`simd` choices to exact provider and variant identities and mapping CPU
presets to feature-set ranges for the execution architecture. It produces a
mandatory cap stage followed by preference or requirement selection. These
must be consumed atomically: applying only the legacy catalog's singular MAX
mode drops preference, while applying only PREFER/REQUIRE drops the ceiling.
The next composition change is a composite selector that filters all candidates
through hard caps before ranking the retained set.

### Native-build parent-to-worker policy handoff

The native-build parent is the sole ambient source owner. It snapshots CLI and
environment inputs once, reads project `simple.sdn`, and reads the explicitly
new feature-specific user source `~/.config/simple/config.sdn`. The latter is
not an alias for `~/.config/itf/config.sdn` and is not reconstructed from a
merged `CompilerConfig`. Both files use bounded regular no-follow reads.

The parent resolves the collected layers, serializes the raw normalized layers
plus generated target CPU/features into a fixed-order bounded V1 wire, and
appends exactly one internal base64url argv value. Parse shards, HIR shards, and
the real worker receive the same value. The worker rejects a missing,
duplicate, corrupt, noncanonical, or oversized value and removes only that
internal argument before invoking native-build; public target flags retain
their exact bytes and order. Policy is not transported by rewriting process
environment variables.

The wire integrity digest detects mutation but conveys no administrator
authority. Until an authenticated administrator source owner is introduced,
the production application owner supplies empty administrator restrictions.
The warm artifact key includes the handoff cache identity, which binds resolved
policy digest and the separate generated target CPU/feature inputs.

This E1 slice is transport-only. Both full and parse-shard worker entrypoints
validate/remove the handoff, and legacy argv parsing accepts the preserved
public policy spellings without applying them. E3 must consume the typed
handoff in every relevant driver path before this transport candidate can be
admitted; standalone E1 integration is not production-safe.

## Prepare/commit coordinator for composite publication

The first production-consumer seam after composite selection is a new adjacent
compiler coordinator. It must not modify the existing catalog, publication, or
binding-runtime owners. Use two phases so policy and artifact checks are pure
and runtime mutation remains parent-authoritative.

The preparation result is `EnvironmentVariantPrepareBundleV1` with these exact
fields:

- `decision`: `EnvironmentVariantPolicyDecisionInputV1` (including requested/effective values, source provenance, explanation, and text `policy_digest`).
- `projection`: `EnvironmentVariantCatalogPolicyProjectionV1` (separate MAX cap and PREFER/REQUIRE selection requests, frontend mode/fallback, and binary `binding_policy_digest`).
- `composite`: `EnvironmentVariantCompositeSelectionV1` (selected index/identities, closure, catalog/lock identities, fallback flag, and bounded rejection rows).
- `publication`: `EnvironmentCompositePublicationV1` and its `BindingPlanV1`.
- `selected_variant_identities`: identities ordered positionally with the facet
  bindings. Dependency membership remains represented by the independently
  validated closure digest and admitted-artifact evidence; dependencies that
  expose no facet are not invented as binding-runtime selections.
- `rejections`: the exact ordered composite rejection rows.
- `bindings`: ordered `VariantFacetBindingV1` values used to create the plan.
- `dependency_closure_digest`, `catalog_generation`, `dependency_lock_digest`, `publication_plan_digest`, and both policy digests.

`environment_variant_prepare_v1(inputs, authority, snapshot, arena_bytes,
feature_words, gpu_devices, root, descriptors, dependencies, resolution,
artifact_evidence, catalog_generation, publication_generation, bindings)` calls
the existing pure resolver, projection, composite publication wrapper, and
returns this bundle. `environment_variant_commit_v1(bundle, runtime, manager,
provider_handles)` is the only phase allowed to call
`binding_runtime_publish_plan_v1`; it returns the existing
`BindingRuntimeReceiptV1`.

Preparation resolves the policy layers exactly once. Feature-ceiling ranges in
the projection refer to the same feature-word arena used to derive the
canonical catalog digest; callers must not substitute another arena between
projection and publication. The returned bundle copies repeated sidecars so
mutating a convenience view cannot silently mutate the nested canonical
publication view.

Preparation validation is ordered and fail-closed:

1. Validate resolver schema, policy text digest, and binary digest equality.
2. Validate projection authority and that MAX and selection requests share provider and architecture authority.
3. Reject required-missing selection; correlate selected root/provider/variant, closure, catalog generation, and lock digest.
4. Validate publication schema/plan and authenticated artifact evidence; correlate plan policy, closure, catalog, lock, and publication generation.
5. Require selected identities and rejection rows to match the composite result exactly; validate facet order, provider generations, and bounded counts.
6. In commit, require `provider_handles.len() == bindings.len()` and let the runtime owner perform its final generation/plan check before mutation.

Focused tests should cover: successful preferred fallback with retained cap
rejections; required selection rejected before runtime mutation; policy digest,
closure, catalog-generation, and lock mismatches; dropped/rewritten rejection
rows; selected-identity or facet-order mismatch; handle-count mismatch; stale
provider generation; and deterministic repeated preparation. These tests can
use existing fixtures and do not require public-facade changes or ABI changes
to `BindingPlanV1`, `EnvironmentPublicationAdmissionV1`, or runtime receipts.

Lifecycle receipt migration is additive. Keep the legacy library bridge for
its current root-only shape and add a compiler-side composite-aware adapter.
The adapter validates the publication's copied binding, selected-identity, and
rejection sidecars with the binding-plan contract, validates every admitted
artifact and the exact root receipt identity, then invokes the value-only
eligible/mapped lifecycle transitions. It must not equate dependency artifact
count with selected facet count. Policy explanation and closure evidence remain
in the composite publication/coordinator bundle because the V1 lifecycle
receipt has no fields for them.

### Parser SIMD kernel dependency sequence

The first real parser kernel is a block byte classifier, not a full grammar
executor. Its input is an immutable byte slice plus an explicit complete-block
range. Its output is typed per-block masks for the exact structural byte set
consumed by the lexer/region planner. A separate scalar tail handles bytes
outside complete blocks and must never read beyond the source allocation.

Implementation acceptance is ordered:

1. Pure-Simple byte-vector operations lower to actual target instructions;
   `f32x8` encoder goldens do not satisfy this condition.
2. Object inspection binds emitted instructions to the artifact identity.
3. Execution evidence binds the admitted provider and qualified host; an ISA
   request or successful compilation alone is insufficient.
4. Every block alignment and tail length matches the scalar mask and complete
   parser token/span/diagnostic digest.
5. The accelerated executor is callable through the structural parse runtime
   provider seam. A standalone benchmark/proof helper is not product wiring.

Current ceiling: the dedicated pure-Simple x86 encoder emits and QEMU-executes
the two-delimiter AVX2 callable, but main MIR/provider lowering and parser
runtime routing remain open. `runtime_simd_utf8.c` is real native SIMD but
would be a C FFI provider, not the requested pure-Simple implementation.

### Structural-mask provider session

The production session API must take an admitted callable lease, a source
buffer lease, two delimiter bytes, source length, and output capacity. It
returns deterministic block masks plus compact positions and a receipt binding
the callable artifact/generation, source snapshot, complete-block count, tail
count, and scalar-fallback reason. It never accepts an arbitrary function
pointer or unleased host address.

Acceptance sequence:

1. False capability creates a scalar session and performs zero executable
   mappings.
2. An admitted SIMD session maps code once per provider generation and copies or
   registers source once per source lease; no allocation occurs per block.
3. Complete blocks invoke the two-delimiter callable and the final 0–31 bytes
   use the scalar oracle with overflow-safe bounds.
4. Tests cover zero length, every tail, block plus tail, duplicate delimiters,
   bytes above `0x7f`, exact positions, source immutability, map/call counts, and
   release-once behavior.
5. Parser runtime routing consumes this session through its admitted provider
   seam; standalone encoder or QEMU success is not runtime integration proof.

The current repository lacks the lower-layer W^X callable service and stable
buffer-lease interface required by steps 1–5. Importing compiler loader owners
from `std.nogc_async_mut.structural.parse` is prohibited.

Proposed opaque interfaces (schema notation, not implemented syntax):

```text
ExecutableKernelLeaseV1
  artifact_digest, provider_generation, callable_operation_id
  lease_generation, required_features, retirement_token

StableSourceBufferLeaseV1
  snapshot_identity, byte_count, memory_domain
  lease_generation, read_only_token, retirement_token

StructuralMaskSessionV1
  session_generation, kernel_lease, source_lease
  first_delimiter, second_delimiter, output_capacity

StructuralMaskBatchResultV1
  block_masks, positions, complete_block_count, tail_count
  source_unchanged_digest, execution_receipt
```

Only the loader/kernel-plugin owner creates `ExecutableKernelLeaseV1`; only the
memory/Object-VM owner creates `StableSourceBufferLeaseV1`; the structural
provider owns the session and deterministic output; the parser runtime owns
selection and fallback. Tokens are opaque and generation-checked, never native
addresses in the public contract.

## 2026-09-08 lexical summary detail addendum

<!-- codex-design -->
`lexical_block_summary_v1.spl` scans at most 32 bytes from an explicit boundary
state. It emits quote/escape/line-comment/newline/delimiter masks and the exact
next state. Compatible concrete summaries concatenate only after exact
boundary-state checking; this is sequential provenance, not independently
parallelizable transition composition. Boundary state carries pending
quote-run, raw-prefix, identifier, slash, and post-newline facts so split
introducers cannot evade fallback. Unsupported raw/triple/interpolation/custom
block/indentation/block-comment regions carry reason bits and force the legacy
lexer path. The scalar implementation is the comparison oracle for a later
SIMD lowering.

The independent-block form is `lexical_transition_table_v1.spl`: exactly 22
ordered input states, one output/provenance row per state, canonical SHA-256,
and bounded row/block validation. Composition selects the right-table row from
the left output state. Identity and associativity are therefore testable without
rescanning neighboring bytes; selecting the initial-state row must equal the
ordinary sequential scalar scan for every partition.

Verification separates unsealed computation from admission. `LexicalTransitionRowsV1`
has no digest or receipt authority and is used for exhaustive scalar differential
tests without repeated SHA work. Only `LexicalTransitionTableV1` is sealed with
a canonical digest; public sealed compose/select validate caller-supplied tables
and reject tampering. Unsealed rows must never enter provider admission, caches,
or execution receipts.

### AVX2 candidate-mask execution detail

`parser_lexical_avx2_classifier_v1.spl` defines the scalar mask record and the
exact x86-64 SysV one-byte equality primitive. For each complete block, the
provider batch constructs the nine published raw fields from independently
validated primitive results; derived brace/structural fields must equal their
canonical component unions. The batch rejects any tail, stale authorization,
ABI/layout mismatch, source mismatch, failed affinity revalidation, or changed
generation before commit. Tails and semantic transition selection remain
scalar. Receipts distinguish emitted bytes, admitted mapping, successful native
calls, and scalar transition resolution; none implies another.

### Parser variant build-plan detail

`ParserVariantBuildPlanV1` uses fixed-width little-endian identity material and
canonical artifact sorting, so request order and build-host changes do not alter
the planned artifacts. A target triple is diagnostic text bound by digest; the
validated `TargetCodegenProfileV1` supplies architecture, ABI, object format,
endianness, pointer width, strict features, backend, semantics, and numerical
authority. Native, SMF, and JIT siblings remain distinct placements. Every
artifact is marked `compilation_executed=false` until a later backend receipt
establishes actual compilation and emitted-feature evidence.

### Packed GPU completion acceptance

Accept completion only when epoch, provider generation, device image, device,
queue/session generation, packed content digest, buffer lease, fence, and
retirement receipt correlate. Reject stale epochs, cross-provider receipts,
replay, checksum mismatch, cancellation without true retirement, missing fence,
and compatibility fallback labeled as device execution. A positive test must
consume packed bytes on the device and correlate provider-issued completion;
route selection or successful queue admission alone is not execution proof.

### Frontend port acceptance

The driver adapter binds transformed source digest and length, dialect,
grammar/actions/semantic identities, input lexical state, exact block range,
policy, lexical ABI/mask schema/tail policy, sealed frontend binding, and
provider/environment generations. `PreferSimd` discards every partial native
result before typed scalar fallback. `RequireSimd` fails on admission,
capability, mapping, guarded-call, oracle, or cleanup failure. Executed receipts
remain classifier-only with `reference_frontend_required=true`; they do not
claim UTF-8, indentation, token, AST/HIR, recovery, or cache ownership.

The first adapter implementation lives at the loader boundary because it must
own package calls; layer 10 remains loader-free. It accepts owners rather than a
caller-constructed batch, acquires sealed authority, revalidates the package's
owner-derived session/source projection, processes only complete 32-byte blocks,
and releases the sealed use before returning copied evidence. Its V1 receipt is
not yet the final frontend receipt: add canonical mask/summary/input/output-state
digests, operation/session terminal identity, bounded historical ownership, and
behavioral equivalence before binding it into `parse_full_frontend_with_scope`.

The advisory request binds the transformed-source digest, dialect, grammar,
actions, semantic profile, session generation, and reference/prefer/require
policy. Its result contains only bounded candidate masks, fallback tags, and
an execution receipt. Acceptance compares no-provider and provider modes for
reset/append/isolation, conditional/domain transforms, interpolation and
placeholder order, streaming alias/promotion behavior, cache hit/miss output,
and help/version lazy startup. The canonical parse result must remain identical;
this port does not constitute parser replacement or parity promotion.
## 2026-09-08 backend callback bridge detail

`Engine2dBackendCompletionPortOwnerV1` provides the contract-level handoff:
register a nonzero adapter identity, record a typed backend callback, consume
the resulting opaque authority exactly once, and create packed submission,
completion, and retirement proofs under the existing proof owner. Unavailable
and fence-only states fail closed at final bridging. This API deliberately does
not accept an `executed` boolean, but it remains forgeable by whichever adapter
owns the port; tests therefore prove correlation/replay behavior only. The
Vulkan implementation must retain a native fence plus exact lease until
retirement and must supply all provider/session/image/device/epoch/content
joins before this result can qualify as device execution.

## 2026-09-08 cache generation authority detail

The generation owner exposes a cache-safe projection only while the exact V2
pin is live. The projection contains the public full-width provider, variant,
artifact, ABI, contract, semantic, grammar, program, plan, and environment
identities plus a canonical authority digest. That digest additionally commits
to the private mapped handle, callable binding, activation authority, pin ID,
provider handle, and generations; the raw mapped handle stays private. A cache
issuer must revalidate this projection immediately before namespace publication
and keep the pin through the cache lookup/materialization decision. The
projection is necessary generation provenance, not sufficient cache authority:
canonical publication/action joins and bounded unambiguous encoding remain
separate gates.

### Canonical cache material

Replace delimiter-concatenated cache material with the existing canonical
action-key codec or a fixed-width/length-prefixed byte encoder. Preflight text,
list, feature-word, artifact, and total-material caps before allocation or
hashing. CPU features are a sorted unique set whose normalized form must agree
with `BinaryObjectActionV1`. Known vectors cover embedded delimiters and Unicode,
feature reorder/duplication, every maximum and maximum-plus-one, each individual
field mutation, receipt/namespace domain separation, and deterministic
round-trip. This encoding gate precedes compiler-owned receipt issuance.

### Publication-owner gate

`EnvironmentCompositePublicationOwnerV1` accepts original admission inputs and
returns an opaque token after canonical admission. Projection is a copy for
inspection. Every authoritative consumer supplies the owner and token again;
revocation makes existing joins stale. V1 admits exactly one root facet binding
and correlates its generation with both admitted root evidence and the pinned
provider-generation authority. Compact `root_referenced_*` arrays are canonical
digest payloads; descriptor range offsets remain hashed catalog metadata and
must not be used to index those compact arrays.

### Build-plan owner gate

`EnvironmentVariantBuildPlanOwnerV1` owns the canonical plan plus copied
baseline and per-artifact feature arenas. Requests are bounded and strictly
ordered by the catalog's full-width digest order, preserving stable artifact
indices without hidden sorting. Emission receives owner, token, artifact index,
action, and actual bytes; raw plans and feature arrays are not accepted. Its
join remains non-authoritative for cache/JIT use until an authenticated backend
feature receipt and canonical target textual/numeric mapping are available.

### Backend feature receipt boundary

`BackendFeatureAuthorityV1` is the bounded declaration store, keyed by full
backend identity and known architecture. A backend adapter must add an
authenticated receipt containing provider/build, JIT-or-AOT mode, exact target,
toolchain/ISA-builder version, policy/config digest, normalized accepted words,
and backend evidence. Revocation invalidates dependent planning/emission
authority. Strict mode rejects documented no-op feature tokens rather than
recording them as accepted.

### Generation reservation protocol

`reserve(pre_publication_evidence)` allocates one manager-scoped reservation
per provider and counts pending plus resident generations against one bound.
Publication uses the reservation's exact generation in root evidence/binding.
`finalize(reservation, publication_plan_digest)` atomically creates that exact
generation and retires the prior active generation; `cancel` removes an
unpublished reservation. Foreign, pending, cancelled, and replayed reservations
cannot pin. Mapped-resource ownership and publication-token correlation remain
the compiler coordinator's responsibility above the generic manager.

The coordinator releases in dependency order: refuse while exact pins are
live, retire the exact finalized generation, release its child publication
token, then reclaim the coordinator record. Each completed cleanup step is
remembered so retry does not repeat an already-completed destructive action.
The next adapter issues coordinator-owned opaque pins; downstream build joins
must not regain direct access to child publication/generation owners.

### Sealed activation adapter

`environment_variant_collect_and_activate_v1(coordinator, pre, input)` performs
admin verification, collection, policy resolution/projection, and coordinator
activation exactly once. It copies selected/rejection and plan metadata into a
non-publication result. Any post-activation projection failure releases the
activation before returning `ActivationFailed`. The next version wraps this in
an aggregate owner so consumers cannot directly retain or release child state.

`EnvironmentVariantSealedActivationOwnerV1` implements that wrapper for
activation and pins. Its projection deliberately omits the child token and raw
publication. Release refuses aggregate pins, delegates coordinator cleanup,
then reclaims the record. Build joins must next register as aggregate leases;
copied pin projections are insufficient for lifetime authority.

Use `environment_publication_activation_pin_live_v1` when admitting a new pin
consumer or build join. Use `environment_publication_activation_pin_continuation_live_v1`
only to revalidate an already-recorded in-flight consumer while it drains. Pin
release addresses the exact handle and generation, never the current provider.

`environment_publication_activation_use_acquire_v1` records an opaque
activation+pin use only after active-pin validation. `use_live_v1` is the
continuation check and `use_release_v1` is one-shot cleanup. Build-join records
retain this token; their release API requires the coordinator so the lease is
released before local records disappear.

### Aggregate build-join authority

The next owner operation takes an aggregate activation token, retained planner
artifact authority, and emitted-byte/action authority. It performs all identity
checks before privately acquiring pin/use holds, stores an immutable canonical
projection, and returns only an aggregate join token. Liveness revalidates the
planner/emission owners and historical coordinator use. Release persists
use-then-pin cleanup progress. Compiler-plan and runtime-plan digests remain
separate fields and are never substituted for one another.

`environment_variant_sealed_build_use_acquire_v1` performs active-generation
admission, privately acquires child pin then child use, and returns an aggregate
token. The retained authority supports continuation liveness after replacement.
Release stores `use_released` and `pin_released` before reclaim. Extend its
projection with canonical publication correlation before wiring emission joins.

The projection includes root descriptor digest, catalog, closure, lock,
canonical-base, binding-policy and publication-generation fields alongside the
pin authority. Acquisition and liveness require exactly one matching
authenticated root evidence row, one selected root, and one generation-matched
root binding. Liveness reconstructs this projection from owner-held child state.

The build-use digest serializes little-endian fixed-width fields in documented
order, beginning with a domain/schema tag, and includes private child token IDs.
Direct join liveness additionally compares the planner plan, selected artifact
intent/cache identity, and generation-authority digest rather than relying on
successful projection alone.

`EnvironmentVariantBuildPlanUseTokenV1` binds a parent plan and artifact index.
Join records retain both planner and coordinator use tokens. Release stores two
progress flags: coordinator use is released first, then planner use, and local
join/emission records are removed only after both succeed. This makes partial
cleanup retryable without double-decrementing either owner.

`build_artifact_emission_issue_v1` acquires a planner use after input/capacity
validation and before receipt publication. `emission_live_v1` reprojects the
planner artifact and checks receipt identities. Unjoined release drops this
retain; joined cleanup releases coordinator use, join planner use, then
emission planner use before removing owner records.

### Frontend lexical advisory adapter

The loader-side lexical adapter is a deliberately non-semantic bridge. Reference
policy returns the original source without acquiring provider authority. SIMD
policy acquires an aggregate sealed frontend build-use, derives package session
and source authority from their owners, correlates the exact provider, variant,
artifact, generation, snapshot, source length, and source digest, then invokes
the authenticated structural lexical batch for complete 32-byte blocks only.
The incomplete tail remains explicitly scalar-owned. The adapter releases its
sealed use before publishing an unchanged-source receipt.

The receipt separates reference no-op, completed SIMD classification, and
scalar fallback. Its canonical batch digest commits all nine masks and every
input/output lexical summary field; its authority digest additionally commits
source/session/provider identities, block and native-call counts, tail bytes,
policy, admission/execution/fallback facts, the exact classifier ABI,
mask-schema and scalar-tail-policy identities, and the batch digest. The
session/source owner only projects those identities from exactly one valid
lexical authorization correlated with the active structural authorization.
A generic structural activation is therefore not accepted as a lexical
provider. These are
historical provenance after release, not a live capability. The adapter also
requires the execution snapshot identity and generation to match the sealed
admitted environment, binds a canonical digest of its complete feature arena
into the receipt, and relies on the package's live verifier for actual feature
usability. Before layer-10 wiring, qualify this owner-derived terminal evidence
under failure injection, then prove a positive SIMD path and exact frontend
equivalence.

For native lexical attempts, the package receipt carries its owner-issued
operation handle and a terminal-cleanup bit set only after the guarded scope,
live verifier, and affinity lease have all retired. The adapter requires and
cryptographically binds this pair whenever any native calls occurred. A
successful SIMD classification requires exactly fifteen mask calls per complete
block. A failed partial attempt can retain a positive strict-prefix call count
as historical evidence, but its status is scalar fallback and its masks are the
canonical scalar result.

Downstream publication calls
`frontend_lexical_advisory_adapter_result_valid_v1` on the complete result, not
on its receipt in isolation. The gate recomputes the unchanged-source identity,
source digest, block/tail coverage, every candidate-mask and lexical-summary
field, status/policy/execution relationships, terminal operation facts, and the
canonical authority digest. Passing this gate establishes internally consistent
historical advisory evidence; it still does not establish parser, AST, or HIR
equivalence.

Layer 10 owns the actual dependency-inversion seam: one typed function-valued
advisory slot, initialized to the lazy reference provider. Only a strictly newer
driver generation may bind a provider; reset cannot roll the generation back.
The dispatcher validates the common receipt and falls back to the reference
implementation if a bound provider returns inconsistent evidence. The shared
frontend invokes this dispatcher after conditional/domain transformations and
before cache lookup and full parsing. Driver and loader modules may bind down
through this port, while layer 10 imports neither of them.

The loader binding adapter owns the configured sealed activation, package
session, execution snapshot, feature arena, and initial lexical state. Its
function-valued projection invokes and validates the rich lexical result, then
issues the smaller canonical frontend receipt. The common receipt distinguishes
reference no-op, unavailable advisory execution, completed advisory execution,
and scalar fallback; its digest binds provider and GPU execution flags and
counts as well as status. Uninstall first restores the layer-10 reference slot,
then discards loader context. Startup composition must still supply and retire
this context, and required-policy failure needs an explicit compiler error path
before automatic selection is enabled.

Callers that enforce `RequireSimd` use checked dispatch. It returns typed
unavailable unless the validated common status is completed advisory execution,
and distinguishes malformed provider evidence. The compatibility dispatcher
may still fall back for reference/prefer callers. Automatic selection is gated
on proving that function-slot replacement changes the actual indirect target;
the slot is therefore stored in a stable reference-semantics object rather than
as a bare mutable global function value. A focused interpreter regression proves
that binding changes the actual indirect target and checked RequireSimd dispatch
observes valid executed evidence. This proves the frontend port mechanism, not
the loader provider or hardware execution behind it.

### Backend-owned parser target evidence owner

`ParserBackendTargetEvidenceOwnerV1` is the first Stage 6A issuer. Its public
surface exposes only owner-scoped `ParserBackendBuildTokenV1`,
`ParserBackendInspectionTokenV1`, `ParserBackendExecutionTokenV1`, and a final
copied `ParserBackendTargetEvidenceReceiptV1`. The owner retains all build,
artifact-buffer, inspector, mapping, callable, capability, and cleanup records.
Stages are explicit enums—Built, BytesSealed, Inspected, ExecutedAndRetired—
rather than caller-supplied booleans. Implementation kind is independently
tagged ScalarReference or ParserLexicalAvx2.

The build record consumes live planner-use/emission and authenticated backend
feature/build authority. It binds compiler plan, parser artifact index/scope,
variant, artifact intent, cache, complete target ABI/profile, optimization and
numerical policy, requested features, backend provider/build/version/mode,
toolchain/ISA-builder generation, accepted features, and unsupported reasons.
The registered backend adapter writes one bounded owner-held artifact buffer;
the owner hashes its exact bytes and dependency content/closure before sealing.

Inspection runs once through a registered owner-issued inspector over the exact
sealed executable section ranges. It retains inspector implementation/version/
generation, normalized decoder output, section identity, parser-classifier
instruction-family counts, forbidden-ISA count, baseline facade/init/dependency
closure result, and canonical inspection digest. The existing f32x8 VEX count
is not parser-classifier evidence.

Qualified execution requires the canonical sealed runtime publication/root and
generation authority, exact mapping authorization and parser ABI/schema/tail
identities, a current execution-domain affinity and live capability verifier,
immutable corpus identity, and the exact pinned callable. It binds environment,
callable, input corpus/count, output, scalar oracle, invocation/native-call
counts, and terminal retirement. Bytes, mapping, callable, source, generation,
and build authorities remain pinned through invocation; cleanup is LIFO. A
partial cleanup record remains private and non-projectable. Replacement permits
already-pinned work to drain but admits no new execution on inactive authority.

The final SHA-256 encoding uses a domain/schema prefix, private token and adapter
registration identities, fixed-width little-endian scalars, full digests,
length-prefixed bounded tool/inspection text, explicit stage/presence/count
fields, and separate requested, accepted, declared, observed, and executed
feature sets. `live` recomputes this digest from owner state. Existing
`TargetCodegenReceiptV1` and parser evidence may be derived only from this live
record; caller-built V1 evidence remains fixture input, never production
authority.

Until real backend, inspector, and executor adapters exist, this owner proves no
emitted parser SIMD, native hardware execution, baseline closure cleanliness,
parser/AST/HIR parity, cache/JIT materialization, cross-platform support, or
performance gain. QEMU evidence remains emulated execution only.
### Backend acceptance issuer placement (2026-09-08 refinement)

Issue backend acceptance at the admitted backend-session compile boundary while
the session generation, normalized target/options, compile result, and exact
object bytes are all live. The result envelope is opaque and owner-scoped; the
driver may project it into `ParserBackendTargetEvidenceOwnerV1`, but cannot
construct acceptance fields itself. Declaration-only feature registries are
diagnostic inputs, never acceptance authority. Direct Cranelift and builtin AOT
paths use adapters into this one envelope rather than defining separate truth
models.

Before issuance, add owner-scoped backend-session generation/liveness authority
and a V2-compatible result envelope carrying canonical accepted features. V1
dynamic providers remain usable for ordinary compilation but are ineligible for
strict optimized-evidence promotion because absence of accepted-feature output
means unknown, not accepted. Builtin adapters must derive acceptance from the
actual configured backend/ISA result, not echo the request.

The authority is a separate owner, not fields added to `BackendSession`: Simple
class copies and the current mutable handle/closed fields are not replay-safe
authority. It binds descriptor, request, unchanged V1 receipt hash, adapter and
dynamic lease identity, generation, and `Accepting | Closing | Closed` state.
Close stops new uses, drains existing compile/result uses, retries failed
teardown, and publishes `Closed` only after success.

Adoption is a migration helper, not the final exclusive-ownership API: because
Simple class values can be copied, a caller retaining the raw session can bypass
the new owner. The production loader path must construct/register the session
inside the authority owner and return only its opaque token. Raw `BackendSession`
continues temporarily for compatibility callers but cannot support strict V2
evidence.

Feature confirmation has an additional precondition: the normalized request
CPU/features must be inputs to the concrete backend target-machine builder.
Today builtin adapter construction drops both fields and LLVM rebuilds its
configuration from defaults. Add a narrow target-configuration object retained
by the adapter/result owner; do not infer effective configuration from the
request after compilation. `AcceptedExact` is available only when the backend
returns the effective canonical feature set used for the exact emitted bytes.

Avoid expanding `BackendCompileOptions`, which has broad non-plugin construction
surface. Add an immutable `BackendPluginTargetContextV2` retained inside the
builtin adapter and plugin-specific compile entrypoints. LLVM receives CPU and
features through `LlvmTargetConfig`; Cranelift requires a new SFFI negotiation
result from its Rust ISA builder. Dynamic providers use a distinct V2 request
wire carrying full normalized target/CPU/features and a V2 result wire carrying
provider acceptance. The frozen 16-byte V1 request remains compatibility-only
and always yields Unknown.

Do not append to or reinterpret the fixed V1 dynamic envelope and do not change
`BackendProviderReceipt.canonical_text()` under its V1 domain. Define a V2
receipt/result schema with canonical requested and accepted feature sets plus
`Unknown | AcceptedExact | Rejected`. V1 adaptation yields `Unknown` and an
empty accepted set. A successful compile, target string, request flag, or object
file never implies acceptance.

The objdump decoder remains a strict stage separate from readobj JSON decoding.
It accepts only the supported object-format header and named executable
sections, reconstructs bytes from gap-free instruction rows, rejects unknown
instructions, and requires full byte-count and digest equality with readobj.
Section order or line position never joins the streams. These rows remain
untrusted data until the external inspection owner consumes admitted terminal
tool-process receipts.

An intermediate pure projection join revalidates all four decoded views and
emits the normalized section, relocation, and instruction shapes plus a framed
digest. It deliberately leaves each `required_feature` empty. A later admitted
instruction classifier must derive features from exact bytes and operands;
caller text or mnemonic-only tables cannot authorize SIMD claims.

Decode the x86 encoding envelope before opcode classification. The bounded
stage recognizes legacy, VEX2, VEX3, and EVEX prefixes, validates reserved map
and length fields, and records only nominal encoded width plus extended-state
need. Keep this evidence separate from exact extension requirements; neither a
VEX prefix nor 256-bit width means AVX2, and EVEX does not mean every AVX-512
extension.

Exact opcode classification uses a generated/digest-identified whitelist keyed
by encoding family, opcode map, mandatory prefix, W, opcode, and encoded width.
Each instruction produces a canonical feature array, because some instructions
require conjunctions such as `avx512f + avx512vl`. Replace or version the
singular V1 feature field before joining classifier output; never flatten a
feature conjunction into one synthetic tier string.

The V2 feature projection consumes both the coherent inspection projection and
the retained exact instruction bytes, rechecks their row identities and byte
digests, classifies all VEX/EVEX rows, and binds canonical per-row and union
feature arrays. Require exact equality between requested and observed feature
sets. Treat legacy rows as unclassified here; a separate baseline-closure gate
must prove their legality.

Bind the readobj and objdump terminal receipts only after confirming distinct
argv identities, common exact input digest/count, terminal lifecycle completion,
local resource caps, and exact stdout/stderr capture digests. The terminal-pair
digest then frames the coherent-data and multi-feature digests. This projection
is the payload a future process owner retains; accepting the same fields from a
caller is validation, never authority.

Place the option-neutral candidate validator below the selected
`CanonicalTargetRegistryOwnerV1`. It enforces canonical ordered tuples,
bijective component IDs/text, and unique profiles/triples. The owner implements
selected Option B: parse and normalize a textual target triple, reject unknown
or ambiguous aliases, resolve the canonical architecture/OS/ABI/object-format
tuple, and issue an opaque live lookup token bound to registry generation,
version, and mapping digest. Direct string hashing does not assign IDs.

The common lookup layer revalidates candidate content/digest before resolving
either canonical triple or numeric profile ID. Profile binding additionally
validates `TargetCodegenProfileV1` and exact architecture/ABI/object/endian/
pointer fields, then emits an inert binding digest. Only a live
`CanonicalTargetRegistryOwnerV1` lookup token may authorize this binding;
registry replacement closes new lookups while retained build/cache uses drain.

Selected inspector Input Option 1 adds `OwnedProcessAtomicInputV3`. Start takes
one bounded immutable byte view and retains its digest/count before child
creation. Its owner progresses stdin writes concurrently with bounded stdout
and stderr drains, closes stdin after the exact byte count, and issues a
terminal token only after child reap. Cancellation, overflow, short write,
timeout, early child exit, or cleanup failure cannot yield inspection authority.
The inspection owner consumes this opaque terminal token and re-runs the
existing projection normalization over owner-retained input and captures.

`CanonicalTargetRegistryOwnerV1` remains a compatibility/content validator.
`CanonicalTargetRegistryOwnerV2` owns bounded resolution and use records. A
replacement stops new use acquisition on old resolutions, preserves projections
for already pinned uses, and retires them only after final release. Its digest
includes the alias table as well as mapping rows and owner generation. V2 output
is still not build authority until a live use projection is consumed inside the
target-profile/build/cache owner rather than copied through caller fields.

The native V3 process implementation must create all pipes atomically with
close-on-exec, bound stdin work to one quantum per poll, and distinguish V2 from
V3 leases. A safe Simple adapter uses a second runtime-owned opaque handle and
never exposes PID, process start identity, or native token halves. Until its
argv/byte-array and returned projection ABI is conformance-tested in both native
and interpreter modes, the C transport cannot be called directly from Simple.

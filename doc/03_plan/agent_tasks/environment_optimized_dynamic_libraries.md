# Agent Tasks: Environment-Optimized Dynamic Libraries

**Phase:** Staged implementation; research/design continuously reconciled with source evidence

## Shared contract

- Interfaces: `EnvironmentSnapshotV1`, `VariantDescriptorV1`, `BindingPlanV1`, `FrontendFacetV1`.
- Scenario helpers: `setup_environment_catalog`, `step_admit_variant`, `step_bind_provider`, `check_execution_receipt`.
- Placeholder policy: `fail(...)`; no empty or always-green scenario bodies.
- Merge owner: root Codex agent.
- Final reviewer: Astra/highest-capability architecture reviewer.

## Parallel lanes

| Lane | Owner/model | Output | Merge condition |
|---|---|---|---|
| Local source truth | Luna sidecar | Local research with exact implemented/gap paths | Root verifies against current worktree |
| Domain mechanisms | Luna sidecar | Primary-source domain research | Direct authoritative citations; proposal separated from fact |
| Requirement alternatives | Luna sidecar | Feature and NFR option documents | 2-4 options with pros, cons, effort; no auto-selection |
| Architecture/design | Astra | Architecture, detail design, compiler plan | Resolves sidecar contradictions and all AC-3..AC-9 boundaries |
| SPipe framing | Root | State, route receipt, system-test plan, agent plan | Acceptance criteria remain testable and implementation-free |
| Generated manual review | N/A in research/design | Deferred until executable SSpec exists | Highest-capability review required before verify |

## Post-selection implementation packages

1. ENV contract/probe/catalog foundation.
2. Native/SMF generation-safe loader adapters.
3. Compiler target descriptor, JIT/AOT cache, and emitted-ISA verification.
4. Legacy/canonical parser seam and scalar parity.
5. Pure-Simple parser SIMD provider family.
6. GPU registry/device-program and lifetime adapter.
7. Residency-aware frontend/render execution islands.
8. Product configuration, explain receipts, packaging, guides, expert knowledge, and blocked-host ledger.

Packages 4-7 remain blocked from done marks until their independent semantic and execution evidence is retained. No agent may fold unrelated dirty work into this lane.

## Current package status

| Package | Current evidence | Remaining owner work |
|---|---|---|
| 1 | Bounded contracts, catalog, exact admission, composite MAX→PREFER/REQUIRE selection, rejection-preserving canonical publication, composite-aware lifecycle receipts, and generation-checked runtime commit | Production startup/CLI consumer wiring, qualified self-host execution, and host matrix |
| 2 | Native/SMF placement contracts and provider provenance adapters | Real callable mapping and native/SMF parity |
| 3 | Host-target build planner, target evidence chain, parser SIMD inspection contract | Real AVX2 artifact emission/inspection/execution and cache wiring |
| 4 | Concurrent lexer/structural work exists outside this lane | Stable parse-result provider seam and normalized scalar dialect parity |
| 5 | SIMD promotion contract; exact-evidence V2 lifecycle; sealed stepwise transaction; truthful routing receipts; partition-safe scalar summaries; sealed 22-state transition-table monoid with exhaustive unsealed semantic verification and canonical admission digests | SIMD candidate-byte classification plus scalar state resolution, routing verification, advisory frontend wrapper, native x86/self-host qualification, broader lexical coverage, and emitted v3/v4 siblings |
| 6 | GPU admission and Engine2D completion bridges with negative specs; hosted ABI-v1 mapper/lifetime owner with sealed Linux provider bytes, bounded capability tokens, retained unload fences, terminal receipt/resource correlation, staged checksum readback, and typed native authority projection | Authenticated device-program image owner, task-owner consumption of native authorities, Vulkan parser kernel, and real device fixture |
| 7 | Architecture and routing-only queue seams | Resident frontend/render execution and transfer-aware scheduling |
| 8 | Requirements, plans, guide, manual, pure policy resolver, presence-aware supplied-layer collector, authenticated sealed collect-to-prepare boundary, catalog projection, and preparation bundle | Trusted command/config owner wiring, package integration, explain output, and measured NFR evidence |

### Package 8 owner handoff

The product owner must preserve `{present, value, source}` while parsing CLI,
environment, project, and user configuration. It must not reconstruct those
layers from merged `CompilerConfig`. `--cpu`/`SIMPLE_NATIVE_CPU` and
`SIMPLE_CPU_FEATURES` remain generated-target inputs. Administrator restrictions
come from an authenticated administrator-owned source. Catalog, environment,
artifact, and binding facts are gathered only on compilation paths, then passed
with the preserved layers to `environment_variant_collect_and_prepare_v1`
exactly once. Help/version paths must not initialize optional GPU/provider state.

### Package 5 parser-session owner handoff

1. **Loader/kernel-plugin owner:** correlate the authenticated publication and
   mapped callable into `ProviderGenerationManagerV2`, map the AVX2 artifact
   once per provider generation, and issue a generation-pinned opaque
   `ExecutableKernelLeaseV1`; never expose an arbitrary function pointer.
2. **Memory/Object-VM owner:** copy or register each immutable source snapshot
   once and issue `StableSourceBufferLeaseV1`; no allocation per 32-byte block.
3. **Structural provider owner:** create `StructuralMaskSessionV1`, invoke the
   leased callable for complete blocks, run the overflow-safe scalar oracle for
   the 0–31 byte tail, and return masks plus deterministic positions.
4. **Parser runtime owner:** route admitted SIMD sessions through the provider
   port. False capability selects scalar before executable mapping; required
   mode fails visibly and preferred mode records fallback.
5. **Lifecycle owner:** keep code/source/output pinned through completion, free
   the source lease exactly once per session, and retire code only after the
   provider generation drains.

The V2 manager does not independently authenticate caller-created evidence.
Only the compiler/loader adapter may construct its activation record, after
recomputing publication sidecars, mapped-byte identity, callable binding, and
execution-capability authority. The guarded call must retain the resulting pin
until result validation and parent-authoritative batch commit finish.

Acceptance covers zero length, all tails, block plus tail, duplicate
delimiters, high bytes, exact positions, source immutability, map/call/free
counts, stale generations, cancellation, and false-capability zero-mapping.
Physical x86 and self-host execution remain separate promotion evidence from
the existing QEMU TCG result.

## Lexical summary follow-up (2026-09-08)

- Scalar owner: qualify `lexical_block_summary_v1` across boundary states.
- SIMD owner: lower the same masks/state contract without widening coverage.
- Frontend owner: consume only untagged summaries; route tagged regions to the
  legacy lexer.
- Sidecar lanes: N/A for this bounded foundation.
- Merge owner: environment-optimized provider lane coordinator.
- Final reviewer: highest-capability architecture review.

## AVX2 lexical primitive follow-up (2026-09-08)

- Implemented: exact x86-64 SysV one-byte/32-byte AVX2 equality-mask callable,
  exact native trampoline, scalar nine-field oracle, and focused contract tests.
- Next SIMD lane: build an authenticated provider-owned batch that invokes the
  primitive for the required byte classes or emits a separately qualified
  one-call multi-mask kernel; feed only raw masks into the scalar 22-state
  transition-table resolver.
- Portability lane: emit and qualify a separate Win64 callable before claiming
  Windows support; the current `RDI`/`ESI` byte sequence is SysV-only.
- Evidence lane: bind code/ABI/layout identities during authorization, execute
  under QEMU or physical x86, and retain the scalar oracle for differential
  qualification. Do not label emitted bytes as executed code.
- Merge owner: environment-optimized provider lane coordinator.
- Final reviewer: highest-capability architecture review.

## Parser variant build-plan follow-up (2026-09-08)

- Contract owner: define `ParserVariantBuildPlanV1` with host execution
  identity, generated target triple/features, parser ABI/schema/grammar/program
  identities, placement, optimization policy, artifact/cache identity, and
  explicit unsupported-feature reason.
- Compiler owner: adapt existing whole-module target CPU/cache plumbing without
  treating it as parser-only sibling generation or JIT feature support.
- SIMD owner: admit baseline and v3 only after emitted/artifact/execution proof;
  keep v4 unsupported until lowering and exact feature requirements exist.
- Sidecar research: completed by the lower-model JIT/AOT audit.
- Merge owner: environment-optimized provider lane coordinator.
- Final reviewer: highest-capability architecture review.

## Packed GPU completion follow-up (2026-09-08)

- Completed contract unit: owner-scoped packed submission/completion/retirement
  schema with unique live submissions, replay rejection, and reusable capacity.
- Backend owner: create the provider callback that derives fence/readback facts
  from the existing Vulkan/CUDA/Metal session rather than caller booleans.
- Queue owner: join that callback at
  `engine2d_draw_ir_runtime_queue_complete_packed`; preserve routing-only
  receipts for compatibility completion.
- Memory owner: correlate the exact packed arena lease and retire it only after
  backend fence authority completes.
- Sidecar research: completed GPU seam and authority red-team audits.
- Merge owner: GPU backend/Engine2D integration owner.
- Final reviewer: highest-capability GPU architecture reviewer.

## Sealed activation migration follow-up (2026-09-08)

- Astra architecture lane: completed the aggregate-owner contract and lifecycle review.
- Smaller-model call-site lane: confirmed there are no production consumers; V1 can remain diagnostic.
- Smaller-model red-team lane: identified child-token exposure, join/pin release ordering, and retired-pin cleanup gaps.
- Implementation owner: added the intermediate collect-and-activate adapter; source check passes.
- Next owner: add fresh aggregate-owner behavioral specs, cleanup-pending recovery, and aggregate build-join leases before migrating a product caller.
- Aggregate-owner evidence owner: completed the first fresh 2/2 lifecycle and failure-without-token-consumption suite; expand only in a later session without rerunning this green gate.
- Replacement owner: active/continuation predicate split is source-checked; add a fresh two-generation regression without rerunning the green aggregate suite.
- Join-lifetime owner: coordinator use lease and build-join integration are source-checked; qualify them in a fresh uncapped spec before cache/JIT authority work.
- Aggregate join owner: Astra contract and two smaller-model audits complete; implement private coordinator pin/use plus planner/emission retains, then migrate away from direct-coordinator joins.
- Planner-retain owner: planner artifact use and retryable dual-lease join cleanup are source-checked; add fresh behavior tests with the aggregate join implementation.
- Planner-retain evidence owner: fresh focused behavior passes 2/2; do not rerun this green gate, and consume it as the aggregate join prerequisite.
- Sealed build-use owner: opaque private child pin/use lifecycle is source-checked; next add full publication projection, cleanup-pending rollback, and a fresh focused spec.
- Sealed build-use projection owner: full runtime publication/pin correlation implemented; next add canonical authority digest, rollback retention, and fresh behavior before emission migration.
- Sealed build-use digest owner: canonical owner-recomputed digest and stronger direct-join planner/generation comparisons source-check; next qualify build-use behavior and migrate emission join.
- Emission-lifetime owner: issue/project/live/release with planner retention is source-checked; add fresh behavior then feed only this owner authority into aggregate join.
- Emission-lifetime evidence owner: fresh focused behavior passes 2/2; consume it as the aggregate join prerequisite without rerunning this gate.
- Merge owner: compiler driver environment-variant owner.
- Final reviewer: highest-capability compiler/loader architecture reviewer.

## Cache V2 follow-up (2026-09-08)

- Contract owner: implemented canonical V2 namespace construction, validation,
  feature registry/digest checks, BinaryObjectAction cross-checks, scoped action
  identity, and V1-to-V2 recomputation migration.
- Evidence: focused bootstrap-seed diagnostic passes 4/4 at the third/final
  cycle; do not rerun unchanged in this session or call it self-host evidence.
- Publication owner: replace caller-built V2 receipts with an opaque receipt
  derived from authenticated publication and exact live provider generation.
- JIT/cache owner: key lookup by `scoped_identity`, preserve cache I/O bounds,
  and validate artifact bytes/entry ABI before materialization.
- Merge owner: compiler backend/environment-provider owner.
- Final reviewer: highest-capability compiler/cache reviewer.

### Owner projection progress

- Completed: generation owner issues and revalidates an opaque full-width pinned
  cache authority whose digest includes private mapping correlation.
- Evidence: focused provider-generation spec passed once; upper-word mutation,
  alternate private mapping, and released-pin staleness are covered.
- Next: the compiler-owned issuer must join this live projection with canonical
  composite publication, target-codegen facts, exact artifact bytes, and the
  complete `BinaryObjectActionV1`; it must not copy caller trust flags.

### Build/publication join prerequisite

- Build owner: add a typed emitted-artifact receipt retaining the exact compiler
  plan/artifact index, target profile/features, backend/toolchain, dependency
  lock, artifact bytes, parser/program/entry closure, and cache key.
- Publication owner: correlate that receipt with the independently canonical
  runtime root descriptor/publication and live pinned-generation authority.
- Cache issuer: consume the opaque join; never equate compiler
  `plan_identity` with runtime `plan_digest`.
- Sidecar audit: completed by the lower-model schema/fixture lane.
- Final reviewer: highest-capability compiler/loader architecture reviewer.

- Scaffold status: bounded actual-byte emission and authenticated root
  publication/live-generation assertion joining and lifecycle reclamation are
  source-checked. Immutable compiler-plan and publication tokens are now wired;
  join behavioral tests, backend-support authority, and canonical target
  text↔ID correlation remain assigned.

- Publication owner: opaque revocable token over canonical admission rows and
  composite sidecars is implemented and required by the build join.
- Target owner: add `TargetIdentityMappingV1` joining canonical triple/object
  text to architecture/ABI/object-format/endian/pointer numeric identities;
  architecture IDs exist, but ABI/object-format/OS numeric registries require a
  selected authoritative assignment rather than inferred LLVM text.
- Backend owner: issue an authenticated supported-feature projection instead of
  treating planner caller arrays as backend capability authority.
  The bounded declaration owner is implemented; backend-specific provider/
  build/mode/target/toolchain/policy receipt adapters remain assigned in
  `environment_variant_backend_feature_receipt_2026-09-08.md`.
- Activation coordinator owner: behaviorally qualify the opaque reserve →
  generation-injected canonical publication → finalize transaction, including
  admission rollback, unique root placeholders, cross-owner tokens, and exact
  active-generation liveness. Only then replace manual generation threading in
  downstream join fixtures.
- Join migration owner: add a fresh coordinator-backed positive join spec after
  the capped raw-owner fixture was removed; cover pin revocation, coordinator
  release-busy, planner revocation, token substitution, and cleanup ordering.

### Cache canonical encoding prerequisite

- Cache owner: replace raw `|`/`,` interpolation with the shared canonical
  action-key codec or bounded length-prefixed bytes; normalize CPU features as
  a sorted unique set.
- Evidence owner: add known vectors, delimiter/Unicode distinctions, every
  field mutation, and exact cap/max-plus-one cases in a fresh session because
  the current cache V2 spec reached its three-cycle limit.
- Sidecar design: completed by the lower-model encoding audit.
- Final reviewer: highest-capability compiler/cache reviewer.

## Backend callback bridge follow-up (2026-09-08)

- Contract owner: completed the bounded opaque completion-port and one-shot
  callback-authority bridge; focused contract diagnostics pass 8/8.
- Vulkan owner: retain the exact native submission fence and packed arena lease
  beyond wait, bind them to provider/session/image/device and epoch/content,
  and issue callback authority only from that owner-held record.
- Queue owner: consume the Vulkan authority at packed completion without
  changing the compatibility route's routing-only status.
- CUDA/Metal owners: N/A until each backend exposes an equivalent persistent
  event/fence and lease-retirement authority.
- Cache owner: implement the independently specified V2 canonical namespace and
  validation adapter before any JIT materialization work.
- Merge owner: GPU backend/Engine2D integration owner.
- Final reviewer: highest-capability GPU architecture reviewer.

## Backend-owned target evidence follow-up (2026-09-08)

- Evidence contract owner: version an opaque staged owner for backend
  acceptance → exact emitted artifact → inspection → callable execution;
  caller-constructed V1 records remain validator fixtures only.
- Evidence contract progress: the parser-scoped `BytesSealed` adoption slice is
  source-checked. It privately retains canonical emission-use authority and
  exposes only an owner-recomputed opaque projection. Next add authenticated
  backend acceptance and owner-held immutable bytes/dependency closure before
  permitting inspection.
- Evidence test progress: the focused owner spec passes 2/2 interpreter examples
  for retained emission lifetime, exact projection, forged-token rejection,
  release ordering, and mismatched-plan rejection. This closes only the first
  `BytesSealed` behavior slice; instruction inspection and execution proof stay
  open.
- Exact-byte progress: the canonical emission owner now retains bounded emitted
  bytes and releases a validated copy only under a live exact use token. The
  parser evidence owner privately snapshots and rehashes that copy before each
  projection. Source checks pass; add a fresh accessor behavior fixture before
  treating this lifetime boundary as behavior-qualified.
- Astra 6A.1 review: use a separate session authority owner rather than changing
  copyable `BackendSession`; preserve V1 receipt hashes and fixed wire; introduce
  V2 requested/accepted feature semantics with V1=`Unknown`; make close
  retryable and drain uses; qualify LLVM confirmation before Cranelift. Merge
  owner remains ENV-05; independent final review remains QA-01.
- V2 schema progress: `backend_plugin/result_v2.spl` and its focused spec now
  pass 3/3. V1 maps only to Unknown, exact acceptance requires canonical equality,
  and request echo/partial claims fail. Next owner is 6A.1a session lifetime;
  this schema alone does not authorize optimized output.
- Session authority progress: separate owner/use/generation and drain-before-close
  lifecycle source is implemented; retryable close fixes landed in session and
  dynamic adapter code. The focused spec passes 2/2 at its cycle cap. Next route
  loader ownership directly into this owner (no escaped raw session copy), add
  teardown-failure injection, then owner-issued V2 result tokens.
- Authorized producer progress: strict loader API now returns only an opaque
  authority token. Its retained LLVM session compiles real representative MIR
  into owner-held bytes and issues a revalidated V2 `Unknown` result whose live
  use blocks close. The focused loader/result spec passes 3/3. Next add actual
  LLVM accepted-feature confirmation, then consume its token in the parser
  backend evidence owner; V1 dynamic providers remain Unknown.
- Smaller-model propagation audit: keep broad `BackendCompileOptions` stable;
  add immutable plugin-only target context to the builtin adapter. LLVM and
  Cranelift need provider-owned effective configuration/negotiation results.
  Dynamic V1 currently transports only a frozen 16-byte prefix despite wider
  header fields, so a separate V2 request/result ABI and runtime round-trip
  tests are required. ENV-05 owns builtin/LLVM merge; backend/runtime owners
  review Cranelift and dynamic ABI changes; QA-01 remains final reviewer.
- Builtin context progress: immutable `BackendPluginTargetContextV2` is retained
  by the builtin adapter and its canonicalization/substitution spec passes 2/2.
  Next add an LLVM-specific compile-result adapter that consumes this context
  and returns effective target configuration; acceptance remains Unknown now.
- LLVM preparation progress: exact x86_64 CPU/feature mapping into
  `LlvmTargetConfig` is implemented and its capped spec passes 2/2. Next route
  representative MIR compilation through this prepared config and return the
  effective configuration with the exact bytes; only that successful path may
  become a candidate for AcceptedExact.
- LLVM configured-emission progress: real MIR now compiles through the exact
  retained target context, returns effective CPU/features with the exact bytes,
  and the authority owner issues AcceptedExact only on exact equality. Backend
  adapter tests pass 4/4 and the authorized suite passes 4/4 at its cap. Next
  project this live result token into `ParserBackendTargetEvidenceOwnerV1`, then
  add independent binary inspection; no instruction/execution claim exists yet.
- Backend adapter owner: consume the real backend/toolchain result and exact
  executable bytes. N/A for target families that cannot yet emit the requested
  feature set; report unsupported rather than scalar success.
- Inspection owner: perform one bounded inspection of those exact bytes, bind
  tool/version, executable section ranges, normalized output digest, observed
  instructions, and dependency/init closure. Never accept a free-form nonzero
  digest as production evidence.
- Execution owner: acquire the admitted execution-domain/provider generation,
  invoke the exact callable, bind input/output/scalar-oracle digests and count,
  then retain evidence until callable and artifact leases retire.
- Cache/JIT owner: consume only the completed opaque evidence token when
  materializing or publishing specialized code; cache identity is not execution
  authority.
- Sidecar audit: Astra highest-assurance review in progress; smaller-model lane
  complete. It requires `ParserBackendTargetEvidenceOwnerV1`, opaque staged
  tokens, immutable owner-held bytes, parser-specific inspection, pinned
  execution, LIFO retirement, and owner-recomputed canonical digest. Smaller-
  model lane N/A because schema inventory already established producer absence.
- Merge owner: compiler backend/environment-provider owner.
- Final reviewer: independent highest-capability compiler/backend reviewer on
  real compatible hardware.

## 6A.2 parallel ownership split — external inspector process

- Process-runtime owner: add the selected identity-owned binary-input ABI beside
  `rt_process_owned_*_v2`; preserve random-token authority, bounded concurrent
  output, process-group cancellation, exact reap, and one-shot collection.
- Simple I/O facade owner: expose only opaque token/value operations and typed
  terminal receipts. Raw PID-based piped APIs remain legacy and cannot authorize
  inspection.
- Tool-admission owner: register exact readobj/objdump image/version/argv/env
  identities, block PATH/shell/plugin/response-file injection, and retain tool
  generations until every process lease retires.
- Inspection owner: consume BytesSealed and terminal non-overflowed exit-zero
  tool receipts, run separate bounded codecs, correlate complete closure and
  raw bytes, and publish the opaque inspection token.
- Sidecars: Astra highest-assurance lifecycle/API audit complete; Luna runtime
  reuse audit and pure-Simple staging option audit complete. User selected
  Input Option 1 on 2026-09-08; merge owner implements atomic immutable stdin.
- Merge owner: runtime/process owner jointly with ENV-05 compiler owner.
- Final reviewer: independent highest-capability runtime security reviewer,
  followed by compiler/backend reviewer for the inspection join.
- Codec progress: bounded readobj section/symbol/relocation/group decoders and
  the objdump raw-instruction decoder now exist. The objdump suite passes 4/4
  and proves exact executable-section reconstruction against readobj digests.
  Next join these projections under the user-selected stdin/staging process
  authority and admitted tool generation; never promote codec output directly.
- Projection-join progress: a strict cross-stream join now passes 4/4 after
  caller-mutation hardening. Next option-independent work is an exact
  byte/operand ISA classifier and its negative opcode/width matrix. Process
  execution remains dependent on the selected inspector-input option.
- Encoding progress: the fail-closed VEX/EVEX envelope decoder passes 4/4 on
  locally emitted instruction bytes. Next implement generated exact opcode-map
  classification for the parser kernel whitelist and bind classifier-table
  identity into the inspection digest. Envelope evidence alone cannot populate
  `required_feature`.
- Opcode progress: exact VPXOR/VPSHUFB/VPTERNLOGD classification passes 4/4.
  Before wiring it into the projection join, introduce canonical bounded
  per-instruction feature arrays and update normalization/digest tests. Then
  grow the generated parser-kernel whitelist from actual emitted corpus rows;
  unknown vector opcodes remain hard failures.
- Multi-feature progress: additive V2 feature projection passes 4/4 with exact
  requested/observed set equality and byte-to-row recorrelation. Next bind its
  digest plus V1 terminal/process facts into an owner-issued inspection token,
  after the user selects the process input mechanism. Independently expand the
  whitelist from the representative emitted parser corpus and add baseline
  legacy-instruction closure.
- Terminal-join progress: the bounded two-tool V2 terminal/data/feature join
  passes 4/4 at its three-cycle cap. Once inspector input option 1/2/3 is
  selected, implement that owned-process adapter and issue an opaque token only
  after rerunning this full normalization internally over owner-retained bytes
  and captures. Do not expose caller-constructible terminal facts as authority.
- Target-mapping progress: the common inert candidate validator passes 4/4 and
  assigns no IDs. User selected Option B on 2026-09-08. Implement the canonical
  target-triple registry authority owner, bind its live generation/version/
  digest into target profiles and cache/build joins, and add alias, unknown,
  ambiguity, cross-version, replacement, and retained-use drain tests.
- Common lookup progress: revalidated triple/profile-ID lookup and exact
  target-codegen tuple binding pass 4/4. Continue with selected B + 1; preserve
  the inert validators beneath both authority owners and do not treat their
  digests as capabilities.
- Selected B lifecycle progress: inert V1 mapping plus a bounded parent-owned
  V2 resolution/use/replacement implementation now exist. Focused V2 specs are
  present but unexecuted because the deployed Simple runtime failed its
  production identity preflight. Next join only live V2 use projections into
  target profile, cache, plan, and receipt owners; do not publish V1 content
  tokens as authority.
- Selected 1 transport progress: native process V3 now copies and hashes bytes
  before fork, uses CLOEXEC pipes, applies bounded three-pipe progress, rejects
  short writes and V2-token substitution, and passed its focused native C
  self-check including concurrent-child EOF isolation. The Simple opaque-handle
  adapter and admitted tool/argv/environment/output-digest inspection owner
  remain active work; their exact ABI and acceptance plan is retained in
  `doc/08_tracking/todo/owned_process_v3_simple_opaque_abi_adapter.md`.
- Selected 1 opaque bridge progress: the runtime-owned random immediate-handle
  registry, binary poll projections, registered native symbols, fail-closed
  interpreter handlers, and typed Simple facade are implemented. Astra review
  found and the merge owner fixed allocation-before-publication/delivery,
  invalid-wait receipt initialization, immediate-handle range, post-reap
  polling, native collection state, and release ABI width. The final focused C
  adapter self-check passes. Non-Unix definitions, allocation-failure tests,
  and admitted production Simple/Rust checks remain open.
- Admitted pinned-tool progress: preserve legacy raw-FD pinning and add a
  separate opaque pin owner. The native pinned V3 path executes only a retained
  sealed static ELF through `fexecve` with fixed environment/cwd and complete
  inherited-descriptor closure. The real integration selfcheck exists but is
  not green after its capped attempt exposed and then prompted correction of a
  Linux preprocessor-scope defect. Add a length-aware pin ABI, register/wrap the
  three pinned symbols, bind SHA-256 of final sealed bytes, and rerun in a fresh
  verification session before consuming this path as tool authority.

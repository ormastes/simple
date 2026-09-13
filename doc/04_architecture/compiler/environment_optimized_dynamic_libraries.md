<!-- codex-architecture -->

# Environment-Optimized Dynamic Libraries Architecture

## Status

**Selected design direction: Feature A + NFR N2 + target registry B + inspector input 1; implementation evidence is pending.** This
document refines the research in
`doc/01_research/compiler/simd/simple_environment_optimized_dynamic_libraries_2026-09-07.md`.
It does not claim an implemented catalog, parser provider seam, SIMD artifact
matrix, GPU execution, benchmark, or conformance result.

The 2026-09-08 authority decision uses a repository-owned versioned canonical
target-triple registry and atomic bounded immutable stdin for external binary
inspection. It does not introduce an external signed registry, network lookup,
or filesystem-staging authority.

The V1 canonical registry is inert content validation only. Production target
authorization uses the V2 parent-owned lifecycle: owner-instance and generation
identity, alias-inclusive registry digest, bounded resolution/use handles,
active-to-draining replacement, and retirement after retained uses reach zero.
Runtime process V3 is likewise a transport primitive; exact tool/argv/
environment and output identities are joined by a separate admitted inspector
owner before any inspection token can authorize publication.

## Context

Simple needs host-aware implementation selection without multiplying the whole
compiler executable. Four axes must remain independent: host execution
environment, generated-code target, artifact placement, and workload execution
policy. Current source provides useful but incomplete foundations:

- `std.nogc_sync_mut.composition` has ABI-safe provider query records and
  generation pin/retire machinery;
- current SIMD manifests and rank-based dispatch are scaffolds, not exact
  feature admission;
- `compiler.frontend.core.frontend` directly invokes the legacy parser;
- structural parse auto-profile selection deliberately returns scalar only;
- hosted GPU loading and packed DrawIR submission exist, but routing is not
  device execution or fence evidence.

## Decision

Extend the existing composition and provider-generation owners with a bounded,
typed variant catalog. Do not introduce an independent plugin framework.
Admission chooses which artifacts are safe and callable. A later domain planner
chooses where an admitted request executes. CPU SIMD and GPU placement are
siblings under policy, never a single ordered tier.

The initial product slice is one baseline-safe Simple core plus parser provider
variants. Other compiler providers remain single-version. Generated native
products specialize selected dynamic-library boundaries first. JIT target
features come from the executor environment, independently of the frontend
host.

No production default changes until selected requirements exist and the
canonical parser reaches declared parity. The legacy CPU frontend remains an
independent correctness path.

## Canonical contracts

The names below are frozen for design and parallel implementation. Their field
sets remain versioned implementation contracts subject to ABI review before publication.

### `EnvironmentSnapshotV1`

An immutable, generation-tagged statement of execution architecture, OS/ABI,
hardware features, OS-usable features, policy-allowed features, CPU execution
domain, vector-state constraints, permitted loading operations, and discovered
GPU devices. It never carries generated-code target intent.

### `VariantDescriptorV1`

A bounded record for provider/variant identity, logical contract and version,
ABI and artifact digests, placement, exact CPU/OS/device requirements, semantic
profile, grammar/program digest, dependencies, memory domains, resource-layout
digest, numerical contract, assurance receipt, and startup budget.

### `BindingPlanV1`

An immutable result of eligibility and dependency resolution: environment and
provider generations, dense facet slots, dependency lock, policy digest,
selected variant identities, and rejected-candidate reason codes. It is pinned
at a session or batch boundary, not recomputed per token or pixel.

### `FrontendFacetV1`

A coarse session interface: create a session, plan regions, execute a batch,
inspect a receipt, and release. The boundary carries immutable byte views or
registered handles plus bounded offset/count arenas. Compiler-private AST/HIR
objects and function values do not cross it.

Existing V1 structures are not rewritten in place. Versioned adapters project
between current provider query/generation records and these contracts.

## MDSOC layer model

```text
L0 policy inputs
  CLI / permitted environment / project / user / administrator policy
                         |
L1 common contracts
  EnvironmentSnapshotV1 / VariantDescriptorV1 / reason codes / codecs
                         |
L2 admission capsule
  inert metadata -> trust/ABI/features/dependencies -> loader adapter
                         |
L3 generation and binding capsule
  activate -> BindingPlanV1 -> pin -> publish -> drain -> retire
                         |
L4 typed domain adapters
  FrontendFacetV1 / compute / render / scene / codegen facets
                         |
L5 execution services
  CPU reference/SIMD | native/SMF/JIT | existing GPU service and queues
                         |
L6 evidence and commit
  execution receipt / semantic validation / cache publication
```

- `common` owns schemas, exact feature IDs, codecs, and shared reason codes.
- composition owns catalog decoding, eligibility, dependency closure, and dense
  bindings.
- loader adapters own platform mapping/callability proof; they do not choose
  semantic fallback.
- provider-generation ownership supplies publication, pinning, draining, and
  retirement.
- frontend, codegen, compute, render, and scene siblings consume typed facets;
  none reaches into another sibling's private state.
- existing GPU registries, SimpleRing, Object VM memory leases, SOSIX host
  capabilities, and Engine2D remain authoritative in their domains.

The admission/binding behavior is a virtual capsule crossing composition,
loader, compiler frontend, JIT/AOT, and GPU domains. Platform loaders and domain
providers are adapters. Observability is a feature transform around coarse
boundaries; it cannot replace implementations or change semantic ownership.

## Eligibility and selection

Eligibility is a conjunction evaluated before preference ranking:

```text
architecture/ABI match
AND authenticated artifact and dependency identity
AND exact required CPU features and OS state are usable
AND execution-domain/vector-state contract holds
AND contract, grammar/program, and semantic profile match
AND effects and memory domains are permitted
AND required GPU features are enabled and limits/lifetimes suffice
```

`prefer` ranks eligible candidates and may visibly fall back. `require` fails
when unavailable. `max` excludes candidates above a compatible architecture
preset. None can manufacture capabilities, cross architectures, or bypass
trust. Instruction permission, tuning, preferred vector width, and scalable
vector-length contracts remain separate fields.

## Lifecycle and trust boundary

The only safe order is:

```text
discover -> inspect inert metadata -> verify identity/dependencies
 -> test environment eligibility -> map/load -> query typed descriptor
 -> create bounded session/resources -> self-check -> publish generation
 -> execute -> drain -> retire
```

Native metadata checks occur before `dlopen`/equivalent because constructors
may execute during load. Arbitrary untrusted native code requires containment,
not optimistic post-load inspection. Artifact and dependency identities bind to
the exact bytes mapped. A generation remains pinned by CPU calls, JIT
relocations, callbacks, sessions, GPU commands, resources, and completion
objects. Cancellation is not retirement evidence.

## Parser architecture

Two CPU paths remain:

1. the legacy frontend, preserving independent full-parser behavior;
2. the canonical runtime, whose scalar, SIMD, and GPU executors share generated
   dialect-specific lexical, structural, grammar, and action programs.

`FrontendFacetV1` is inserted behind the shared frontend facade only after a
reference adapter preserves reset, append, isolated-error-state, interpolation,
placeholder transformation, diagnostics, and source spans. Simple, SDN, and
sosh retain distinct dialects under one grammar authority. GPU-valid regions
may advance to flat Parsed HIR/local work; global binding and recovery remain
explicit CPU stages until independently designed and qualified.

## Generated-code architecture

The baseline facade and initialization closure remain within their declared ISA.
Sibling native/SMF artifacts may carry exact x86-64 preset plus optional-feature
requirements. A provider can internally use function multiversioning, but the
catalog remains the portable deployment mechanism. JIT units record executor
features, backend/compiler digest, target ABI, optimization/numerical policy,
dependencies, and resource generation. Unsupported strict features fail; a
scalar loop cannot be reported as SIMD execution.

The x86 host path uses the V2 feature word as its sole preset authority. The
live adapter bounds CPUID leaves, keeps hardware, OS-usable, and policy-ceiling
words separate, and admits AVX-512 state only when XSAVE and OSXSAVE are
advertised and XCR0 enables XMM, YMM, opmask, ZMM-high-256, and high-ZMM state.
Plain x86-64-v4 requires AVX512F/BW/CD/DQ/VL; VBMI and VBMI2 remain separately
named optional variants. Canonical publication routes x86 snapshots through
this exact-level gate before mapping or artifact admission, while forwarding
GPU device facts unchanged to the shared eligibility selector. Generated-code
target CPU/features never participate in this host-execution decision.

## GPU architecture

A GPU variant has a host control provider and one or more logical device
programs. Device formats, enabled features, resource layout, memory domains,
limits, and numerical semantics are separately admitted. The domain planner
chooses resident execution islands from admitted facets using node execution
cost plus memory-domain crossing cost. GPU rendering and GPU-owned scene
semantics remain distinct profiles. Actual submission, fence completion, and
lease retirement are mandatory execution evidence.

## Startup and hot paths

Startup performs one bounded environment snapshot, catalog decode, eligibility
pass, dependency resolution, and binding-plan publication. CPU-only help,
version, and reference compilation must not initialize GPU services. Production
startup never compiles a missing optimized provider.

Hot requests read a generation-pinned dense slot and invoke one coarse batch.
They perform no filesystem scan, environment parse, symbol lookup, pointcut
match, subprocess, catalog decode, benchmark, or lifecycle lock per token,
pixel, or operation. GPU requests reuse admitted device/session resources and
bounded queues.

## Cache and invalidation

| Cache | Identity | Invalidated by |
|---|---|---|
| Environment snapshot | host process, usable feature state, execution domain, policy generation | affinity/domain, vector state, policy, device or loader-capability change |
| Binding plan | catalog, environment generation, policy, dependency lock | any identity input or provider quarantine change |
| Semantic parse/HIR | source, dialect/grammar/actions, options, schema, semantic profile | source/grammar/action/schema/semantic change |
| Native/SMF/JIT code | IR/source, backend/compiler, target triple/features, ABI/numerics, dependencies | any identity change |
| Device program/pipeline | program, device API/features, layout, toolchain, compatible driver/device identity | incompatible program/layout/device/driver state |
| Calibration | environment, workload bucket, policy, provider digest, evidence | provider/environment/policy change or evidence expiry |

Semantic cache sharing across providers requires certified equivalence and
retains execution provenance. Calibration may rank only already eligible
candidates.

## Proposed budgets and evidence gates

Exact acceptance values are **pending NFR selection**. Initial measurement
envelopes for option-setting are:

- CPU-only warm startup regression: measure p50/p95 and max RSS against the
  baseline core; proposed target <= 5% latency and <= 8 MiB RSS increase.
- warm provider dispatch: proposed p95 overhead <= 1% of representative batch
  time, with no per-element allocation or lock.
- catalog work: one bounded startup pass, with candidate/dependency limits and
  explicit rejection rather than unbounded growth.
- parser variants: report tiny, ordinary, large, Unicode-heavy, malformed, and
  boundary-tail workloads; no promotion without exact differential results.
- GPU: report cold initialization, warm queue time, upload/readback bytes,
  synchronization, CPU service time, p99 latency, and actual device completion.

These numbers are design hypotheses, not accepted requirements or measured
results. Requirements selection may replace them.

## Failure and rollback

Admission failures are typed and occur before publication. Execution writes to
private staging and commits only validated results. `require` never falls back;
permitted auto/prefer fallback records a reason. Rollback selects a previous
qualified generation for new sessions; pinned old sessions drain. Broken
artifact/environment pairs enter an explainable quarantine. Device loss or
post-submit cancellation retains resources until real completion/retirement.

## Consequences

### Positive

- one portable core rather than a whole-executable environment matrix;
- exact compatibility and truthful execution evidence across native, SMF, JIT,
  CPU SIMD, and GPU placements;
- bounded hot-path dispatch and generation-safe replacement;
- parser-first rollout can proceed independently of resident GPU scene work.

### Negative

- descriptors, adapters, dependency locks, and lifetime proofs add complexity;
- canonical parser parity and real SIMD/device proof are substantial gates;
- heterogeneous execution domains require pinning or common-feature policy.

### Neutral

- GPU is an execution placement, not a CPU tier;
- dynamic libraries and SMFs share logical contracts but not binary ABIs;
- aspects remain useful for observation/verification, not hidden replacement.

## Open decisions requiring user-selected requirements

- initial host/product matrix and which x86/Arm/RISC-V variants ship;
- whether the first release is parser-only or also includes one generated
  dynlib pilot;
- automatic-selection policy and accepted startup/RSS/dispatch budgets;
- canonical parser parity scope and GPU profiles eligible for opt-in;
- trust/signing/containment requirements for third-party artifacts.

## PAR-03 implementation gate: parser byte SIMD

The compiler now has a pure-Simple-emitted x86-64 AVX2 two-byte mask callable
and typed lowering primitives for unaligned byte load, equality, OR, and lane
mask extraction. Exact bytes match independent assembler output and the body
has positive/negative QEMU execution evidence. This is a real byte-SIMD
prerequisite, but it is not yet general MIR lowering, hardware/self-host proof,
or parser-provider execution. The C UTF-8 kernels remain useful references but
are not evidence of a pure-Simple parser kernel.

The narrow critical path is:

1. Generalize the proven byte emitter into fixed-width byte-vector MIR
   operations where needed, retaining scalar lowering and the exact callable
   golden as a backend conformance fixture.
2. Admit AVX2 execution only behind complete CPU plus OS vector-state authority;
   inspect emitted object instructions and execute on a CPUID/XGETBV-qualified
   host.
3. Implement a sibling structural classifier that emits masks for parser-used
   bytes, processes complete blocks only, and uses the scalar algorithm for
   every tail length without over-read.
4. Differentially test masks and parser results against the permanent scalar
   oracle, then route only the admitted accelerated provider. The scalar oracle
   itself remains unchanged.

Until all four steps have evidence, accelerated parse modes continue to report
fallback and no product receipt may claim parser SIMD execution.

### Parser SIMD session ownership prerequisite

The structural parser library must not import compiler-loader executable-memory
functions or bind their runtime externs directly. W^X mapping, authenticated
artifact identity, and callable retirement remain loader/provider lifecycle
responsibilities. Source bytes similarly require a memory-owner lease; a
language `[u8]` value is not a stable native pointer contract.

The integration seam therefore requires two admitted opaque leases supplied to
the structural provider: one callable-kernel generation lease and one stable
source-buffer lease. Session creation copies or registers source bytes once,
pins both generations, and processes every complete 32-byte block without
allocation. The scalar tail handles only the remaining 0–31 bytes. Session
release retires the data lease and unpins the callable; code mapping is shared
per provider generation rather than repeated per source or block.

When capability/admission is false, session creation selects scalar before any
executable mapping or GPU initialization. Until this lower-layer service exists,
the current AVX2 callable remains build/emulation evidence and accelerated
parser modes must retain their explicit fallback receipt.

### Stable execution-domain authority gap

The hosted runtime now has a Linux-first current-thread AVX2 affinity adapter.
It captures the original effective CPU set, restricts the caller to one allowed
CPU, validates the singleton set/current CPU/live AVX2 state, and restores the
original set on release. The Simple driver owns the typed lease lifecycle.
Non-Linux hosts fail closed. Fixed `cpu_set_t` sizing also fails closed when the
kernel mask cannot be represented; a dynamic-mask extension remains required
for very large CPU sets.

The current live AVX2 receipt remains observational and the typed native
invoker remains disabled until it consumes this lease in the same scoped call
and releases it only after native-call/provider-pin drain. The runtime lease
generation is independent, but EnvironmentSnapshot V1 still lacks a separately
owned domain-generation field and canonical CPU-set digest. Those schema joins,
positive Linux runtime tests, and restoration-failure telemetry remain gates.
Process IDs, logical queue worker numbers, and caller-provided booleans are not
execution-domain evidence.

## References

- `doc/01_research/compiler/simd/simple_environment_optimized_dynamic_libraries_2026-09-07.md`
- `src/lib/nogc_sync_mut/composition/provider_contract.spl`
- `src/lib/nogc_sync_mut/composition/provider_generation.spl`
- `src/compiler/10.frontend/core/frontend.spl`
- `src/lib/nogc_async_mut/structural/parse/auto_profile.spl`
- `src/compiler/99.loader/aspect_lifecycle_gate.spl`
- `doc/04_architecture/gpu_dynamic_backend_provider.md`

## 2026-09-08 lexical block-summary foundation

<!-- codex-architecture -->
Structural preprocessing now has a versioned scalar lexical block-summary
contract. A summary is one concrete input-state to output-state evaluation with
quote, escape, comment, newline, and delimiter masks. V1 composition is checked
sequential provenance concatenation when adjacent boundary states match; it is
not a ParPaRaw-style associative parallel-prefix summary. That later form must
encode transitions for every finite input state or an equivalent monoid.
Raw/triple strings, interpolation, custom blocks, indentation semantics, and
block comments are explicit fallback tags in V1; tagged summaries cannot be
promoted as canonical lexer execution. SIMD remains a future equivalent
lowering of this scalar authority, not a current claim.

### Finite transition-table follow-up

Independent block construction uses a fixed 22-state admitted V1 domain and
builds one scalar-oracle transition row per state. Table composition is true
function composition, retains per-block mask provenance, is bounded to 256
blocks, and carries a canonical digest. Unsupported combinations remain outside
the state domain or produce fallback-tagged rows. This establishes the future
parallel-prefix shape but does not claim SIMD execution.

### AVX2 candidate-mask provider boundary

The first vector artifact is intentionally narrower than the lexical state
machine: an x86-64 SysV leaf callable classifies one requested byte across one
exact 32-byte block and returns a `u32` mask. A provider-owned batch may invoke
that primitive for the admitted lexical byte classes, but only the scalar
22-state transition table resolves quote, escape, comment, and fallback state.
The lexical provider requires a distinct artifact/ABI authorization identity;
authorization for the older two-delimiter callable cannot be reused. Mapping,
source addresses, affinity windows, and generation pins stay loader-private.
A separate Win64 artifact is required because its argument registers differ.

### Parser-only build-plan boundary

Parser sibling planning consumes the shared target-codegen profile and exact
feature registry rather than host CPU facts. Host environment identity is
retained as provenance only and cannot affect artifact/cache identity. The
canonical plan binds parser ABI/schema/grammar/program, target ABI and features,
placement, numerical/optimization policy, backend/toolchain, source IR, and
dependency lock. Initial support is baseline plus x86-64-v3/AVX2; v4 is an
explicit unsupported result until its lowering and exact requirements exist.
Planning never reports compilation, emission, mapping, or execution.

### GPU packed-completion proof join

The existing packed DrawIR queue must remain the submission owner. A narrow
provider-specific completion adapter joins its epoch to an immutable
provider-issued receipt containing provider and device-program identity,
device/queue/session generation, packed-content hash, resource-lease generation,
fence completion, optional readback identity, and retirement evidence. The
adapter consumes existing registry, scheduler, backend, and memory owners; it
does not introduce another GPU loader or queue. Routing admission and host
daemon activity remain insufficient without this exact join.

### Frontend advisory insertion

The production binding is split across layers. Layer 10 owns only the typed
request/result port and lazy reference default. A driver adapter acquires the
sealed build-use, requires the selected frontend facet and supported interface,
and opens the loader-owned lexical package. The loader may execute authenticated
32-byte AVX2 candidate classification, but scalar lexical-state resolution and
the reference frontend remain mandatory. Receipts distinguish selected,
admitted, partially executed, fully executed, and fallback states. Package
operations require source/native leases, provider/mapping generations, and
cleanup state all to be valid before preparation and commit.

The first production consumer is a frontend-owned typed advisory port in
`parse_full_frontend_with_scope`, after conditional/domain source transforms
and before `frontend_parse_or_restore`. The frontend layer owns the port and a
no-op reference implementation; loader/provider code binds it through the
composition boundary rather than being imported by layer 10. Candidate masks
may inform preprocessing only. They cannot mutate parser globals, reset pools,
cache keys, interpolation or placeholder ordering, streaming promotion state,
AST, or HIR. Provider failure is an explicit receipt and policy decision before
the canonical parser executes.
## 2026-09-08 backend callback authority addendum

The generic backend completion port is an admission/lifecycle adapter, not a
device oracle. It owns bounded opaque port and callback handles and consumes a
completed callback once, but the concrete backend remains responsible for
creating the underlying fence and retaining the matching resource lease. Until
the Vulkan session exports such an owner-held record, callback facts are
provider assertions and the public epoch remains routing-only. The first
concrete adapter must preserve one identity chain from admitted provider and
device image through queue/session, packed epoch/content and lease to native
fence observation and final retirement.

## 2026-09-08 build-to-publication identity boundary

Compiler build identity and runtime publication identity are separate
authorities. `EnvironmentVariantBuildPlanV1.plan_identity` records target build
intent; the composite `BindingPlanV1.plan_digest` records catalog admission and
runtime bindings. Neither may substitute for the other. An artifact owner must
issue an opaque bridge that proves the selected compiler artifact and exact
bytes became the root runtime descriptor and live provider generation. Cache
receipt issuance is downstream of that bridge; target-codegen, cache lookup,
materialization, and execution receipts remain independent states.

V1 composite publication deliberately has one selected root facet. Its binding
provider, variant, and generation are joined to the recomputed selector result
and unique authenticated root evidence; selected identity is selector-derived.
Multi-facet publication requires a versioned selector projection. The compiler
publication owner invokes canonical admission from original inputs, retains the
result privately, and exposes an opaque revocable token. Build/publication joins
must revalidate that token and the exact live V2 generation authority; a copied
publication value is diagnostic data, never authority.

The compiler side follows the same pattern. A build-plan owner invokes the
canonical planner from original inputs and retains exact per-artifact feature
arenas behind a revocable token. Emission consumes only its owner-derived
artifact projection. Planner-token, publication-token, and generation-pin
liveness are independent conjunctive requirements; losing any one invalidates
the bridge. Backend supported-feature assertions and target text-to-numeric-ID
mapping require their own owners and cannot be inferred from a successful plan.

Backend feature ownership has two levels. A declaration owner can freeze and
revoke a bounded backend/architecture feature set, preventing mutation and
identity substitution. Authenticated acceptance additionally binds backend
provider/version/build, compilation mode, target, toolchain/ISA builder, policy,
and backend-produced evidence. Only the latter may authorize cache publication
or materialization; accepted configuration tokens that are implementation
no-ops cannot satisfy a strict requested-feature contract.

Provider generation publication uses reserve-then-finalize. The generation
owner first issues an opaque exact handle/generation reservation from stable
pre-publication identities. Canonical publication binds that generation and
produces the runtime plan digest. Finalization consumes the reservation and
adds that digest before activation/replacement; only finalized generations can
be pinned. This removes any need to predict an owner counter and keeps failed
publication cancellable without exposing an active provider.

The compiler activation coordinator is the only layer permitted to thread a
reservation generation into publication evidence. Callers provide exactly one
root binding/evidence row with generation zero; the coordinator copies and
fills those rows, admits publication, then finalizes. Its rollback releases any
issued publication token before cancelling a still-pending reservation. The
generic generation manager remains unaware of compiler publication types.

Pins follow the same encapsulation. The coordinator retains raw V2 pins and
cache authority, returning only opaque pin tokens and copied public identity
projections. Build-artifact joins consume coordinator activation/pin tokens and
never receive child publication owners, generation managers, raw pins, or
caller-carried cache authority. Join release and pin release are separate so
resource ownership remains explicit.

The sealed product boundary migrates additively. V1 collect-and-prepare remains
an inert diagnostic compatibility path. The new collect-and-activate adapter
removes raw publication from the result and establishes coordinator-owned
generation publication. A later aggregate sealed owner must hide the child
coordinator/token as well and mediate pin/release; until then the adapter is not
the final product authority.

The aggregate sealed owner is now the intended external lifetime boundary: it
privately retains coordinator activation and pin tokens and returns only its
own opaque handles. This closes child-token exposure, but promotion still
requires owner-visible build-join leases and independently loader-issued
mapping/callable evidence.

Pin truth has two predicates. Admission/new-use requires the activation to be
the current active generation. Continuation/drain requires the exact retained
historical pin and recomputed generation authority, but not current-active
status. Replacement closes new work on the old generation without falsifying
already-issued lifetime ownership.

Build joins are coordinator use leases, not copied proofs. Acquire is allowed
only while the pinned activation accepts new work. The retained lease then
revalidates through historical pin authority across replacement. Pin release
refuses live uses; join release drops the use before pin and activation cleanup.

The final product boundary moves that lease inside the aggregate sealed owner.
The aggregate build-join authority privately owns coordinator pin/use state and
joins planner plus emitted-byte authority to runtime publication identities.
External compiler consumers receive only aggregate join tokens and copied
diagnostics; the current direct-coordinator join is an intermediate adapter.

The first aggregate primitive is a sealed build-use token. It privately owns a
coordinator pin plus use lease, remains drainable across replacement, blocks
activation release, and cleans up use before pin. It is not yet the full build
join: publication/catalog/policy and planner/emission identities still require
one owner-derived aggregate correlation record.

That build-use projection now correlates the canonical publication sidecars,
unique authenticated root evidence, selected root, sole binding, environment,
and provider generation with the historical pin authority. It remains a
runtime admission/lifetime projection; compiler planner/emission facts enter
only in the later aggregate build join.

Aggregate build-use identity is a domain-separated, fixed-width binary digest
over runtime authority plus aggregate and private child token namespaces. It is
always recomputed inside the owner and never accepted alone as capability or
execution proof.

Planner plans use the same lifetime rule. An artifact-index-specific planner
use token retains the exact canonical artifact and target-feature projection;
parent release is busy while uses exist. Join acquisition takes the planner use
before coordinator use and compensates in reverse order on failure.

An emitted artifact receipt has its own lifetime. Issuance retains the exact
planner artifact use, and owner-derived project/live checks bind plan, variant,
artifact intent, cache and target facts. Emission release is blocked by joins
and releases its planner retain before record reclamation.

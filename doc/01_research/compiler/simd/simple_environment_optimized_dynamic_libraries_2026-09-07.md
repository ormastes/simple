# Simple Environment-Optimized Dynamic Libraries
## SIMD tiers, compiler/JIT/AOT specialization, shared parsing, and GPU-resident execution

**Date:** 2026-09-07  
**Repository:** `ormastes/simple`  
**Inspected revision:** `da48c00098e843a0465ba36a5850e664685f6c6c` (main snapshot, commit timestamp 2026-09-07 10:15:22 UTC)  
**Status:** Research-grounded proposal and staged implementation plan. No repository change, executable build, hardware benchmark, or device-conformance result is claimed.  
**Primary implementation:** Simple, using the existing composition foundation and no-GC kernel/plugin direction; platform probes and existing host loader bridges remain narrow adapters.  
**Scope:** Optimize Simple itself and its generated code without requiring a separate whole executable for every environment. Initially, the pure-Simple compiler varies only its parser provider. Generated native distributions specialize dynamic-library boundaries first.

---

## 1. Executive decisions

Build **environment-optimized provider families**, not an independent environment-specific plugin framework. Extend the existing composition/provider admission path with a variant catalog and environment predicates. Keep native, SMF, static, and JIT placements behind the same logical contracts. Reuse the existing GPU provider registry through adapters rather than replacing it in the first patch series. [R07–R12, P03]

Make two decisions at different times:

```text
Admission / load decision:
    Which implementations are compatible, trusted, and callable here?

Execution / placement decision:
    Which admitted implementation should execute this request or resident island?
```

A GPU implementation belongs in the same catalog, but **GPU is not a higher SIMD tier**. GPU execution needs explicit device programs, resource leases, asynchronous completion, and placement decisions. A compatible Vulkan provider does not imply that every frontend or scene operation has a Vulkan implementation.

Adopt these product rules:

| Area | Decision |
|---|---|
| Simple executable | Keep a baseline-safe core and reference path; do not ship a mandatory whole-executable SIMD matrix. |
| Pure-Simple optimization pilot | Build one core plus parser provider variants from Simple source. Keep other compiler providers single-version initially. |
| CPU classification | Use `x86-64`, `x86-64-v2`, `x86-64-v3`, `x86-64-v4` as presets; store exact feature requirements separately. |
| AVX-512 | Support a v4 family and separately gated byte-oriented extensions such as VBMI/VBMI2; benchmark selection rather than assuming wider is faster. |
| Native output | Specialize selected dynamic libraries; keep application entry/control code portable by default. |
| JIT output | Specialize admitted code units for the execution target, independently of the CPU running the compiler frontend. |
| SMF | Select compatible SMF variants using the same catalog; verify actual execution placement and callable ABI, not only magic or symbol presence. |
| Aspects | Reuse lifecycle and publication mechanisms; use typed implementation ports for replacement. Keep observer aspects observational. |
| Parser sharing | One platform and generated grammar authority; separate Simple, SDN, and sosh dialects. Preserve the independent legacy CPU frontend. |
| GPU beyond parsing | Admit typed compute/frontend/render/scene facets; choose whole resident execution islands when that avoids transfers. |
| Rendering | Preserve conservative CPU semantics → GPU rendering and additive GPU-owned scene profiles as distinct products. |
| Configuration | Automatic selection with `prefer`, `require`, and `max` semantics. Overrides never manufacture capabilities or bypass trust. |

No new source-language grammar is necessary for the initial implementation. New CLI/configuration keys and schemas in this document are **proposed**, not existing commands.

## 2. Evidence and current-state audit

This is a targeted source audit, not a claim that every implementation, call site, test, or platform has been examined. Historical plans remain proposals unless current source establishes a narrower implemented mechanism.

### 2.1 Current source findings

| Current source | Observed behavior | Required action |
|---|---|---|
| `src/compiler/30.types/simd_platform.spl` | One detector parses `/proc/cpuinfo`, treats `avx512f` as one AVX512 tier, and contains an explicitly placeholder intrinsics layer. | Retire coarse detection as admission authority; do not mistake its vector API wrappers for native vectorization evidence. [R01] |
| `src/runtime/runtime_simd_dispatch.c` | Existing C detection has GCC/Clang builtins and an MSVC OSXSAVE/XGETBV guard for AVX/AVX2. | Consolidate these useful probes; do not add a third competing feature authority. [R02] |
| `src/runtime/runtime_simd_utf8.c` | Inspected code contains real SSE2, AVX2, and AArch64 NEON counting kernels plus scalar UTF-8 validation. | Reuse algorithms and test corpora; qualify a pure-Simple implementation against these where appropriate. [R03] |
| `src/lib/nogc_sync_mut/simd/host_cpu_config.spl` | Profile constructors, a total numeric rank across x86 and Arm, an SSE4-assuming `x86_baseline`, and fixed 256-bit SVE modeling. | Replace the correctness model with architecture-specific feature predicates and execution-state constraints. [R04] |
| `.../simd/variant_dispatch.spl` | String suffix routing and an eight-slot table; AVX512 maps only to `-mavx512f`; tier spelling differs from the host model. | Preserve compatibility entrypoints but generate typed descriptors and backend feature mappings. [R05] |
| `.../simd/loader_variant_probe.spl` | Constructs `.so` names and records manually marked found flags; x86 sequence can probe AVX512 after a lower preferred tier. | Treat this as scaffold, not safe real loading; replace filename authority with filtered catalog candidates. [R06] |
| `.../simd/variant_manifest.spl` | Platform/tier/path/size/default entries, eight slots, colon-delimited paths; no exact requirements or artifact digest in this entry shape. | Introduce a bounded validated catalog, native path handling, and authenticated artifact identity. [R07] |
| `src/compiler/99.loader/advice_binding_registry.spl` | Actual slot-cell rebind/unbind plumbing; explicitly excludes signature checks and the full aspect state machine from its scope. | Reuse only after typed admission; never treat successful slot patching as semantic replacement proof. [R08] |
| `src/compiler/99.loader/aspect_lifecycle_gate.spl` | Serializes publication, pin/unpin, replacement, and removal; fallback explicitly lacks native concurrency evidence. | Reuse lifecycle invariants and avoid entering this gate inside SIMD hot loops. [R09] |
| `src/compiler/80.driver/driver_provider_contract_v1.spl` | Coarse fixed-width operation contract with generation-local handles; implementation digest zero deliberately does not establish admitted artifact identity. | Use this as the boundary pattern; create a parser-specific facet without exporting compiler-private layouts. [R10] |
| `src/compiler/10.frontend/core/frontend.spl` | Shared compiler/interpreter facade still directly calls the current parser and applies interpolation/placeholder transformations. | First parser insertion point; preserve reset/append/isolation and transformation ordering. [R13] |
| `.../structural/parse/auto_profile.spl` | Returns Scalar with `auto_profile_not_implemented_wave_1`. | Automatic SIMD/GPU selection at this seam remains implementation work. [R14] |
| `src/runtime/runtime_dynload.c` | Native CUDA/Vulkan/Metal provider registry, environment paths, local loading, required operation lists, ABI/backend validation. | Feed admitted artifacts into this registry through an adapter; do not duplicate driver loaders. [R11] |
| `.../gpu/engine2d/draw_ir_runtime_queue.spl` | Legacy SDN/immediate path coexists with deferred and registered packed submission. Packed completion explicitly reports routing-only evidence; real device fence/retirement evidence remains TODO at this seam. | Preserve the new packed path; connect actual provider execution and resource retirement rather than redesigning the queue. [R15] |
| `doc/07_guide/lib/api/dynlib_api.md` | Distinguishes SMF session/registry checks from executable mapping; describes a separate hosted native SFFI path and GUI SMF release acceptance. | Unify selection, not falsely equate native host calls with SMF execution proof. [R12] |
| CPU feature configuration documentation and Rust search result | `SIMPLE_CPU_FEATURES` and `--cpu` presets exist; several Arm features are documented/declared as accepted no-ops in that Cranelift path. | Preserve compatibility, but make unsupported requested codegen features fail clearly in the new strict interface. [R16, R17] |

### 2.2 Concrete regression cases implied by inspected helpers

These are directly testable source-level problems or incomplete contracts. Whether every helper is reachable in production requires call-site tracing.

1. `TierClamp.clamp("avx2", "neon")` compares ranks rather than architecture compatibility. The requested AVX2 rank is lower, so the helper can leave an x86 request on an Arm host. The corrected result must be an architecture mismatch, not a valid tier.
2. An x86-64 baseline without SSE4 must run the baseline provider. The current baseline profile constructor cannot represent that accurately.
3. A missing preferred AVX2 file must not make a later existing AVX512 file eligible without exact feature checks.
4. `avx512f=true` does not establish the complete requirements of a byte-processing v4/VBMI implementation.
5. Unknown tier spellings must fail at configuration parsing; silently assigning scalar rank does not repair the invalid request.
6. Windows paths containing a drive colon must round-trip through the catalog representation.
7. SVE feature presence must not silently imply a 256-bit execution length.
8. A found SMF symbol or successful GPU queue admission must never be labeled executed code.

## 3. Research synthesis and chosen mechanism

| Reference mechanism | Useful property | Limitation for this task | Simple decision |
|---|---|---|---|
| x86-64 psABI levels and glibc-hwcaps | Standard cumulative CPU presets and optimized shared-library deployment. [E01] | Not a portable GPU/SMF policy and not every optional x86 feature. | Reuse level names and exact requirement expansion; optionally export Linux hwcaps layouts. |
| Clang `target` / `target_clones` | Per-function target specialization and runtime multiversioning; tuning is distinct from instruction permission. [E02] | Support and dispatch mechanism depend on target/toolchain; no provider lifecycle or GPU placement policy. | Allow inside a native provider where supported, not as the cross-platform product architecture. |
| simdjson / simdutf | Mature implementation-family dispatch, byte-oriented SIMD, observable selected backend. [E03, E04] | Their parsers/codecs do not supply Simple grammar semantics. | Adopt mechanisms and benchmarking discipline; retain Simple implementations and grammar authority. |
| LLVM ORC | JIT code can be organized into linkage units with explicit resource ownership. [E05] | Does not automatically prove application quiescence or CPU compatibility. | Model JIT artifacts as provider-owned generations; apply the same environment and lifetime contracts. |
| ParPaRaw | Parallel state-summary composition for involved lexical contexts. [E06] | Delimiter-separated parsing is not full Simple/HTML semantics. | Apply the principle to lexing/structural stages; independently qualify the grammar executor. |
| CUDA device image bundles | A bundle may contain architecture-specific device binaries and intermediate device code. [E07] | Device compatibility differs from the host-library ABI. | Separate host control artifact and device image selection. |
| Vulkan features and pipeline caches | Features must be supported and enabled; pipeline caches identify compatible device/driver state. [E08, E09] | A GPU name or API version alone is insufficient admission evidence. | Include enabled features, limits, resource layout, and device/cache identity in contracts. |

The default is **catalog-selected sibling provider artifacts**, with optional internal function multiversioning. This keeps cold alternatives unmapped, supports independent updates, and allows native and SMF placements to use one selection policy. These are architecture goals to benchmark, not claimed measured gains.

## 4. Separate four independent axes

```text
HostExecutionEnvironment
    Where the compiler/runtime/provider code executes now.

TargetCodegenProfile
    Where the generated program or library is intended to execute.

ArtifactPlacement
    static | native_dynlib | smf | jit_materialized | contained_worker

WorkloadExecutionPolicy
    cpu_reference | hybrid_vector_gpu | resident_gpu | auto
    plus domain-specific render/scene requirements
```

An AVX512-capable build machine may compile a baseline x86 library, an Arm SMF, or a Vulkan program. Its parser can use AVX512 without contaminating the output target. Conversely, a baseline host can cross-compile a v4 library without being allowed to execute its tests locally. A remote JIT must use the remote executor's admitted environment, not the compiler service's CPU.

## 5. CPU presets and exact feature requirements

Use standard x86 presets as user-facing names. The preset expansion includes all required non-SIMD features; it is not merely a register-width label. Baseline has SSE2, v2 adds the older extension group, v3 the AVX2-era group, and v4 the defined AVX512 group. [E01]

| Provider family | Required capability summary | Initial use |
|---|---|---|
| `scalar_reference` | Product architecture/ABI baseline; scalar algorithm, not necessarily a ban on baseline compiler instructions | Independent correctness path |
| `x86-64` | Baseline x86-64 contract, including SSE2 | Portable x86 implementation |
| `x86-64-v2` | Complete v2 expansion | Optional 128-bit optimized tier |
| `x86-64-v3` | Complete v3 expansion with OS-enabled AVX state | Main AVX2 parser/text tier |
| `x86-64-v4` | Complete v4 expansion, including AVX512F/BW/CD/DQ/VL and enabled state | AVX512 parser/text tier |
| `x86-64-v4+vbmi+vbmi2` | v4 plus explicitly required optional extensions | Separate advanced byte-shuffle/compaction experiments |
| `aarch64-neon` | Target ABI plus usable ASIMD/NEON capability | Arm baseline acceleration |
| `aarch64-sve` / `aarch64-sve2` | Exact SVE family features and compatible vector-length/state contract | Scalable-vector provider |
| `riscv64-rvv` | Exact supported vector ISA/profile, usable process state, and element/length contract | RISC-V vector provider |

AVX512 is a family of extensions; v4 does not grant every extension listed in Intel's intrinsics catalog. [E01, E10]

### 5.1 Capability acquisition

The loader itself and all pre-admission code use the product baseline. X86 admission checks the complete CPU/OS sequence, including XCR0, before admitting AVX-family code. Reuse tested compiler/runtime probes where possible. A host feature string is diagnostic input, not the sole execution authority. [E01, R02]

On Arm Linux, query OS-reported capabilities and account for per-thread SVE vector length. Prefer vector-length-agnostic kernels; a fixed-length specialization must be bound only on compatible worker threads. On RISC-V Linux, combine hardware probing with vector execution permission/control; do not equate compiled-in V support with usable runtime state. [E11–E13]

On other hosts, implement a platform capability provider with the same output schema. For unsupported or unverified queries, report unknown/unavailable and retain the product baseline. On SimpleOS, privileged providers must establish that the scheduler saves/restores the required vector state before exposing the feature to user programs.

For heterogeneous or restricted CPU sets, bind code to a proven execution domain: either the common usable features of allowed CPUs, or a pinned worker set with an explicit capability contract. A later widening of affinity cannot silently invalidate that contract.

### 5.2 Instruction permission is not performance preference

Store separately:

```text
required_features       # legality of the emitted code
optional_tuning         # scheduling/cache/microarchitecture preferences
preferred_vector_width  # algorithm/codegen preference, not permission
vector_length_contract  # scalable, minimum, or exact when unavoidable
```

A v4 machine may select an AVX2 provider for latency, power, small inputs, or measured contention. AVX512VL also makes lower-width AVX512 implementations possible when their exact features are present. Selection should be learned from end-to-end workload measurements, not CPU branding or a fixed widest-first rule. Do not publish a v4+extra artifact as plain v4 merely because the build happened on a machine with both.

## 6. Proposed environment-optimized provider architecture

```text
Application / Compiler / Interpreter / Simple Web / Simple 2D
                         |
              typed logical provider requests
                         |
     existing composition + kernel_plugin lifecycle
        |                |                    |
   EnvSnapshot      VariantCatalog      Policy / receipts
        +----------------+--------------------+
                         |
              eligibility + dependency resolution
                         |
               generation-pinned BindingPlan
                         |
       +-----------------+------------------+
       |                 |                  |
   native loader     SMF adapter       JIT/static adapter
       |                 |                  |
       +----------- typed facet slots ------+
                         |
              domain execution / offload planner
                         |
      CPU reference / CPU SIMD / admitted GPU island
                         |
     existing compute/Engine2D/Object VM/SimpleRing services
```

**Kernel responsibility:** identity, bounded catalog decoding, admission, dependency closure, lifecycle, capability authority, cancellation, receipts, and dense binding slots.

**Provider responsibility:** parser algorithms, vector kernels, compiler transforms, GPU backend translation/execution, rasterization, style/layout, and domain-specific cost estimates.

**SOSIX responsibility:** capabilities for platform access, libraries, input, display, timers, file/network and related host services. It does not absorb parser semantics, DrawIR, layout, or raster algorithms. [P02, P03]

### 6.1 Proposed records

The following is schema notation, not new Simple syntax or an implemented ABI:

```text
EnvironmentSnapshot
  execution_arch, os, abi, object_format, endian, pointer_width
  hardware_features, os_usable_features, policy_allowed_features
  cpu_execution_domain, vector_state_contract
  load_permissions, gpu_devices, snapshot_generation

VariantDescriptor
  provider_id, variant_id, contract_id, contract_version, abi_digest
  semantic_profile, grammar_or_program_digest
  placement_kind, artifact_digest, artifact_location
  required_cpu_features, required_os_state, target_triple
  required_device_api, required_device_features, device_limits
  memory_domains, resource_layout_digest, numerical_contract
  dependency_requirements, assurance_receipt, startup_budget

BindingPlan
  composition_digest, environment_generation, provider_generations
  dense_facet_slots, dependency_lock, policy_digest
  selected_variant_ids, rejected_candidate_reasons
```

Do not overwrite V1 wire structures in place. Add negotiated descriptors/facets or a new version with explicit adapters. Use bounded arrays/offset tables rather than eight hand-expanded slots. Reject duplicate identities, corrupt lengths, integer overflow, impossible feature combinations, unknown required fields, incompatible ABIs, and missing mandatory operations before publication.

### 6.2 Eligibility before ranking

For candidate `v`, environment `e`, and request `r`:

```text
eligible(v,e,r) =
    architecture_and_abi_match
    AND artifact_and_dependency_identity_verified
    AND exact_required_features_are_usable
    AND execution_state_contract_satisfied
    AND contract_and_semantic_profile_match
    AND requested_effects_and_memory_domains_allowed
    AND required_device_features_enabled
    AND resource_limits_and_lifetime_supported
```

Only eligible candidates participate in preference ranking. Neither a filename suffix, a benchmark score, nor a manual preference may bypass eligibility.

### 6.3 Safe binding and replacement

Discover → inspect inert metadata → validate identities and dependency closure → check environment requirements → map/load → query typed descriptor → create bounded session/resources → self-check → publish generation → execute → drain → retire.

Native constructors can run before `dlopen` returns. Therefore, metadata/CPU/trust validation must precede opening the candidate, not be delegated solely to a function exported by that candidate. A signature/descriptor query after load confirms compatibility but cannot protect against code already run during load. [E14]

Require inert first-party initialization where practical. For arbitrary native dependencies, treat loader execution as trusted code admission; untrusted extensions need process isolation. Bind to immutable digest-addressed artifacts and validate the exact bytes/dependency closure used, avoiding path-replacement races. Native dependency search policy must not quietly replace admitted dependencies with unrelated system or working-directory files.

For parser calls, pin one provider generation per session/request or batch. For GPU work, pin host provider, device program, descriptor layouts, buffers, callbacks, and completion objects until true retirement. Cancellation is not proof that submitted work stopped.

## 7. Aspect dynload: what to reuse and what not to reuse

Aspects are not inherently read-only. Current Simple code can rebind a joinpoint slot to another target. However, the inspected registry explicitly excludes signature checking and complete state-machine semantics from its own scope. That is useful machinery, not sufficient authorization for arbitrary implementation substitution. [R08]

| Mechanism | Appropriate use | Decision |
|---|---|---|
| Observer aspect | Counters, sampled traces, input/output checks, fallback auditing | Keep observational; no hidden implementation replacement. |
| Verification aspect | Run a CPU oracle and compare normalized output under explicit policy | Useful during qualification; not enabled on every production call. |
| Typed provider port | Select one equivalent parser/kernel/render implementation | Primary optimization mechanism. |
| Declared around/replacement aspect | Legacy integration where a provider seam cannot yet be introduced | Temporary adapter; resolve at load/seal time to the same typed slot. |
| Arbitrary text patch/hot interception | Rewrite undeclared functions and assume matching calling conventions | Not the default environment-optimization design. |

Replacement admission checks signature/ABI, ownership, effects, error behavior, determinism/numerical policy, capacity requirements, and generation lifetime. An observer permission must not imply permission to change program behavior. Each active implementation family has one selected implementation; ordered observer chains are a separate axis.

Prefer read-only function tables after startup and data-pointer publication for a new generation, rather than executable-page rewriting for ordinary selection. No pointcut matching, dictionary lookup, symbol lookup, environment parsing, or lock acquisition per token/pixel. Dynamic mode pays at a coarse call boundary; static-sealed mode can use generated direct bindings. “Low overhead” must be measured, not renamed “zero overhead.”

## 8. Build products: Simple itself, native libraries, SMF, and JIT

### 8.1 Pure-Simple compiler profile

```text
simple-core                    one baseline-safe admitted executable
parser.reference               permanent independent CPU frontend
parser.canonical.baseline      canonical runtime, once parity is ready
parser.canonical.v3            Simple-built parser specialization
parser.canonical.v4            Simple-built parser specialization
parser.canonical.v4-vbmi2      optional, explicitly gated
parser.canonical.arm/riscv      independent platform builds
```

The initial “parser-only variation” profile permits duplication of private parser kernels, not the entire compiler or every standard library. Shared grammar tables and immutable syntax programs should be stored once where practical. A parser variant change rebuilds its artifact and necessary private dependencies; grammar or interface changes have their own explicit invalidation scope.

Pure Simple does not automatically imply that the interpreter executes native SIMD instructions. Each backend must prove vector lowering/extern legality and actual emitted instructions. When unavailable, build a truthful baseline artifact and report the optimized target unsupported. Do not substitute a scalar loop and label it an AVX512 execution result.

The first compiler rebuild establishes the stable provider seam. Subsequent parser algorithm/tuning edits normally update only parser artifacts and composition locks. Full bootstrap remains the explicit toolchain qualification operation from the previous plan, not the default cost of every new CPU variant. [P03, P04]

### 8.2 Native generated libraries

Default deployment shape:

```text
application executable      baseline control path
logical library catalog
  library.baseline          native dynamic artifact
  library.v3                native dynamic artifact
  library.v4                native dynamic artifact
  library.device-programs   optional device bundle
```

Use one baseline facade or application import binding to select the implementation. The application must not statically depend on the v4 artifact merely because it was built on a v4 host. The fast kernels and their private helpers are the versioned unit, not every exported function by default.

Prevent LTO/inlining from pulling high-ISA code into the baseline loader or facade. Check init routines and dependency closures as well as exported kernels. Keep allocator ownership, TLS, exception/unwind policy, global state, and callback ABI explicit. Do not allocate in one runtime/CRT and free through an incompatible one.

Clang function multiversioning can be an optional implementation technique *inside* a provider. Native sibling selection remains the common cross-platform deployment model. Use glibc-hwcaps as an optional packaging adapter; it must not disagree with explicit Simple selection or bypass catalog policy. [E01, E02]

### 8.3 SMF variants

SMF is a packaging/loading dimension, not a claim of architecture neutrality. Every variant declares whether its payload is target-native code, a supported interpreted form, or a materializable program. Native-code SMFs carry target ISA/ABI requirements just as native dynlibs do.

Keep the same logical provider ID and negotiated facet across native and SMF placements. The adapter is responsible for callable export resolution and session ownership. The catalog must distinguish “metadata admitted,” “symbols resolved,” “mapped executable,” “typed callable,” and “actually executed.” Current SMF session/registry evidence does not collapse these states. [R12]

Preserve the existing pure-GUI SMF release identity and acceptance rules. A hosted bridge calling an extracted native payload may be a valid SMF packaging strategy, but the full package validation and intended SMF path must be exercised. A successful unrelated `.so` call is not substitute evidence.

Production startup does not auto-compile a missing optimized provider. Auto mode may choose an installed admitted baseline; required mode fails. Existing development dynSMF compile requests remain an explicit development workflow and are never used to mask a missing release artifact.

### 8.4 JIT

Construct a target description from the actual executor environment and policy. Generate specialized code in bounded compilation units, with baseline as required by the product. Import shared kernels through selected provider slots; do not recompile the same codec/parser helper in every JIT unit.

A compiled unit records the exact features actually permitted/required, optimization and numerical policy, compiler/backend digest, target ABI, dependency bindings, and resource generation. The execution engine owns publication and retirement. LLVM ORC's linkage/resource model is a useful implementation reference, not a requirement to replace Simple's other JIT backends. [E05]

An optional later tiered JIT can promote hot units after profiling. No global AVX512 rewrite, no invisible recompilation of all resident units when an unrelated provider changes, and no direct call to retired code. SFFI call boundaries must use typed adapters rather than treating all exports as `i64` calls.

### 8.5 Host portability matrix (implementation targets, not passing-test claims)

| Host/product | Native placement | SMF placement | Environment adapter responsibility |
|---|---|---|---|
| Linux / compatible ELF hosts | Existing hosted shared-library adapter | Validated native-payload or supported executable SMF adapter | Exact process ABI, OS-usable ISA, permitted CPU set; optional hwcaps packaging |
| Windows | DLL host adapter with typed ABI | SMF-to-callable host adapter with explicit acceptance evidence | Windows ABI/runtime ownership, usable vector state, controlled dependency search |
| macOS | Native dynamic-library adapter | Existing intended SMF packaging/call bridge, with full artifact checks | OS/architecture/code-loading permissions and available device backend |
| FreeBSD | Native shared-library adapter | Same logical SMF contract with a separately qualified host adapter | Do not assume Linux feature-query interfaces exist; qualify OS state and loading behavior |
| SimpleOS | Existing supported executable loader/provider placement | Native SMF contract | Scheduler vector-state preservation, capability authority, actual executable mapping |
| Browser/Wasm product | No assumption of native process dynlib loading | Only an explicitly supported module/container adapter | Engine-exposed SIMD/GPU capabilities and module binding, not host CPUID/dlopen |

The product can share catalog/schema/policy code across these hosts without sharing their binary ABI. A macOS or Windows artifact is not an ELF sibling with a renamed suffix. Artifact selection must precede choosing the corresponding loader adapter.

## 9. Generated-code SIMD optimization pipeline

Library selection only helps when the chosen artifact contains a useful implementation. Add an auditable target-capability contract to optimization and lowering rather than treating an ISA flag as a vectorization guarantee.

```text
shared semantic IR
  → loop and data-access normalization
  → alias/ownership/effect checks
  → vectorization candidates + legality proofs
  → target-specific cost choice
  → fixed-width/scalable-vector lowering
  → instruction legalization and safe tails
  → artifact requirement verification
```

Preserve equivalent scalar lowering. Existing MIR/vector infrastructure should be adapted after inventory; do not create a parallel IR just for variant packaging.

The vectorizer must account for loop-carried dependencies, aliasing, alignment, integer overflow policy, reduction order, floating-point contraction, gather/scatter costs, and bounds-safe tail handling. `nogc` and ownership information can supply useful evidence but are not automatic no-alias proofs. Under strict numerical semantics, do not silently reassociate floating-point reductions or permit new approximations. A relaxed numerical variant has a different declared semantic profile.

For JIT latency, begin with already recognized profitable loops and prebuilt kernel calls. More expensive analysis is an explicit higher optimization tier. For AOT dynlibs, permit more costly optimization/PGO and CPU tuning, while keeping the public ABI unchanged. Record missed-vectorization reasons so an AVX512 build whose hot path remains scalar is visible.

### 9.1 Artifact verification

Inspect the emitted executable sections and compiler target metadata. Verify the baseline host/facade and all early initialization paths remain within their declared target. Compare declared requirements with backend-produced requirements; include transitive private dependencies. Disassembly is an important cross-check, not a complete proof for arbitrary embedded data or unsupported decoders.

Report separately:

```text
requested target features
backend accepted features
artifact declared requirements
emitted vector instructions / selected kernels
executed implementation identity
```

Never infer the last two facts from a command-line option alone.

## 10. Shared parser integration and SIMD algorithms

The existing parser plan remains authoritative: one shared runtime and cache protocol, distinct dialects, and an independently maintained legacy CPU frontend. Valid-source GPU work may extend through direct Parsed HIR and local semantic work; global-name resolution and syntax recovery remain explicit CPU stages. [P01]

### 10.1 Two CPU paths, not one renamed oracle

- **Legacy CPU frontend:** current full parser behind the existing frontend facade. Preserve independent implementation diversity and normalized comparisons.
- **Canonical runtime:** scalar, SIMD, and GPU executors consume generated lexical, structural, grammar, and action programs. This is the common per-region fallback implementation.

The normal product may initially use the legacy frontend with selected SIMD preprocessing primitives. Switching the default to the canonical provider requires full parity. A selector must not promote an incomplete canonical implementation merely because its manifest says AVX512.

### 10.2 Provider granularity

Export batch/session operations, not an indirect call per character or token:

```text
FrontendFacet
  create_session(dialect, grammar_digest, source_snapshot, budget)
  plan_regions(session, request)
  execute_batch(session, region_range, output_reservation)
  inspect_receipt(session, operation)
  release_session(session)
```

These are logical operations mapped to generated typed descriptors. Native pointer-rich AST/HIR structures do not cross a stable dynamic boundary. Use borrowed immutable byte views where the ABI permits them, or registered handles plus offset/count ranges. Flat output arenas and adapter-owned native objects retain clear lifetimes.

A per-session immutable operation table binds the chosen CPU implementation. The reference implementation and optimized implementation may use different algorithms while producing the same canonical spans, token values, node order, and diagnostics under the declared profile.

### 10.3 SIMD work order

| Stage | CPU SIMD strategy | GPU relationship | Qualification requirement |
|---|---|---|---|
| Encoding/UTF-8 | Byte classification, continuation checks, vector conversion where required | Batch conversion/validation kernels | Exact malformed-sequence locations and source mapping |
| Lexical masks | Classify bytes, construct quote/escape/comment masks, compose cross-block state | Parallel chunk-state summaries and scans | Same lexical state at every chunk boundary |
| Structure | Delimiter/line/indentation indexes and compact candidate positions | Count/scan/emit structural arrays | Identical matched spans, nesting and indentation behavior |
| Tokenization | Operate on spans, compact starts/ends, classify tokens without copying lexemes | Region/batch token production | Stable token identities and text-backed spans |
| Region map | Compute independent function/statement/expression regions | Work-table construction | Correct dependencies and deterministic ordinals |
| Grammar execution | Vectorizable table/state operations across independent regions; scalar within irreducibly serial subregions | Generated grammar executor over regions | Full dialect conformance, not only a lexical toy |
| Parsed HIR/local work | Disjoint indexed emission and eligible batch operations | Direct flat Parsed HIR and local binding/constraint work | Exact references, ranges, semantics and provenance |
| Global binding/recovery | CPU-owned | Explicit compact CPU task handoff | Never mislabeled as accelerated failure |

For a vector width `W` bytes, bulk work handles complete blocks and a safe final tail. Do not read across a guard page merely because an algorithm would like padding. A padded-source API must explicitly allocate/validate the padding contract. Test every tail length and boundary condition for each width.

Chunk state must cover the real Simple lexical rules, including indentation, interpolation, raw/triple strings and custom blocks. Do not copy JSON quote rules and assume they define Simple. Lexical state-summary composition is a reusable technique, not permission to approximate the grammar. [P01, E06]

### 10.4 Parser platform consumers

Compiler, interpreter, REPL, SDN, sosh, and editor integrations request the same platform but retain their dialect/output needs. Native Tree-sitter may remain a separate execution runtime whose grammar is generated from the same authority; it is not forced through the compiler's semantic HIR ABI.

Preserve the current frontend facade's interpolation and placeholder transformations until their equivalents are integrated and tested in canonical actions. Reset/append/isolation behaviors are acceptance tests, not optional refactoring details. [R13]

### 10.5 Failure and commit

Use immutable source snapshots, count/scan/reserve/emit, disjoint output ranges, and private staging. On malformed/unsupported/failed regions, emit typed reason and work tags compatible with the predecessor plan. Only validated output enters the semantic cache or downstream compiler state. An execution failure after partial writes must not leak a partially trusted HIR.

## 11. GPU programs as environment-optimized artifacts

A GPU variant consists of two separately checked parts:

```text
host control provider
  native or SMF library, callable in this process
  creates/query sessions and submits through existing services

logical device program bundle
  one or more compatible device images
  declared entrypoints, resource layouts, feature requirements, effects, limits
```

Possible image formats include Vulkan SPIR-V, CUDA PTX/cubin, native Metal libraries, Direct3D shader artifacts, or an admitted browser shader module. The catalog's format registry must be extensible; implementing every adapter is not a prerequisite for the CPU/parser pilot. CUDA's documented device bundling is precedent for this separation. [E07]

A native host library cannot be called directly by a GPU shader. Device code must resolve to device-callable implementations, and host effects must go through explicit capability requests. A host SMF container with a shader payload does not make host pointers or arbitrary syscalls device-legal.

### 11.1 Generality beyond parsing

Admit domain facets rather than a single giant GPU ABI:

| Facet | Example work | Contract boundary |
|---|---|---|
| Frontend | Validation, structural indexing, token/region maps, valid-source grammar execution | Source/grammar/output arena contracts |
| Compute | Scans, reductions, sorting, compression, image operations, numerical kernels | Typed buffer/effect/numerical contracts |
| Compiler continuation | Local semantic batches, selected graph/table transforms, backend-specific experiments | IR/schema and dependency contracts; global binding remains separately owned |
| Render | Path preparation, binning, rasterization, effects, composition | Existing DrawIR/Prepared2D/Engine2D contracts |
| Scene | Hit testing, event programs, mutation, selector/cascade/layout frontiers | Scene generations, QueryIR/MutationIR, supported feature profile |

An optimization provider can expose several facets under one artifact generation. Avoid a separately loaded library and GPU context for every small kernel. Conversely, do not make the core load every optional renderer/backend merely to run a parser.

### 11.2 GPU capability admission

Check the selected physical device, API support, actually enabled logical-device features, required limits, subgroup behavior, address spaces, resource layouts, memory budget and code format. Vulkan requires feature enablement at logical-device creation; late-loading a plugin must not pretend an unsupported or unenabled feature became available. [E08]

Resolve a product's required capability closure before creating the shared device where practical. A later optional provider may be rejected or use a deliberately separate device/session; it must not silently recreate a live shared device and invalidate other providers.

CPU control artifacts and GPU kernels may have independent tuning variants. Avoid compiling every combination into separate full bundles. Factor shared host control, grammar/program tables, and device payloads using dependencies unless whole-island fusion requires joint compilation.

## 12. Offload selection is a graph and residency problem

Library selection determines an admitted implementation set. The domain planner then chooses among that set for the current workload. Its inputs include input size/shape, current data placement, queue occupancy, compilation/cache state, output requirements, latency budget, required semantics, and resource limits.

A useful explicit model is:

```text
CPU cost = CPU setup + CPU execution

GPU cost = provider/device warmup + upload + enqueue/launch
         + GPU execution + synchronization + required readback
         + conversion / ownership-transition cost
```

Measure those terms independently. For a long-lived session, amortize initialization over the actual expected work; never hide cold start in a throughput-only result.

For a pipeline, minimize node execution costs **plus** costs on edges crossing memory/execution domains. Independently choosing the fastest implementation of each stage can be slower than keeping a slightly slower chain resident.

Examples:

- A tiny REPL edit can remain CPU scalar/SIMD even with a GPU installed.
- A batch build can use GPU lexical/grammar stages when transfer and queue costs are amortized.
- A resident frontend can hand only compact global-binding/recovery tables to the CPU, then continue on the GPU.
- A GPU WebScene should normally keep event → mutation → style → layout → DrawIR → raster data resident instead of bouncing each facet through host memory.

Use deterministic conservative defaults before calibration exists. Calibration is an explicit bounded command or evidence-install workflow, not an arbitrary hidden benchmark during application startup. Different latency/throughput/energy policies can select different eligible variants.

## 13. Unify Simple GPU, Simple Web, and Simple 2D

Preserve the checked-in rendering plan's two semantic ownership profiles. [R18, P02]

```text
Conservative rendering:
    CPU event/style/layout owner
      → canonical DrawIR
      → selected Engine2D CPU/SIMD/GPU rendering provider

GPU-resident scene:
    normalized input/resource packets
      → admitted GPU event and mutation programs
      → QueryIR/style/layout frontiers
      → packed encoding of existing DrawIR
      → selected Engine2D raster/composite provider
      → host-mediated platform presentation
```

The second path is not established merely by making the last raster function dynamic. It needs supported scene semantics, device data structures, bounded effects, and proof that the earlier stages executed on the device. Current WebScene documentation correctly calls this additive and experimental. [R18]

### 13.1 Shared ownership

- **Composition/kernel-plugin:** artifact admission, provider generations and typed slots.
- **GPU service/backend:** actual device/queue/program/pipeline/fence ownership and execution facts.
- **Object VM/memory leveling:** arena placement and resource leases, shared across parser and render consumers.
- **SimpleRing:** asynchronous request/completion and cancellation transport; no second Future ABI.
- **Frontend/scene/render providers:** domain algorithms and deterministic commit semantics.
- **SOSIX:** input, display, files, clocks, network and related host services.

Reuse one compatible device service where practical, but not necessarily one queue: separate interactive rendering and bulk compiler work by policy/budget, with shared accounting and explicit priority limits. Do not assume portable arbitrary GPU preemption. Bounded kernels/batches and backpressure must prevent the compiler from monopolizing the rendering lane.

### 13.2 Reconcile the latest packed queue code

The saved September 5 report identified a text-serialization/immediate-drain route. Current source now additionally provides registered packed submission and deferred completion. The plan must retain that progress. [P02, R15]

The remaining integration target at this seam is stronger: connect the selected provider identity, actual device submission, fence completion, and resource retirement to the epoch receipt. The compatibility path explicitly uses no-device-evidence receipts; do not change a boolean to “true” without real evidence.

For GPU-required profiles, a refused or failed scene must report the failure; it must not secretly run event/style/layout on the CPU. For balanced profiles, whole-island fallback is allowed only with a state/commit contract and an explicit reason. Retrying an uncommitted pure parser batch is different from replaying an already committed input event or network effect.

### 13.3 Host work remains visible

Native window/input/driver submission/presentation services still execute host API calls. Vulkan exposes submission and presentation through host entrypoints. The target is GPU-resident admitted application work with bounded host control, not a misleading universal “zero CPU” claim. [E15, E16]

Measure semantic residency, data residency, submission autonomy and scheduling assurance independently. A short `main()` is an API property, not an offload measurement.

## 14. Configuration, overrides and explainability

### 14.1 Precedence

Apply non-overridable hardware/OS/trust/capability limits first. Within that admissible set, preference precedence is:

```text
explicit invocation API / CLI
  > permitted process environment
  > project configuration
  > user configuration
  > administrator defaults
  > built-in auto policy
```

Administrator restrictions are not merely defaults: enforced restrictions are intersected with every level and cannot be widened by CLI or project input. Elevated/service profiles may disable environment-controlled library paths entirely.

### 14.2 Three distinct override meanings

| Override | Meaning | Unsupported behavior |
|---|---|---|
| `prefer=v4` | Choose the requested eligible variant when available | Select an admitted fallback and record why |
| `require=v4` | This implementation/capability is part of the request | Fail explicitly; never silently clamp |
| `max=v3` | Exclude candidates exceeding the allowed x86 feature preset | Still apply exact predicates; do not cross architectures |

A maximum ISA preset is not a maximum vector-width setting. A 256-bit AVX512VL kernel can still require v4 features. Expose width preference separately.

### 14.3 Proposed CLI examples

These examples describe the intended interface, not commands verified in the current release:

```sh
# Inspect usable environment and the actual selected provider.
simple env explain --provider parser

# Portable compiler control path, CPU parser capped at v3, no GPU.
simple compile app.spl --host-cpu-max=x86-64-v3 --offload=off

# Require a qualified parser implementation for a controlled test.
simple compile app.spl --parser-impl=require:x86-64-v4

# Generate several native dynlib artifacts; do not multiply the executable.
simple build --emit=dynlib --target=x86_64-linux-gnu \
  --env-variants=x86-64,x86-64-v3,x86-64-v4

# Pure-Simple compiler rebuild: only parser family varies.
simple build --product=simple --implementation=pure-simple \
  --env-variant-scope=parser

# Preserve explicit CPU semantic ownership or require GPU scene ownership.
simple run showcase.spl --scene-profile=gpu_render
simple run showcase.spl --scene-profile=gpu_scene_required
```

Proposed environment keys: `SIMPLE_HOST_CPU_MAX`, `SIMPLE_PARSER_IMPL`, `SIMPLE_OFFLOAD`, and a catalog/policy path permitted by deployment policy. Keep the existing `SIMPLE_CPU_FEATURES` compatibility meaning on the **generated-code target** side. Its documented no-op feature tokens must not be interpreted as proof that a strict new request succeeded. [R16, R17]

### 14.4 Explain receipt

```text
provider = parser
requested = prefer:x86-64-v4
selected = parser.canonical.x86-64-v3
selection_phase = bound
artifact_digest = ...
contract_digest = ...
environment_generation = ...
reason = v4_installed_but_not_qualified_for_this_grammar
host_usable_features = ...
target_codegen_profile = aarch64-...
gpu_loaded = false
```

A later execution receipt adds actual implementation identity, input/output hashes, work counts, timings, fallback reasons, transfer bytes, and device completion evidence. Admission and execution receipts must remain distinct.

## 15. Cache and rebuild identities

Maintain separate namespaces:

| Cache | Identity inputs | Sharing rule |
|---|---|---|
| Semantic parse/HIR | Source snapshot, encoding map, dialect/grammar/actions, options, schema and semantic profile | Backend-independent only after equivalence certification; provenance kept separately |
| Native/SMF/JIT code | Source/IR digest, compiler/backend digest, target triple/features, optimization/numerical/ABI policy, dependency locks | Never reuse solely because CPU names look similar |
| Device program | Kernel/IR digest, target API/code format/features, resource layout and toolchain | Compatible device images can be reused under verified predicates |
| Driver/pipeline cache | Program and pipeline state plus required device/driver compatibility identity | Invalidate or ignore incompatible cached driver data [E09] |
| Selection/performance profile | Environment, workload bucket, measurement policy, provider digest, calibration evidence | Never authorizes an otherwise incompatible artifact |

Store exact execution provenance even when canonical semantic results share a cache. A grammar edit invalidates semantic parse results; a performance-only backend change need not do so after parity. A numerical-policy change can alter semantics and must not share a strict cache entry. A driver cache is acceleration data, not an artifact-trust authority.

Build caches factor common source/IR/grammar from target code. Avoid an uncontrolled Cartesian product of CPU model × GPU model × OS × artifact format × grammar. Publish a small preset matrix and independently version optional device bundles.

## 16. Lifetime, concurrency, memory and safety requirements

A provider generation cannot retire while referenced by a CPU call, suspended continuation, direct JIT relocation, callback, session object, GPU command, descriptor/pipeline, or in-flight buffer lease. GPU completion and resource retirement are separate from user-visible cancellation. Pin at coarse session/batch boundaries where this is sufficient, not once per scalar operation.

Default replacement policy for production is new-session cutover. Existing sessions finish on the old generation. Hot state migration is optional and requires an explicit serialization/schema transition; matching function names are not enough. Static/critical profiles may disallow replacement entirely.

Bound catalog storage, pending loads, outstanding operations and device allocations. Command startup declares static/pool/dynamic budget modes consistent with the existing memory planning direction. Keep application allocator growth out of the static-pool hot path; report driver-internal allocation separately.

Validate lengths, alignment and generation of every shared arena reference. GPU kernels never receive arbitrary host pointers. Define endianness and fixed-width fields for persistent/wire representations. Process-local opaque handles must not be persisted as reusable addresses.

Do not use signal trapping of arbitrary illegal instructions as the normal feature detector. Negative tests may use a controlled subprocess/emulator, but production eligibility comes from verified environment contracts.

## 17. Migration plan and parallel-agent work packages

Implementation agents own feature work and a corresponding layer expert reviews their boundary changes. One contract owner controls canonical descriptor schemas, feature IDs, ABI version changes and generated registries. Other agents consume generated interfaces instead of independently editing them.

| ID / owner | Work | Dependencies | Merge acceptance |
|---|---|---|---|
| ENV-00 / evidence owner | Pin baseline, trace production callers of current SIMD/variant helpers, inventory compiled vs stub code, record real test commands | None | Truthful current-state matrix and reproducible baseline artifacts |
| ENV-01 / contract owner | Environment/target split, exact feature registry, descriptor schema, ABI-version policy, reason codes | ENV-00 | Generated schemas; unknown/incompatible records rejected; no V1 layout break |
| ENV-02 / host layer | Consolidate CPU/OS probes, affinity contract, Arm scalable length, RISC-V permissions, baseline-safe adapters | ENV-01 | Synthetic feature tests plus actual hosts; no cross-architecture rank |
| ENV-03 / composition layer | Catalog decoding, dependency locking, eligibility, policy precedence, dense binding plan | ENV-01 | Deterministic selection; prefer/require/max semantics and invalid catalog tests |
| ENV-04 / loader layer | Native and SMF adapters; metadata-before-load; actual callable evidence; generations | ENV-02,03 | Same contract through both formats; incompatible constructor-bearing candidate never loaded |
| ENV-05 / compiler layer | Target feature legalization, JIT/AOT cache keys, dynlib build matrix, ISA boundary checks | ENV-01 | Output target independent of host parser; native-code requirements verified |
| PAR-01 / frontend layer | Add provider seam at shared frontend facade; legacy adapter and session semantics | ENV-01,03 | Existing compiler/interpreter tests unchanged in reference mode |
| PAR-02 / parser feature | Canonical scalar engine/dialect conformance and normalized oracle comparisons | PAR-01 | Real Simple/SDN/sosh parity for declared coverage; incomplete coverage cannot become default |
| PAR-03 / SIMD feature | Pure-Simple baseline/v3/v4 kernels, tails, table/mask algorithms, backend lowering | ENV-05, PAR-02 | Actual vector code and cross-variant exactness; parser-only rebuild scope |
| GPU-01 / backend layer | Adapt existing GPU registry, device images, enabled-feature queries, device/fence receipts | ENV-04 | Actual device execution with negative controls; no duplicate registry |
| GPU-02 / frontend feature | GPU regions, private staging, tagged CPU handoffs, direct Parsed HIR and continuation | PAR-02, GPU-01 | CPU-owned global binding/recovery preserved; deterministic differential results |
| GPU-03 / scheduler-memory layer | Shared resource leases, residency-aware island planner, budgets and queue fairness | GPU-01 | No use-after-retire; measured transfer/cold-start costs; UI not starved by compile batches |
| REN-01 / rendering layer | Connect current packed epoch path to real backend fence/completion and provider generation | GPU-01,03 | Packed data consumed by actual device; correct retirement, no text hot-path regression |
| REN-02 / scene feature | Wire rendering-only and resident-scene facets under existing DrawIR/QueryIR/MutationIR contracts | REN-01 | Required profile has no silent CPU scene fallback; same visible semantics |
| OPS-01 / product owner | CLI/config compatibility, explain receipts, packaging and release profiles | ENV-03–05 | Native/SMF and baseline/optimized installs work without hidden production compilation |
| QA-01 / independent reviewer | Fuzzing, failure injection, hardware matrix, repeatable perf evidence, rollout gates | Starts at ENV-01 | Evidence-based promotions, not manifest labels or test counts alone |

Critical path:

```text
contract + probes
  → safe native/SMF selection
  → legacy parser seam
  → canonical scalar parity
  → pure-Simple AVX2/AVX512 parser variants
  → production parser-only rollout

GPU registry adapter + real fence evidence
  → shared lifetime/residency planner
  → GPU frontend and packed rendering integration in parallel
  → resident-scene expansion
```

The CPU/parser pilot must not wait for a full GPU browser. GPU-only work must not destabilize baseline bootstrap or CPU-only products.

### 17.1 Suggested source ownership

Reuse current files and add versioned modules under the existing architecture:

```text
src/lib/nogc_sync_mut/composition/
    environment and variant schema/codec/validation extensions

src/lib/nogc_async_mut/kernel_plugin/
    environment admission, binding, generation and receipt integration

src/lib/nogc_sync_mut/simd/
    compatibility facades for current tier/manifest/dispatch helpers

src/compiler/10.frontend/core/frontend.spl
    stable provider invocation seam

src/lib/.../structural/parse/
    canonical runtime and qualified CPU/GPU executors

src/compiler/...codegen... and compiler_rust/.../codegen/
    target descriptor adapters and requirement verification

src/runtime/runtime_dynload.c and native/SMF host adapters
    compatibility bridge to admitted artifact selection

src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl
    current packed path and real provider evidence integration
```

The ellipses intentionally avoid claiming a new authoritative directory layout where existing module ownership still needs inventory. Generated registry output must not become a frequently hand-edited merge bottleneck.

## 18. Acceptance and test matrix

### 18.1 Correctness and admission

| Test group | Required cases |
|---|---|
| CPU classification | True x86 baseline; each v2/v3/v4 missing-feature case; AVX512F without BW/VL; optional VBMI absent; unknown tier; x86 request on Arm |
| OS state | CPU advertises extension but OS execution state unavailable; SVE length changes; RISC-V vector permission off; restricted/changed worker domain |
| Override semantics | `prefer` falls back visibly; `require` fails; `max` limits features; width preference does not grant ISA permission; administrator restriction wins |
| Catalog | Duplicate IDs, corrupt offsets, oversized counts, Windows paths, mixed platform defaults, missing digest, invalid ABI, invalid optional/required fields |
| Loading | Missing dependency; wrong architecture/format; stale cache; substituted artifact; constructor candidate rejected before opening; load failure rollback |
| Native/SMF parity | Same logical contract and output; registry-symbol-only state rejected as callable; wrong SMF payload ISA; real mapping and call evidence |
| Parser | Empty/small/large inputs, every SIMD tail, guard pages, UTF-8 splits, malformed encoding, indentation, comments/strings/interpolation/custom blocks, incremental edits and error recovery |
| Facade behavior | Reset/append/isolation, interpolation and placeholder transformations, diagnostics order and source spans |
| JIT/AOT | Host-target separation, strict vs relaxed numerics, aliasing/dependence legality, old cache on new environment, scalarized unsupported operations correctly reported |
| Lifetime | Concurrent first load, unload during active CPU/JIT calls, cancellation while GPU running, delayed completion, device loss, queued old generations, stale handles |
| GPU truth | Device absent, forced driver failure, wrong shader, missing feature, no fence, output mismatch, negative-control program, selected versus actually executed artifact |
| Rendering | Resize/reset, overflow, input epoch replay, host-effect commit boundaries, packed arena retirement, required-profile rejection without CPU semantic fallback |

Synthetic feature fixtures test selection logic; they do not grant the local machine those instructions. Emulation is useful for legality and fallback tests, not native performance claims. Hardware promotion requires actual supported hosts/devices.

### 18.2 Performance measurements

Measure cold and warm compiler startup, parser latency/throughput, full compile latency, JIT compile-and-execute cost, memory/RSS and mapped text, allocation counts, instructions/cycles, cache/branch effects where available, vector instruction evidence, provider lookup cost, and artifact size.

For GPU tests add provider/device initialization, program/pipeline creation, queue time, upload/readback bytes, synchronization, kernel timestamps where supported, CPU service time, frame/input latency, and buffer residency. Report application, host broker, and driver-facing work separately where measurable.

Benchmarks include tiny interactive sources, ordinary modules, large projects, Unicode-heavy text, difficult lexical boundaries, malformed sources, 2D scenes, and admitted WebScene profiles. Compare scalar, AVX2 and AVX512 on the same machine when possible; compare CPU and GPU end-to-end rather than importing speedups from another paper.

Promotion thresholds are configurable project policy established after baseline collection. No invented universal percentage or fixed parser/GPU crossover size belongs in the initial design. Use repeated runs and uncertainty intervals; a throughput win cannot hide unacceptable p99 startup/frame regressions.

## 19. Rollout and rollback

**Stage A — observation only:** detect environment, build catalog, explain would-select decisions. Existing parser and GPU paths remain unchanged.

**Stage B — explicit opt-in:** users/tests force admitted providers; preserve existing reference path and collect correctness/performance receipts.

**Stage C — qualified automatic parser:** auto-select only variants certified for the exact grammar/runtime contract. Keep one-step CPU reference override and per-variant quarantine.

**Stage D — dynlib/JIT adoption:** expand selected library families and target-code optimization after ABI and cache tests pass. Do not rebuild the whole compiler matrix.

**Stage E — GPU integration:** select real device programs through existing backend services; qualify frontend, rendering-only and resident-scene facets separately.

Rollback changes the selected generation for new sessions. Active work drains on its pinned generation unless a declared fault protocol requires termination. Persist a reasoned quarantine entry for a broken artifact/environment pair; do not repeatedly crash by selecting it again. A security rejection must remain visible even when a safe optional baseline is available.

## 20. Completion criteria

The feature is complete for a declared product/profile only when all of the following hold:

1. Automatic and manual selection agree with exact CPU/OS/ABI/device requirements and policy.
2. Native and SMF artifacts implement the same typed logical contracts, with truthful callable/execution evidence.
3. Pure-Simple parser variants can be rebuilt/replaced without rebuilding unaffected compiler providers.
4. Generated-code target selection remains independent from the host parser's implementation.
5. CPU-only startup, help/version and reference compilation do not initialize optional GPU machinery.
6. Canonical parsing has qualified dialect coverage and the independent CPU frontend remains usable.
7. AVX512 selection is based on actual required extensions and measured workload performance.
8. GPU offload supports multiple typed domains without a second loader, scheduler, memory-placement layer or display list.
9. Packed rendering uses actual device completion and lease retirement; routing-only paths are never promoted as device proof.
10. Every fallback, rejection, artifact identity and actual execution backend is explainable; unsafe overrides and silent semantic substitutions are impossible by contract.

## 21. Research references and source ledger

### Current repository source

All repository paths below were inspected at the pinned revision unless marked as a search excerpt or documentation claim. URLs are provided as source identifiers.

- **R01:** Coarse SIMD detection and placeholder intrinsics: `src/compiler/30.types/simd_platform.spl` (lines 1–280 inspected).
- **R02:** C runtime feature detection: `src/runtime/runtime_simd_dispatch.c` (1–220).
- **R03:** Real CPU text kernels: `src/runtime/runtime_simd_utf8.c` (1–270).
- **R04:** Tier/profile model: `src/lib/nogc_sync_mut/simd/host_cpu_config.spl` (1–420).
- **R05:** String dispatch/codegen tier scaffold: `src/lib/nogc_sync_mut/simd/variant_dispatch.spl` (1–330).
- **R06:** Variant probe scaffold: `src/lib/nogc_sync_mut/simd/loader_variant_probe.spl` (1–380).
- **R07:** Manifest scaffold: `src/lib/nogc_sync_mut/simd/variant_manifest.spl` (1–330).
- **R08:** Aspect rebind registry: `src/compiler/99.loader/advice_binding_registry.spl` (1–230).
- **R09:** Aspect lifecycle owner gate: `src/compiler/99.loader/aspect_lifecycle_gate.spl` (1–210).
- **R10:** Fixed-width provider contract: `src/compiler/80.driver/driver_provider_contract_v1.spl` (1–170).
- **R11:** Hosted GPU loader/required operations: `src/runtime/runtime_dynload.c` (1–170; later lifecycle details are documented in R12).
- **R12:** Dynamic library behavior/limitations: `doc/07_guide/lib/api/dynlib_api.md` (complete returned guide).
- **R13:** Shared frontend facade: `src/compiler/10.frontend/core/frontend.spl` (complete).
- **R14:** Current scalar-only auto seam: `src/lib/nogc_async_mut/structural/parse/auto_profile.spl` (complete).
- **R15:** Legacy/deferred/packed queue paths: `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl` (1–260 and 290–440).
- **R16:** Documented feature overrides: `doc/04_architecture/app/compiler/cpu_features_config.md` (complete).
- **R17:** Rust configuration search excerpt, not a full codegen audit: `src/compiler_rust/compiler/src/codegen/common_backend.rs`, `CpuFeatureConfig` declaration and parser.
- **R18:** Current checked-in experimental scene plan: `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` (1–190).

Canonical source URL prefix:

`https://github.com/ormastes/simple/blob/da48c00098e843a0465ba36a5850e664685f6c6c/`

### Recovered predecessor plans

- **P01:** `simple_gpu_frontend_parser_unification_design_plan_2026-09-01.md`; saved report, proposed architecture, baseline `1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae`. Retrieved opening architecture/audit/invariant sections. Keeps two CPU paths and global binding/recovery boundaries.
- **P02:** `simple_gpu_scheduler_sosix_resident_rendering_design_2026-09-05.md`; saved report, proposed architecture, baseline `0aed33b8e84f5e6dbe080386e36358fdf0cb4ea6`. Retrieved architecture, profile, evidence and ownership sections. Current packed queue progress is reconciled explicitly in section 13.2 above.
- **P03:** `simple_lint_kernel_plugin_mdsocpp_research_design_parallel_plan_2026-09-03.md`; saved report, baseline `43a4a491c3b5ab8bd350a09a2541a726213053a2`. Retrieved executive design and predecessor-adoption sections. Supplies mechanism-only kernel, stable composition foundation, dense dispatch and no-GC async lifecycle direction.
- **P04:** `simple_compiler_kernel_plugin_bootstrap_refactor_plan_2026-08-30.md`; recovered saved predecessor; architectural adoption is taken from the newer P03 reconciliation rather than assuming every older draft is authoritative.

### External primary references

Accessed 2026-09-07. Toolchain features described by moving documentation must be capability-tested against the actual compiler version used by Simple.

- **E01 — x86-64 psABI, microarchitecture levels and optimized shared libraries:** `https://gitlab.com/x86-psABIs/x86-64-ABI/-/raw/master/x86-64-ABI/low-level-sys-info.tex`
- **E02 — Clang target attributes and function multiversioning:** `https://clang.llvm.org/docs/AttributeReference.html#target-clones`
- **E03 — simdjson architecture implementation selection:** `https://simdjson.org/api/4.6.4/md_doc_2implementation-selection.html`
- **E04 — simdutf project and runtime SIMD implementations:** `https://github.com/simdutf/simdutf`
- **E05 — LLVM ORC design, linkage and resource trackers:** `https://llvm.org/docs/ORCv2.html`
- **E06 — Stehle and Jacobsen, ParPaRaw, research paper:** `https://arxiv.org/html/1905.13415v2`
- **E07 — NVIDIA CUDA compiler driver, host/device compilation and fatbinary:** `https://docs.nvidia.com/cuda/cuda-compiler-driver-nvcc/index.html`
- **E08 — Vulkan supported/enabled features:** `https://docs.vulkan.org/spec/latest/chapters/features.html`
- **E09 — Vulkan pipeline-cache compatibility identity:** `https://docs.vulkan.org/refpages/latest/refpages/source/VkPhysicalDeviceIDProperties.html`
- **E10 — Intel Intrinsics Guide, separate AVX512 extension families:** `https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html`
- **E11 — Linux Arm64 SVE capability and per-thread state:** `https://docs.kernel.org/arch/arm64/sve.html`
- **E12 — Linux RISC-V hardware probe:** `https://docs.kernel.org/arch/riscv/hwprobe.html`
- **E13 — Linux RISC-V vector execution control:** `https://docs.kernel.org/arch/riscv/vector.html`
- **E14 — Linux man-pages, dlopen and constructor timing:** `https://man7.org/linux/man-pages/man3/dlopen.3.html`
- **E15 — Vulkan queue submission contract:** `https://docs.vulkan.org/refpages/latest/refpages/source/vkQueueSubmit2.html`
- **E16 — Vulkan presentation contract:** `https://docs.vulkan.org/refpages/latest/refpages/source/vkQueuePresentKHR.html`

---

**Final recommendation:** One baseline-safe Simple core; typed environment-optimized provider families; parser-only SIMD variation first; common native/SMF/JIT admission; optional device-program bundles; and domain-aware GPU residency planning over the existing parser, SimpleRing, Object VM, SOSIX and Engine2D architecture. Use aspects to observe and verify these boundaries, not to hide implementation identity or change semantic ownership.

## Mechanism addendum: composable lexical summaries (2026-09-08)

This addendum records mechanism transfer only; no external throughput number is
treated as a Simple target.  ParPaRaw's useful abstraction is a chunk-local
finite-state transition table: for each possible entry state, a chunk returns
an exit state and bounded diagnostics.  If `A` and `B` are adjacent chunks,
`compose(A,B)(s) = B(A(s))`; function composition is associative, so a prefix
scan can recover each chunk's true entry state without a preliminary serial
context pass.  This applies to bounded lexical state, not to arbitrary Simple
grammar execution.  Source: Stehle/Jacobsen, PVLDB 13(5),
<https://www.vldb.org/pvldb/vol13/p616-stehle.pdf>.

simdjson's stage-1 design supplies a separate byte classifier/structural index:
backslash runs identify escaped quotes, an odd-backslash mask removes escaped
quote bits, and a prefix parity operation produces the in-string mask.  The
portable lesson is separation of candidate discovery from semantic parsing;
the JSON quote grammar must not be copied as Simple's grammar.  Source:
<https://github.com/simdjson/simdjson/blob/master/HACKING.md>.

simdutf demonstrates two validation contracts that matter for a chunked kernel:
an optimistic boolean validator and an error-reporting validator with an exact
failure position.  UTF-8 validation is not purely byte-local: a chunk summary
must carry pending continuation count, constrained lead-byte range, and first
error status/offset.  Exact error position and malformed-sequence parity need
boundary carry or scalar fallback.  Source:
<https://simdutf.github.io/simdutf/api/> and
<https://arxiv.org/abs/2010.03090>.

For Simple, only a bounded lexical subset should enter the associative path:
ASCII byte classes, quote/escape parity, line-comment visibility, and bounded
UTF-8 boundary state.  Indentation stacks, interpolation nesting, raw/triple
string delimiters with unbounded payload rules, here-documents, and grammar
recovery are fallback boundaries unless their state is explicitly bounded and
included in the transition domain.  Any fallback must preserve source offsets,
diagnostics, ordering, and the same scalar semantic oracle.

Qualification is differential, not benchmark-based: enumerate every chunk
partition around quotes, odd/even backslashes, comment delimiters, CR/LF,
UTF-8 lead/continuation bytes, malformed/truncated sequences, and tail lengths;
compare concatenated masks, exit state, first error offset, and token positions
with one scalar whole-input run.  Also test random partitioning, empty chunks,
all admissible entry states, bounded-state overflow, and unsupported-state
fallback.  Until these pass, report only classification/summary evidence and
not “parallel parser” execution.

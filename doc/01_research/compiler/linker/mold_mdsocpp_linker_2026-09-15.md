# Simple Linker: mold-Based MDSOC++ Architecture (research)

**Research date:** 2026-09-15 (ingested 2026-09-18)
**Status:** proposed architecture and acceptance plan. This is not an implemented or
benchmark-certified linker, and it contains no new measurements.
**Snapshots inspected:** Simple `a637ff56177`, LLVM `37d9648ca786`.
**Companion docs:**
- Inventory of what already exists: `linker_loader_inventory_2026-09-18.md`.
- Plan: `doc/03_plan/compiler/linker/mold_mdsocpp_linker_plan_2026-09-18.md`.
- Design: `doc/05_design/compiler/linker/mold_mdsocpp_linker_design.md`.

**Primary requirement:** keep a performance-first default, and add an independently
selected link mode that preserves every feature and accepts a job-memory limit of
6,000,000,000 bytes.

## 1. Executive decision

Build a **mold-inspired linker product specialized per object format**, on top of the
existing Kernel Plugin Fabric (KPF). LLVM lld is the main native-format reference and
compatibility oracle. GNU ld stays the reference for linker-script semantics. New
providers are written in Simple; external tools and FFI adapters remain as explicit
fallbacks during migration.

> mold-style parallel data processing + lld-style native-format ownership + MDSOC++
> product composition + separately specialized fast and bounded-memory execution.

The design rules out three things:
- Translating every mold class into a dynamically dispatched plugin.
- Forcing ELF, COFF, Mach-O and SMF through one oversized in-memory object model.
- Treating a code-sharing percentage as an acceptance objective. Earlier 50–80 %
  estimates were never measured and are withdrawn. LLVM's native linkers share a
  design but little code [E01].

| Requirement | Design decision | Acceptance evidence |
|---|---|---|
| mold architectural base | Parallel parsing, resolution, section processing and output; compact native state; coarse phase scheduling | Phase traces; comparable native-link benchmarks |
| MDSOC++ | Generic KPF kernel + linker product coordinator + format capsules | Dependency-closure checks; single authoritative owner for each piece of state |
| Product aspects | Aspect packs contribute typed providers, bindings and observers without editing kernel source | Add/remove-pack tests; generic-kernel object keys unchanged |
| Environment variants | Bind eligible CPU/native/SMF variants once per session | Admission rejection; static/dynamic parity |
| Five platforms | Host effects, output format, target ABI and runtime profile kept separate | Native execution or a real SimpleOS boot for each matrix row |
| Fast default | No bounded-store dispatch, spill tracking or pressure polling in fast loops | Generated-code inspection; paired performance gate |
| ≤6 GB mode | Bounded working sets, task reservations, streaming output, optional external-memory algorithms | Complete real Simple link under a measured job-wide limit |
| No feature loss for memory | Same debug, safety, linking and optimization semantics | Fast/bounded output and behavior parity |
| Safe migration | Existing facade and explicit external-tool fallback remain | Reversible cutover, one platform at a time |

## 2. Source facts (at `a637ff56177`)

- **R01 `native_linking.spl`.** `link_to_native` dispatches to platform wrappers and
  external mold/lld/ld or a compiler-driver fallback. SMF is handled separately, and
  mixed SMF/native input is rejected on that path. An explicit `SIMPLE_LINKER` that
  cannot be resolved is an error. The host guards cover Windows x86-64,
  Linux x86-64/AArch64/RISC-V64, and macOS/FreeBSD x86-64/AArch64. Windows ARM64 is
  rejected because MSVC/CRT discovery is x64-only. These are dispatch conditions, not
  proof that each platform's bootstrap passes, and some decisions still consult host
  architecture where they should consult the target.
- **R02 KPF ledger.** Contains common contracts, bounded slots, generation pins,
  async machinery, worker transport, the SDK, backend sessions and a capsule/facet
  sealer. It separates published implementations from unclosed qualifications.
  Reuse it and do not declare KPF fully qualified.
- **R03 compiler plugin migration.** LLVM+Cranelift, ABI v1, canonical `simple.sdn`
  and the aspect-pack policy are all kept. The 6 GB limit is a separate product gate.
- **R04 `link_manager_contract_v1`.** Frozen `ResolveProfile`, identity/placement
  types, CPU-reference encoding, and stages L0–L12:
  - L0 discovery, L1 decode, L2 arenas, L3 intern/sort, L4 selection;
  - L5 archive closure, L6 reachability, L7 layout, L8 relocation;
  - L9 assembly, L10 provenance, L11 write, L12 manifest commit.

  `ResolveMode` is one of CPU-reference, hybrid or resident-GPU. **Memory policy is a
  new orthogonal axis.** Never reuse the GPU-mode discriminants for it or renumber
  stages. Negotiate new facets instead.
- **R05 SMF linker map (2026-07-31).** Its "dead/unwired" labels must be re-audited
  before any code is deleted or adopted.
- **R06 `src/os/kernel/arch/x86_64/linker.ld`.** Uses `PHDRS`, `KEEP`, page alignment,
  section symbols and `AT(...)` LMA expressions for a higher-half image. mold-style
  userland layout cannot express this.

| External reference | Finding | Consequence |
|---|---|---|
| mold paper, Aug 2026 [E02] | Phase and data organization drive parallel speed; mapped input/output residency can dominate memory | Take the performance direction; design a separate bounded working-set path |
| mold manual [E03] | Userland-oriented; limited scripts; fork/detach hides work | Separate boot-layout provider; benchmark with `--no-fork` / `--no-detach` |
| lld architecture [E01] | Native engine per format, no universal abstraction | Common product shell, specialized engines |
| lld ELF/COFF/Mach-O writers [R08–R10] | ELF has finalization/compression/header/offset interplay; COFF has thunk convergence, security tables and PDB ordering; Mach-O has chained fixups, UUID and signing order | Each capsule owns its own dependency DAG |
| GNU ld options [E07] | Memory-saving options reread data; a cache limit is not a job RAM limit | Reference behavior only |

## 3. Architecture: two kernels, one product boundary

```text
existing build/native-build/linker facade
                    │  typed immutable LinkRequest
     LinkProduct coordinator / LinkPlan  (a product facet on generic KPF)
        ┌───────────┼────────────┬─────────────┐
   ELF capsule  COFF capsule  Mach-O capsule  SMF capsule
   fast|bounded fast|bounded  fast|bounded    reference|optimized
        └──── target ABI + layout + debug/codegen facets ────┘
                    │  declared buffer leases, coarse task batches
             SOSIX host capabilities
generic KPF (below): identities, admission, generation pins, capabilities,
dense bindings, cancellation, resource accounting, receipts
```

| Owner | Authoritative state | Must not own |
|---|---|---|
| Generic KPF | Provider identity, admission, lifecycle, capability and generation tables | Symbols, COMDAT, relocation semantics |
| LinkProduct | Immutable request, composition, job transaction, stage receipts, verdict | Private format data |
| Format capsule | Symbol winners, archive membership, section graph, layout, relocation state | Another capsule's mutable objects |
| Target ABI/profile | Runtime imports, entry conventions, security defaults, layout policy | Implicit host filesystem discovery |
| Working-set impl | Windows, leases, spill partitions, reservations | Liveness or other semantic decisions |
| Debug/codegen facet | Its own bounded intermediate state and artifacts | Unaccounted helpers; hidden option changes |
| SOSIX | File/mapping, process/thread, timing, page accounting | Format algorithms |

**Share:**
- input identities, safe binary readers, diagnostics, content hashes;
- coarse scheduling, immutable descriptors, lease protocols;
- external sort, transaction publication, cache validation, test harnesses;
- generic graph/partition/prefix-sum code, but only via compile-time specialization.

**Do not share:** ELF visibility/versioning/interposition, COFF weak
externals/COMDAT/directives, Mach-O namespaces/fixups, TLS, unwind, and layout
convergence. **Do not introduce a mandatory `VirtualObject → VirtualSection →
VirtualRelocation` hierarchy.**

**Loader vs linker.** Reuse loader-core identity checks, SMF parsing, admission, ABI
negotiation, generation tracking and caches through their facades. Keep full native-link
algorithms (archive search, ICF, LTO, whole-image layout) out of the runtime loader
closure. `simple --help` and SimpleOS recovery builds must not load a linker, LLVM or PDB
code.

## 4. mold → MDSOC++ mapping (unit = coherent subsystem, not class)

| mold responsibility | Owner | Dispatch frequency |
|---|---|---|
| Config/driver | LinkRequest adapter + LinkProduct | once per job |
| `Context<E>` state | private engine session, target-specialized | engine chosen once |
| File/archive reading | engine reader + SOSIX byte sources | per input batch/window |
| Symbol resolution | format-private arrays/tables | direct loops |
| Reachability/ICF | engine kernels with explicit roots | per pass/partition |
| Relocation functions | target-specialized code inside engine | never a plugin lookup per relocation |
| Placement/synthesized data | native layout planner | dependency/fixpoint stages |
| Output copy/patch | output kernel + output leases | per disjoint range |
| LTO | optional codegen facet with budget | per module batch |
| Diagnostics/profiling | KPF receipts + observer aspect | phase/batch boundaries |

Proposed contract notation (not an existing API):

```text
LinkRequestV1        request_id, target{arch,os,abi,object_format,endian,address_width},
                     inputs(ordered manifest handle), semantic_profile_digest,
                     runtime_and_sysroot_digest, output_contract, required_features,
                     layout/debug/codegen contract handles, reproducibility_policy
LinkExecutionPolicyV1 mode Fast|Bounded|Auto, job_memory_limit_bytes,
                     scratch_limit_bytes, max_workers, allowed_placements,
                     enforcement_requirement
LinkEngineFacetV1    describe_capabilities, inspect_and_plan, create_session, run,
                     cancel, drain -> RetirementProof, take_result
```

- **Wire format:** fixed-width schema fields, overflow-checked offset tables, versioned
  tails. Dynamic boundaries carry opaque generational handles and bounded spans only.
- **Fast vs bounded:** separately compiled variants, selected once
  (`run_elf_x64_fast` / `run_elf_x64_bounded`). Source may be shared through
  specialization, but there is never a per-reference virtual `MemoryStore.get()`.

## 5. Product aspects and environment-selected dynload

- **What a pack can contribute:** real providers (ELF/COFF engines, boot layout,
  bounded variant, debug) and observers. It declares
  `ProductAspectContribution{provided/required facets, typed ports, semantic profile,
  variant requirements, lifecycle deps, effects/capabilities, resources, ordered
  observers}`.
- **Replacement rules:** replace only at a declared typed port, with one
  implementation per facet in a sealed session. Conflicting replacements are a seal
  error.
- **Binding:** reuse `EnvironmentSnapshot`, `VariantDescriptor` and the
  generation-pinned `BindingPlan` [P02]. Validate descriptors and dependencies before
  loading, because native constructors run at load time.
- **Host vs target:** the host feature set is independent of the output target. An
  x86 AVX-512 engine may emit an ARM64 image.
- **Overhead:** static-sealed composition gives direct calls; dynamic composition gives
  one indirect entry or batch call. Never call it "zero"; measure it. No per-symbol
  lookup, pointcut, lock or ABI check sits in fast loops. No code-page rewriting.
  A generation update applies only to new sessions.
- **Two meanings of "aspect":** linker-product aspects change the linker itself.
  Target-program aspects arrive as compiler-produced objects/metadata before
  `FinalLayoutSeal`. Laid-out images are never patched.
- **Cancellation:** cancel is a request. Unload requires a completed drain and zero
  generation pins; otherwise the worker is isolated.

## 6. Native semantic pipeline

```text
ordered input manifest → discovery/decoding → symbol + archive closure ⇄ optional
codegen (generated inputs re-enter) → section selection/reachability/ICF →
relocation scan + synthesized sections → layout ⇄ thunk/relaxation/fixup convergence
→ FinalLayoutSeal → output ranges + relocation + finalization → debug/identity/
signature/validation → artifact transaction + receipt
```

- **Archives:** preserve command-line ordinals and group boundaries. Parallel
  discovery never changes precedence. Archive closure is a real fixpoint.
- **Symbols:** a hash only proposes a candidate; compare the full identity (namespaces,
  versions). A frozen `ResolveKey` needs a collision-verifiable name sidecar or a new
  facet. Duplicate strong definitions stay strict unless an explicit, receipted
  compatibility switch says otherwise.
- **ICF and roots:** roots = entry, exports, init, TLS callbacks, aspect
  registration, script `KEEP`, unwind/security associations. ICF preserves address
  significance. Bounded mode never folds more aggressively than fast mode.
- **Layout is a converging computation** (COFF ARM thunks, ELF compression/headers,
  Mach-O fixups/signing). `FinalLayoutSeal` is immutable. Relocation arithmetic is
  shared only when the full contract matches (location convention, addend, bias,
  range, encoding, pairing).
- **Transactional output:** disjoint ranges; declared handling for relocations that
  cross window boundaries; digest-addressed artifacts published through a manifest
  pointer. A missing required PDB/dSYM/manifest makes the result incomplete, not
  successful.

## 7. Platforms

| Target | Engine | Oracle/fallback | Acceptance |
|---|---|---|---|
| Linux userland | ELF | mold, `ld.lld`, GNU ld | execute compiler + regression corpus |
| FreeBSD userland | ELF | native `ld.lld` | execute on FreeBSD |
| Windows MSVC | COFF/PE | `lld-link`, `link.exe` | run EXE/DLL, debug/unwind on Windows |
| Windows GNU | COFF/PE | MinGW toolchain | MinGW fixtures + Simple product |
| macOS | Mach-O | `ld64.lld`, Apple ld | run on macOS; dylib load; debug |
| SimpleOS boot image | ELF + `BootLayoutPlan` | host `ld.lld`/GNU ld | real boot under QEMU and on hardware |
| SimpleOS apps/providers | native image and/or SMF | existing loader | load/call/unload/generation tests |

- **Host capabilities:** declared separately (reads, windows, range writes, threads,
  spawn, dynload, accounting, atomic publish, temp storage). They are obtained through
  SOSIX adapters. A static-sealed composition works where there is no dynload or spawn.
- **`BootLayoutPlan`:** regions, segment permissions, placement/retention,
  VMA/LMA expressions, entry/boundary symbols, assertions and boot-protocol ranges.
  Translate the real SimpleOS scripts first, and keep the external script linker until
  boot equivalence is shown.

## 8. Performance-first execution

- **Fast:** resident metadata, hot/cold split, compact local indices, lookup-once
  handles. 64-bit offsets with segmented arenas (no accidental 4 GB ceiling). Delayed
  expansion, deterministic ordering. The allocator is chosen by measurement, not
  assumed.
- **SIMD/GPU:** SIMD comes only after a measured bottleneck. GPU providers are
  experimental, outside the 6 GB promise, and kept with a CPU oracle.
- **Caches:** a cold link must work. Cache keys cover inputs, ABI, options, layout,
  sysroot, debug/codegen policy and semantic provider digests. No mandatory daemon.
- **Product splitting** is not a memory result for the full product.

## 9. The 6 GB contract

- **Scope:** 6 GB = 6,000,000,000 bytes (≈5.59 GiB) for the entire job: coordinator,
  providers, stacks, input/output residency, decompression, debug, LTO and helpers. A
  machine preset for 6 GB hosts is 4.5 GB, subject to qualification.
- **Bounded strategies:**
  - *Bounded-stream* (built first): resident core metadata; windowed input,
    decompression and output.
  - *Bounded-spill*: partitioned symbols, disk-backed indexes, external sort.

  Switching is allowed only at safe stage boundaries within the bounded family.
  Fast → bounded requires a clean restart.
- **Reservation envelope** (a proposal, in decimal GB):

  | Category | Reservation (GB) |
  |---|---:|
  | Coordinator, provider images, thread stacks | 0.25 |
  | Symbols and names | 0.95 |
  | Section, COMDAT and layout metadata | 0.65 |
  | Reachability and ICF | 0.45 |
  | Input and decompression windows | 0.70 |
  | Output staging and cache | 0.80 |
  | Worker scratch | 0.40 |
  | Debug and codegen helpers | 1.00 |
  | **Planned active envelope** | **5.20** |
  | **Headroom** | **0.80** |
  | **Acceptance ceiling** | **6.00** |

- **Scheduling:** `admissible_workers = min(cpu_limit, floor(available_budget /
  peak_per_worker))`. The bounded mode is no-GC, not no-allocation.
- **External-memory equivalents:**
  - windowed input with no retained pointers into evicted windows;
  - partition-and-spill symbol grouping with full-name compare;
  - a persistent archive bitmap plus bounded frontiers;
  - source-indexed relocation partitions and paged reachability;
  - external ICF refinement with exact compare;
  - bounded output buffers and streamed/spilled debug data.

  The spill directory has its own quota and never lands on tmpfs. Spill files carry
  checksums. Giant single objects need streaming at record/subsection granularity, or
  an explicit minimum-workspace failure.
- **Accounting:**
  - Linux: a fresh job cgroup including descendants and file-cache pages, no swap;
    judged on the measured peak.
  - Windows: Job commit plus measured residency. Job commit is not a residency cap.
  - macOS and FreeBSD: measured-only until an adapter is qualified.
  - SimpleOS: SOSIX page-budget authority.

  Every receipt names its accounting class (`MeasuredOnly` / `NotCertified` /
  qualified).
- **LTO and PDB** are separate consumers with their own budgets. Never silently
  downgrade Full LTO to ThinLTO, strip debug, weaken ICF safety or drop security
  features.
- **Auto mode:** selects before execution and records its reasoning. A strict-bounded
  product always uses bounded admission.

## 10. Integration, configuration and receipts

- **Order:** adapters first. Prove the request adapter over the existing external
  linker (arguments, runtime selection, diagnostics, artifact identity), then add
  internal providers behind the same boundary.
- **Proposed placement:** `src/lib/common/linker/` (contracts only),
  `70.backend/linker/{product,compatibility}`,
  `src/plugins/link_{elf,coff,macho,smf,boot_layout,debug,codegen}/`,
  `src/lib/nogc_async_mut/link_working_set/`, `src/compositions/linker_{fast,bounded}/`.
  Every one of these must pass the closure checker.
- **Proposed config:** `link.execution.mode fast|bounded|auto`,
  `memory_limit_bytes 6000000000`, `accounting qualified_job_scope`,
  `semantics.preserve_requested_features true`.
- **Proposed CLI:** `simple link --link-mode=... --link-memory-limit=...`. An
  unavailable explicit request is a named error.
- **Receipt:** request and input digests, toolchain identity, separate host and target,
  engine/placement/variant/generation, policy digests, activated aspects, counts and
  artifact digests, phase and fallback history, accounting class and measured peak,
  helper/scratch/I/O totals, feature coverage and retirement.
- **Distinct outcomes:** `Success`, `UnsupportedFeature`, `UnsupportedBudget`,
  `IncompleteDebugOutput`, `InputError`, `ResourceFailure`, `Cancelled`.

## 11. Verification

- **Corpus (captured first):** small CLI; full compiler release (the 6 GB target);
  compiler plus providers; full-debug; ThinLTO; SimpleOS kernel and apps; an
  adversarial giant-object set.
- **Correctness:** native parsers plus execution. Fast/bounded parity for the same
  profile. Targeted cases:
  - archives, COMDAT, roots;
  - relocation overflow and thunks;
  - ICF address significance;
  - malformed inputs;
  - imports/exports/dylibs, TLS/unwind/security;
  - debug identity;
  - spill corruption, disk-full, cancel.

  Hand-derived goldens are required as well as oracle agreement.
- **Plugin tests:** ABI mismatch, missing operations, false claims, conflicts,
  observer order, stale handles, generation pins.
- **Performance:** paired runs with pinned mold/lld; cold and warm separate. Report
  latency, CPU, peak memory with accounting class, faults, I/O, spill and phases.
  A 2 % regression is an investigation trigger, not an allowance. Inspect generated
  code as well.
- **Memory:** a Linux cgroup set up before the first input access, including all
  descendants and no swap. The measured peak must sit under the ceiling and the link
  must succeed.
- **Mutation-sensitive gates:** remove the archive fixpoint, drop a boot `KEEP`, skip
  the ABI check, allow a stale generation, remove a reservation, bypass the bounded
  variant, drop debug output, suppress relocation overflow, or report success without
  running the engine. Each mutation must turn its gate red.

## 12. Gates (dependencies, not dates)

| Gate | Work | Exit |
|---|---|---|
| G0 | Baseline corpus + recipes; re-audit linker map; freeze 6 GB meaning and accounting classes | reproducer reruns; missing items stay BLOCKED |
| G1 | `LinkRequest`/`LinkExecutionPolicy` via the schema authority; wrap mold/lld/ld/driver as external providers; aspect contributions + receipts | existing products build through the facade; explicit-missing requests fail; closure + rollback pass |
| G2 | Internal ELF fast engine for the real compiler corpus; SMF adapters; archive fixpoint, GC, relocation, synthesized sections, output transaction | real compiler links and runs; oracle semantics match; direct-vs-plugin performance measured |
| G3 | Bounded-stream, then spill; whole-job accounting; non-LTO and debug separately; ThinLTO later | full product links under 6,000,000,000 measured bytes, semantics unchanged |
| G4 | COFF, Mach-O, FreeBSD, SimpleOS layout lanes in parallel; AArch64/RISC-V relocation; Windows ARM64 as new capability | per-platform native run or boot, parity, advertised memory profile |
| G5 | Dynamic aspects, generation-safe replacement; static recovery linker keeps bootstrap non-circular | aspect add/replace without kernel edits; old sessions stay safe |
| G6 | Per-platform cutover; SIMD, GPU and caches behind their own gates | receipts name the actual engine; a fallback is never counted as completion |

Lanes A0–A10: architecture/integration, schema/KPF adapter, ELF semantics, fast,
bounded, COFF, Mach-O, FreeBSD/SimpleOS, debug/codegen, host/lifecycle,
conformance/performance. Each works in its own worktree. Only the schema owner changes
wire layouts.

## 13. Risks

| Risk | Stop condition / mitigation |
|---|---|
| Universal abstraction slows hot loops | Private native state; specialization; measure before merging |
| New plugin kernel duplicates KPF | Linker contributes facets only |
| Fast and bounded drift apart | Shared semantic policy; differential corpus |
| Page cache or helpers evade the cap | Job-wide accounting class |
| Giant input defeats window bounds | Subsection streaming or explicit failure |
| PDB/LTO eats the budget | Separate admission; no silent feature removal |
| Boot image linked like userland | Dedicated layout profile + boot tests |
| Unload with live callbacks | Pins, drain proof, isolation |
| Aspect conflict or hidden mutation | One implementation per facet |
| Stale historical "implemented" status | Current call-path audit |
| Fallback hides missing native work | Engine identity recorded in the receipt |
| Circular bootstrap | Static recovery product + external toolchain |
| Copied upstream code loses provenance | Track origin and license |

mold's older design document flags its own age and is not authoritative [E05].

**First slice:**
1. Keep the facade.
2. Add the KPF linker contract.
3. Wrap the external providers.
4. Build the native ELF subset the real Simple compiler needs.
5. Prove the fast path.
6. Add bounded stream/spill.
7. Close the 6 GB gate.

Completion means measured execution of the declared product, on the declared
platform, under the declared resource contract.

## Sources

- **Repository (`a637ff56177`):**
  - R01 `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl`
  - R02 `doc/03_plan/agent_tasks/kernel_plugin_fabric.md`
  - R03 `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md`
  - R04 `doc/05_design/platform/structural_compute/link_manager_contract_v1.md`
  - R05 `.spipe/link_manager/smf_linker_map.md`
  - R06 `src/os/kernel/arch/x86_64/linker.ld`
- **Upstream code:** R07 mold `src/main.cc`; R08–R10 lld `ELF`/`COFF`/`MachO`
  `Writer.cpp` at LLVM `37d9648ca786`.
- **Predecessor designs:**
  - P01 lint/kernel-plugin MDSOC++ plan (2026-09-03)
  - P02 env-optimized dynlibs/SIMD/GPU (2026-09-07)
  - P03 compiler kernel-plugin incremental bootstrap (2026-08-30)
- **External:**
  - E01 lld.llvm.org/NewLLD.html
  - E02 arXiv 2608.23228 (mold)
  - E03 mold manual
  - E04 lld.llvm.org
  - E05 mold `design.md`
  - E06 lld MachO
  - E07 GNU ld Options
  - E08 PE/COFF spec
  - E09 cgroup v2
  - E10 Windows Job Objects
  - E11 Clang ThinLTO

## 14. Release-branch research refresh — 2026-10-03

**Author:** Codex research sidecar `/root/linker_research`.
**Session:** `item4-linker-research-20261003`.
**Worktree:** `C:/dev/simple-item4-linker-research-20261003`.
**Work branch:** `work/item4-linker-research-20261003`.
**Target:** `origin/release/1.0`; source-inspection base:
`e9cd3153c881c55f59eaaa2573b4b8a5e803023a`.
**Renewed session base and expected target:**
`cb2f783acf0ea22e8da54ff0d8d18b4fb14c816c`.
The integration owner fetched the original target before delegating the worktree,
then renewed it after concurrent release integration. The private lane rebased
with its sole owned edit preserved; the target delta changes none of this
research document, linker sources, completion producer, or bounded composition.
This append-only refresh preserves historical findings above. It records source
inspection and primary-source research, not new runtime PASS evidence.

### 14.1 Current implementation versus qualification

The seven-plan host-completion document's item 4 retains the full linker scope.
An emitted header, parser, model, or receipt validator cannot substitute for
executable startup, host qualification, or measured resource compliance.

| Evidence at the pinned base | Consequence for acceptance |
|---|---|
| `link_engine_external.spl::link_request_internal` rejects every non-ELF object format; `_LinkerWrapper/native_linking.spl::internal_link_native` rejects non-Linux OS and target/host architecture mismatch | The request facade's supported target set differs from the separate Windows COFF production route. Exercise both entrypoints; do not infer facade PE support from COFF writer tests. |
| `link_request_to_native` resolves bounded policy and returns `UnsupportedBudget` before input access because its owned execution/job-scope provider is disconnected | Fail-closed admission is implemented; a successful bounded link and fast/bounded digest parity remain unproven. |
| `src/compositions/linker_bounded/composition.spl` seals a static descriptor with a 6,000,000,000-byte policy | A declared memory contract does not prove actual stream/spill execution, descendant accounting, or the measured peak. |
| `link_engine_external.spl::resolve_engine_id_for_success` documents that a successful compiler-driver fallback can be reported as the originally resolved direct linker | Engine identity must come from the actual execution result. A new detection probe after success cannot prove which engine ran. |
| `requirement_from_header` constructs schema identity requirements from the same incoming header; `receipt_header` uses placeholder identity | Existing shape validation cannot establish independent schema identity admission. Preserve the S1 owner handoff; do not invent a second registry in the linker. |
| `mold_compatibility.spl` reports Linux unqualified, Windows hosted-partial, and SimpleOS boot evidence pending | These source states contradict treating historical lane PASS notes as whole-product completion. |
| `src/app/test/mold_completion_receipt.spl` checks ten ordered receipt keys, status text, regular files, and SHA-256 bindings before publishing an aggregate | The producer proves bound-file integrity. It does not parse actual command exit status, verify engine identity, inspect object-format semantics, or independently measure performance. Those checks remain obligations of each evidence producer and admission reviewer. |
| Completion keys enumerate Linux, Windows, SimpleOS, corpus/parity/platform/performance evidence, but no explicit Mach-O or FreeBSD key | The generic `platform_receipts` artifact must enumerate those retained targets and their admission or user-approved unsupported decision. Their absence must not become implicit approval. |

The initial scan found Mach-O parser/inspection modules, ELF engine modules,
and a COFF engine with PE import/export/base-relocation writers. This establishes
source ownership locations only. No native execution was performed in this
research lane, and no target is newly certified by this document.

### 14.2 Concrete retained acceptance inventory

IDs below trace existing item-4 requirements and the research/plan G0–G6 gates.
They do not select new optional scope or silently delete unsupported targets.
Each scenario needs a real setup action, production entrypoint, independent
observable assertion, and evidence tied to the exact tested commit/runtime.

| ID | Concrete acceptance scenarios and failure oracle |
|---|---|
| ITEM4-REQ-001 | Map each retained layer/facet to its source owner and public entrypoint. Reject unknown schema identity, missing required facet, and incompatible ABI before reading inputs. Check both the facade and actual engine path. |
| ITEM4-REQ-002 | Force an internal link and prove its receipt names the format-specific internal engine. Force direct-link failure followed by an allowed compiler-driver success and require the receipt to name that driver. For an explicit unavailable engine require a named failure and no fallback output. |
| ITEM4-REQ-003 | Link two objects returning 42; test strong-over-weak and duplicate-strong failure. Build an archive where resolving one member creates a reference needing another extraction pass. Keep an explicit root/constructor/retained section, discard a dead section containing an undefined reference, and prove retained code executes. |
| ITEM4-REQ-004 | For each admitted architecture, patch hand-derived relocation values and compare independent tool inspection. Test minimum/maximum legal values, adjacent overflow, misalignment, and unsupported relocation. Assert failure leaves no newly published executable and preserves an existing valid output. |
| ITEM4-REQ-005 | Run an executable importing a function and data from a shared library; verify runtime result and required dependency metadata. Exercise admitted TLS and unwind paths. Link stripped and unstripped variants: both run identically, while inspection proves the requested symbol/debug removal without deleting required dynamic symbols. |
| ITEM4-REQ-006 | Maintain explicit format/OS/architecture/backend rows for ELF, PE/COFF, and Mach-O, including FreeBSD, Windows ARM64, RISC-V, and SimpleOS obligations retained in G4. Each advertised row requires native execution or the declared firmware/board evidence. A missing host is BLOCKED; an unsupported scope decision requires user acceptance. |
| ITEM4-REQ-007 | Re-link identical immutable inputs with controlled environment and scheduling variations; compare complete output digest and diagnostics ordering. Missing symbol, duplicate symbol, malformed input, and wrong machine must produce stable named diagnostics through the production API. |
| ITEM4-REQ-008 | Link the real self-hosted compiler and representative applications using the internal engine; execute the resulting compiler on a known program and check its output. Bind all input, runtime, engine, output, command, and transcript identities. Small fixture execution alone cannot close this row. |
| ITEM4-REQ-009 | Compare pinned internal/baseline runs on the same corpus, separating cold/warm runs. Record elapsed time, CPU, qualified peak memory, output size, I/O/spill, and correctness. Run fast and bounded modes with identical semantics; require whole-job peak strictly below 6,000,000,000 bytes and complete digest parity. Inject spill corruption, disk-full, and cancellation; prove failure cleanup and no partial publication. |
| ITEM4-REQ-010 | Retained linker G5 only: replace a linker aspect without kernel edits, hold an existing session across replacement, and prove it continues with its pinned generation. Reject stale handles and ABI conflicts; prove the static recovery composition and `simple --help` remain independent of linker activation. This does not transfer item-5 ownership into this lane. |

A modern SSpec manual should describe actions/results from these executable
scenarios. Helpers must execute production behavior and assert returned data;
a test-local Boolean named `success` or `linker_available` is not evidence.
Mark unavailable infrastructure explicitly and keep the corresponding gate open.
Mutation examples: bypass archive closure, suppress relocation overflow, report
the requested engine after fallback, omit one platform row, and replace a
measured memory receipt with `MeasuredOnly`. Each must make its acceptance fail.

### 14.3 Primary-source research and design implications

Research date: 2026-10-03. These upstream references inform test oracles; they do
not certify Simple's implementation. Pin exact tool versions/commits in test
receipts rather than relying on mutable upstream pages.

- [mold manual](https://github.com/rui314/mold/blob/main/docs/mold.md)
  documents deterministic output. Test whole-image reproducibility separately
  from semantic equivalence against a different linker.
- [mold's historical design](https://github.com/rui314/mold/blob/main/docs/design.md)
  warns that its 2020 description is outdated. Use current implementation/manual
  evidence when adopting performance or script-support claims.
- [LLD implementation design](https://lld.llvm.org/NewLLD.html) and the
  [Mach-O port](https://lld.llvm.org/MachO/index.html) describe distinct format
  implementations. Their existence supports format-specific conformance gates,
  not inference that an ELF engine implements Mach-O.
- [LLD section-retention documentation](https://lld.llvm.org/ELF/start-stop-gc.html)
  distinguishes compiler retention from linker garbage collection. Fixtures must
  encode the actual retention contract rather than assume a compiler `used`
  annotation roots a section during linking.
- [Microsoft PE/COFF format](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format)
  is the reference for machine types, imports, base relocations, and image
  structures. Check PE fields independently and execute through the Windows
  loader; an ELF success or COFF parser success is insufficient.
- [Linux cgroup v2](https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html)
  defines memory controller interfaces including limits and swap controls.
  Install the job boundary before the first input access, include descendants,
  disable swap under the retained contract, and collect the qualified peak.
  Process RSS alone does not prove the declared whole-job memory bound.

### 14.4 Sequencing without scope loss

First repair the measurement surface that can misidentify an executed engine
and define the executable acceptance matrix. Then use red tests to drive missing
format/facade routing and engine semantics. Keep host execution, compiler-corpus
runs, bounded execution, and linker lifecycle gates visible until independently
qualified; passing a policy validator is not an alternative end state.

The branch owner integrates research into plan/design and allocates source/test
ownership. Any new optional capability beyond the retained plan must have
pros/cons/effort options and user selection before implementation. No unsupported
target is accepted, no release is approved, and no whole-item PASS is claimed by
this research addendum.

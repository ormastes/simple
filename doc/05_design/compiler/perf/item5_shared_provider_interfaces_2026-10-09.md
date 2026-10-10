# Item 5 shared provider interfaces and release compatibility

## 2026-10-11 variation and SOSIX integration

The user selected the [integrated variation proposal](../simd_gpu_sosix_variation_final_2026-10-10.md) for research, plan and design incorporation. Current comparison baseline: release `02b150b385013d21bc408b45244431de85d391de`. Earlier dated observations below remain historical. This addendum takes precedence where their ownership or PR status differs; it does not certify implementation or native support.

### Canonical owners and compatibility

- Reuse `composition/environment_variants/`: `EnvironmentSnapshotV1`, `VariantDescriptorV1`, `BindingPlanV1`, `TargetCodegenProfileV1`, catalog, admission, feature registry and binding runtime. Existing `feature_registry_v1.spl` already defines precise psABI V2 feature IDs/masks; extend registered rows rather than create another feature taxonomy.
- Reuse `canonical_target_registry_owner_v2.spl` and environment-variant `provider_generation_v2.spl` for their existing target/generation responsibilities. Generic loader/generation V1 and environment generation V2 have distinct authority roles; an explicit adapter must bind their identities, pins and retirement without replacing public V1 callers or duplicating either state machine. That adapter's production qualification remains pending.
- Keep one resolver-only `variants/` root with `config/var.sdn`; implementation code stays in its current layer. Scoped slots, legacy SIMD-root normalization and selected-source cache keys require real resolver work. A manifest policy field that the parser ignores is not enforcement.
- Keep fixed/scalable CPU SIMD and GPU SIMT distinct. The shared vectorizer receives output-target intent; host, worker vector state, policy and device generations govern execution admission. Width alone cannot satisfy an ISA requirement. Qualcomm CPU, Adreno GPU and Hexagon/HVX are separate domains.
- SOSIX/common operation contracts and SimpleRing own service completion, buffer leases and retirement. GPU providers retain API mechanics; existing compiler/ProcessingIR owners retain algorithms and planning. No second GPU runtime, Future family or scheduler is introduced.
- Resolve/authenticate/bind outside arithmetic loops. Prepared CPU calls stay direct; no ring submission, CPUID, catalog walk, source scan or filesystem probe is added per SIMD operation. Timeout/cancel does not release an in-flight buffer; close waits for generation pins and operation retirement.

### Current corrections and limits

Release PR #2840 contains the canonical native-all C GPU registry repair; PR #2838 contains the LLVM pointer-cast repair. The reviewed five registry files match the replacement-archive C test that executed eight device launches, checked 1,506 words and 128 canaries, and rejected an invalid digest. That evidence covers the C registry/device boundary only. It does not qualify Simple DB, compiler plugins, SOSIX-G, image authority or full bootstrap.

The GPU environment-variant task bridge still declares device-image authority and physical execution unavailable. Do not promote those flags from the independent C result. The current vectorizer's host-global fallback and width-based requirement receipts remain concrete integration gaps. Native ARM/RISC-V application execution and physical performance remain open.

The inspected environment validators accept x86_64, AArch64, RV64 and wasm32; the canonical registry's native rows are Linux GNU/ELF, alongside wasm. Windows/macOS/FreeBSD/SimpleOS and ARM32/x86-32/RV32 registration, codec/validator parity and execution cannot be inferred from backend presets. Keep these migration rows open. The CPU vector byte wire is process-local and synchronous (64-byte request, 24-byte response); its borrowed pointers are not transferable GPU handles, and 32-bit conversion needs explicit checked parity.

The proposal's P0–P9 are migration work packages in the [existing implementation plan](../../../03_plan/compiler/perf/runtime_optional_provider_binary_size_optimization_plan_2026-09-02.md). Its P5 means SIMD planning; Item 5 Phase 5 continues to mean Size and Loading Gates. Preserve REQ-001..015 and NFR-001..007; the selected variation requirements and pending acceptance rows extend them. No default, ABI, support flag or executable source changes in this documentation update.

Status: documentation reconciliation against release `59499d746975ef06ada5e6769142bdb7d5403e86`, 2026-10-09. This defines the compatibility and verification handoff; it does not certify implementation completion, native application execution, or bootstrap admission.

Item 5 is kernel/extension aspects and binary size in the [seven-item plan](../../../03_plan/seven_plans_host_completion_2026-09-29.md). Its own **Phase 5 is Size and Loading Gates** in the [implementation plan](../../../03_plan/compiler/perf/runtime_optional_provider_binary_size_optimization_plan_2026-09-02.md). Neither name is a compiler generation or permission to skip the other phases. The selected [requirements](../../../02_requirements/feature/runtime_optional_provider_binary_size_optimization.md) and their budgets remain unchanged.

## Shared owners, not parallel interfaces

Paths below are repository-root-relative. Reuse these production owners; do not add a second provider loader or copy a wire contract into each application.

| Concern | Existing shared owner and contract | Compatibility boundary |
|---|---|---|
| Generic provider query | `src/lib/nogc_sync_mut/composition/provider_contract.spl`: `SimpleProviderQueryV1`, `SimpleProviderQueryResultV1` | Preserve the 44-byte query, 84-byte result, 32-byte digest, field widths, versions and statuses. These are distinct from the vector operation wire. A descriptor or digest is not an executable address. |
| Metadata admission | `src/compiler/99.loader/provider_admission/state.spl`, `admission.spl` | Reuse metadata/effect-owner admission. Its successful result does not prove a native library was opened or initialized. |
| Callable signature admission | `src/compiler/99.loader/provider_call_boundary_v1.spl` | A call permit validates the boundary; it does not itself dispatch a provider operation. |
| Actual mapping and lifetime | `src/os/smf/provider_loader.spl`: `ProviderAdmissionRequestV1`, `ProviderAdmissionResultV1`, `ProviderLoaderSessionV1`, `ProviderDynamicAdmissionV1` | Keep one loader/session owner for digest, process-callable query, pins, invocation and close. Preserve V1 constructors and public outcomes for existing callers. |
| Generation ownership | `src/lib/nogc_sync_mut/composition/provider_generation.spl`: `ProviderGenerationManagerV1`, `ProviderGenerationPinV1` | Activate and pin already-admitted generations; this manager does not independently map libraries. Thread returned owned query/release/close session values through callers, including cleanup failures. |
| Kernel/plugin sharing | `src/lib/common/kernel_plugin/` and `src/os/smf/kernel_plugin/native_loader.spl`: `KpfSchemaHeaderV1`, `KpfSchemaRequirementV1`, `KpfSmfNativeSessionV1` | Use existing KPF adapters and schema/status contracts. Admitted operation tables and their session generation remain required; do not expose compiler-private trait/AST/HIR layout as a new plugin ABI. |
| Host and variant eligibility | `src/lib/nogc_sync_mut/composition/environment_variants/contracts_v1.spl`: `EnvironmentSnapshotV1`, `VariantDescriptorV1`, `BindingPlanV1` | Host capabilities and generated target intent are distinct. A caller-supplied target label cannot manufacture host capability or trusted artifact identity. |
| CPU vector operations | `src/runtime/simple_vector_kernel_abi_v1.h` | One byte-wire contract for bitmap and HTTP kernels across AVX512, NEON, SVE/SVE2 and RVV. Do not replace the defined wire layout with native struct packing. |
| GPU operations | `src/runtime/simple_gpu_provider_abi_v1.h` | Preserve the GPU handle/resource/submit/receipt contract and asynchronous lifetime rules. Share admission and evidence policy with CPU providers, not their operation ABI or completion semantics. |
| Application evidence | `scripts/check/run-item5-app-vector-receipts.shs`, `scripts/check/lib/item5-app-build-manifest.pl`, `scripts/check/lib/Item5QemuProfile.pm` | Keep native manifest v2 compatible; use the target-bound v3 path for QEMU profiles. Provider events, guest PID and target tool/runtime identities must bind actual app binaries. |

The architecture's `RuntimeFeatureClosureV1`, `ProviderStabilityReceiptV1`, `ProviderSelectionV1`, `RuntimeLinkManifestV1`, `NoUnwindProofV1` and `BinarySizeReceiptV1` remain design roles, not implemented production types under those names. Release does define `ProviderDescriptorV1` in `src/compiler/99.loader/provider_admission/state.spl` for compiler package/effect metadata; that existing record is distinct from an executable plugin descriptor or a callable-admission record. The historical `runtime_feature_closure.spl` owner is absent in this release. Do not rename an existing provider request into one of these roles, change its ABI, or mark a design role implemented solely because another record has similar fields.

Preserve the [dynamic kernel/provider composition design](../dynamic_runtime_kernel_provider_composition_2026-09-22.md) and selected [kernel migration requirements](../../../02_requirements/feature/kernel_plugin_migration.md). K0 grammar/HIR/MIR and trust roots remain core; K1 LLVM/Cranelift selection remains explicit. A manifest for LLVM alone does not admit both backends. Shared parser consumers can reuse the admission/lifetime substrate, but `ParserProviderV1` currently defaults to `LegacyReference` and rejects candidate modes. `FrontendFacetV1` is a descriptor, not a replacement parser ABI or proof of implemented facet acquisition grammar. This update changes neither parser defaults nor those incomplete implementation boundaries.

## Common handoff and lifetime

1. The compiler/link owner derives entry, target and retained-root evidence. Uncertain roots remain retained with a reason; linker flags alone are not a closure proof.
2. Registry and environment owners select metadata without loading, compiling, parsing or initializing optional providers. Cache keys must bind artifact, dependency, ABI, policy and evaluated environment generations.
3. First demand joins that evidence to the existing loader. Required path/digest/policy/ABI/target/dependency refusals must happen before executable mapping or constructor effects. This is the required contract, not a statement that every refusal is implemented on release.
4. The loader publishes a process-callable result only after query/signature admission. A runtime registry offset, metadata success, provider event counter or copied address cannot substitute for its session authority.
5. CPU calls retain their session pins through invocation. GPU submissions retain the required session and resource ownership until completion or cancellation reaches its real terminal boundary. A CPU call returning is not evidence that GPU work has finished.
6. Replacement creates a new admitted generation; existing work drains under its own retained pins. Close must respect the existing ownership checks. Do not promise immediate operating-system unmapping or reuse an expired session for new work.

Use the existing public typed failure/status model. Keep diagnostics such as artifact-not-found, digest refusal, ABI refusal and unavailable feature distinguishable wherever the current contract distinguishes them. A new refusal must be mapped through a reviewed, versioned compatibility path; this document adds no enum discriminants or wire fields. Scalar fallback is permitted only by the selected capability policy and must preserve the original application's results and errors. Effectful DB, network and GPU work executes once; shadow comparison is limited to pure bounded operations.

## Release state and pending integrations

| Slice | Release evidence boundary | Remaining work |
|---|---|---|
| Minimal image/startup | Lazy SIMD initialization, CPU-query separation and their scoped tests are landed | Full closure attribution, matched C inputs, optional-load traces and admitted Phase-5 release cohorts remain required. An older 13,704-byte Hello is not proof for this release's compiler/runtime pair. |
| CPU ISA and QEMU runner | Vector kernel sources and fixed-profile runner plumbing are present; real C kernel/PID checks are narrower evidence | Build and run actual Simple DB/HTTP binaries, including refusal and scalar fallback, for each claimed target/profile. QEMU correctness is not physical ARM/RVV performance. |
| Pre-open refusal and app consumers | Draft [PR #2762](https://github.com/ormastes/simple/pull/2762), source `af7524600bfc6394b825eb057fef6186620ba931`, is not release implementation | Compile the actual constructor-side-effect fixture and app consumers with an identified qualified producer. The proposed pre-open policy repair does not eliminate the separate digest/handle TOCTOU limitation. |
| Compiler support | Draft [PR #2761](https://github.com/ormastes/simple/pull/2761), source `3237ca2ae176f5158e90fce38f7c60e1a313d942`, is not a qualified compiler | New matching producer/runtime, exact-binary Hello, trait/enum/layout regressions and full bootstrap/core/MCP checks. The previous different-source compiler timeout is neither a pass nor a failure of this new source. |
| CUDA | Native device/session probes exist for specifically identified runtime archives | No Simple CUDA DB application pass is implied. The app PR's Simple facade pointer handling is distinct from the pending Rust native-all registry/generated-extern corrections and their runtime archive identity. |

Release state above is a dated inventory, not a substitute for checking a later PR head or release commit. Keep producer compiler, compiler source, consumer source, runtime archive, provider artifact and observer identities separate. Do not transplant old receipts onto new source or invalidate an in-flight build by changing its frozen inputs.

## Compatibility with Phase 5 size and loading gates

- Preserve NFR-001..007: below 2 MiB unstripped NoGC Hello; Linux release-small at most 15 KiB and 1.05 times the specified matched C program; admitted non-ELF allowances; interpreter startup/RSS within the selected Python budget; zero optional initialization without demand; no unrelated provider dependency.
- Retain at least 30 development or 100 release samples, exact link/strip inputs, toolchain and binary hashes, output checksums, p50/p95 and RSS. A 30-sample diagnostic cannot become release evidence by relabeling it.
- Keep image size, startup, warm requests, build cost and application throughput as distinct rows. A kernel microbenchmark does not qualify DB/web throughput. A speed change that grows text must state both effects; remove no diagnostics, unwind support or feature merely to meet a number.
- Join the same immutable cohort across closure/link inspection, provider events, application assertions and performance records. Missing target runtimes, unavailable hosts and unexecuted tests remain open; do not classify them as passing or unsupported by convenience.
- Use the existing [14-case acceptance plan](../../../03_plan/sys_test/item5_provider_size_acceptance_2026-10-02.md). I5-01/02/03 cover no-demand, activation and refusal; I5-05/10 cover concurrency and lifetime; I5-07 covers target parity; I5-11/12 cover matched size/startup; I5-13/14 cover command cutover and ownership. Keep the other cases and their requirements intact.

## Nonbreaking implementation order

Land this documentation alignment independently. Then freeze the shared owner/version map before source changes; add adapters within the existing owners rather than duplicating contracts. Qualify each changed boundary with its existing callers and positive/negative native fixtures before changing defaults. Build the compiler and app consumers as separately identified artifacts. Promote providers individually only after target, failure, lifetime and performance evidence exists; retain the existing rollback contract.

This update changes no executable source, package manifest, exported symbol, wire layout, release profile, runtime default or bootstrap command. Existing feature/build behavior is preserved by that source scope, not asserted from an unrun full bootstrap. Merge owner and final reviewer: the primary agent; parallel agents provide read-only source audits, with no lower-model sidecar acceptance delegated.

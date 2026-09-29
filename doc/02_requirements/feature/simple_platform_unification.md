<!-- codex-research -->
# Simple Platform Unification — Feature Requirements

**Date:** 2026-09-13
**Status:** selected requirements; implementation and qualification remain in progress

## Decision and authority

SimpleOS shall be a first-class target of one Simple platform, not a parallel
compiler/runtime universe. The parser, compiler, startup policy, loader policy,
configuration, provider selection, portable SOSIX semantics, debug schemas, and
artifact/release metadata are shared. Hosted providers and SimpleOS services
implement those contracts; privileged kernel/MMU/IPC/IRQ/DMA/driver mechanisms
remain platform-private.

The user selected this consolidated architecture on 2026-09-13. These are final
requirements, not options. Existing authorities retain their stable identities:

- `PF/REQ-001..008` and `PF/NFR-001..007` in the parser-framework documents;
- `EODL/REQ-001..016` and `EODL/NFR-001..012` in the environment-optimized
  dynamic-library documents;
- `SMPB/REQ-SMPB-001..013` and `SMPB/NFR-SMPB-001..004` in the SimpleOS
  multiplatform-build documents.

If this document and an inherited authority overlap, the stricter measurable
constraint applies. A planned type, adapter, test, or source review is not proof
that a requirement is implemented.

`AC-1..14` below refer to the acceptance criteria in
`.spipe/simple_infra_optimization_unified_simpleos/state.md`;
`UP-AC-001..006` refer to the integration rows in
`doc/03_plan/sys_test/simple_platform_unification.md`.

## Functional requirements

- **REQ-001 — One platform authority.** Each of environment snapshot, provider
  descriptor, variant admission, immutable binding, target identity, startup
  plan, loader lifecycle, image manifest, machine plan, QEMU launch plan, and
  release evidence shall have exactly one production authority. Legacy models
  shall be adapted during migration and then deleted or marked diagnostic-only;
  they shall not independently decide production behavior.

- **REQ-002 — Dependency boundary.** Shared product code shall depend on
  platform contracts and SOSIX, never directly on hosted APIs or SimpleOS
  kernel code. Platform providers may translate shared contracts into native
  mechanisms. Application code shall not use the private SimpleOS kernel ABI
  except through an explicitly privileged component.

- **REQ-003 — Shared parser platform.** The compiler frontend shall consume the
  parser platform through the selected `FrontendFacetV1`/parser adapter. One
  runtime shall support dialect-owned grammars/actions for Simple, SDN, and
  sosh while owning normalization, UTF validation, structural indexes,
  tokenization, region execution, incremental identity, cache protocol,
  backend selection, receipts, and fallback reporting. `PF/REQ-001..008`
  remain normative.

- **REQ-004 — Independent parser oracle.** The existing recursive-descent
  frontend shall remain an independent legacy oracle and migration fallback
  until canonical scalar output is qualified. Scalar, SIMD, and GPU providers
  shall share semantic output and cache identity only after forced-backend
  parity proves tokens, regions, actions/HIR, mappings, diagnostics,
  invalidation, and deterministic hash. GPU error recovery remains CPU-owned
  until separately qualified.

- **REQ-005 — Environment and variant authority.** One immutable,
  epoch-bound `EnvironmentSnapshotV1` shall separate host execution facts,
  generated-code target intent, policy, and CPU/GPU execution domains. The
  provider catalog and selector shall satisfy `EODL/REQ-001..016`: inert
  admission precedes executable mapping, `auto`/`prefer`/`max`/`require` remain
  distinct, selection is deterministic and explainable, dependency closure is
  quarantined on failure, and old generations drain before retirement.

- **REQ-006 — Orthogonal execution domains.** CPU ISA variants and GPU
  providers shall be sibling execution domains, not a single scalar-to-GPU
  ranking. A workload policy may compare already-admitted domain plans using
  retained crossover evidence. Availability alone shall not select GPU.

- **REQ-007 — Baseline-safe composition.** Kernel, early boot, init, loader,
  selector, and hosted baseline runtime shall execute using the baseline ISA
  without optional optimized providers. Static composition is permitted for
  tiny/embedded and early-boot profiles; hosted and SimpleOS userland may load
  optional verified providers through the same catalog.

- **REQ-008 — Shared startup and loader.** Startup shall purely decide what
  should run and emit one metadata-derived startup plan. Environment selection
  decides candidate admissibility; loader core decides dependency, symbol,
  relocation, cache, generation, and lifecycle behavior. File/memory/library
  operations shall pass through `LoaderProviderV1`. Existing competing startup
  and loader models shall be reconciled before a V1 serialization is frozen.

- **REQ-009 — Shared portable services.** VFS/path/namespace/file contracts,
  `ProcessLaunchSpecV1`, capability references, task/wait/cancellation/
  completion types, allocator algorithms, trace/debug/dump schemas, portable
  binary readers, artifact metadata, and provider lifecycle metadata shall be
  shared across hosted and SimpleOS providers. Kernel scheduling and privileged
  memory/device mechanisms remain separate implementations behind these seams.

- **REQ-010 — Compiler-host SOSIX completeness.** The ordinary Simple compiler,
  without a `SimpleOSCompiler` fork or compiler-specific OS shortcut, shall run
  under SimpleOS using SOSIX filesystem, VM, process, environment, time, random,
  task/wait, and library/provider services. It shall report its version, compile
  a source program inside the guest, and execute the guest-produced artifact.

- **REQ-011 — Canonical targets and products.** SimpleOS shall support canonical
  `x86_64-unknown-simpleos`, `aarch64-unknown-simpleos`, and
  `riscv64-unknown-simpleos` target triples initially, with CLI aliases such as
  `simpleos-x86_64` normalized by the canonical registry, while retaining the
  explicit SMPB catalog and its x86_32/RV32/ARM32 requirements. Host capability
  discovery shall never alter target code-generation semantics. A build shall
  expose distinct kernel, services, runtime, optional compiler, provider,
  symbols, filesystem/volume, manifest, and boot-image products.

- **REQ-012 — Persistent image model.** NVFS shall be the canonical SimpleOS
  root path, with boot carrier, root filesystem, logical volumes, immutable
  system snapshot, writable overlay, and user data represented separately.
  Image assembly shall verify every included artifact identity and produce a
  deterministic `SimpleOsImageManifestV1`; FAT32, DBFS, and NVFS shall not be
  mislabeled as interchangeable formats.

- **REQ-013 — Image profiles.** `dev`, `runtime`, and `minimal` profiles shall
  select documented product sets. Every profile shall remain baseline bootable;
  the `dev` profile includes compiler/interpreter/test/debug facilities, while
  `minimal` includes only required services, loader, and its target application.

- **REQ-014 — Backend-neutral machine plan.** One bounded, declarative
  `QemuMachineSpecV1` shall describe guest policy. A sealed
  `QemuLaunchPlanV1` shall resolve executable, accelerator, firmware, media,
  devices, paths, endpoints, and argv for Linux, Windows, macOS, and FreeBSD
  host adapters. Adapters own host discovery only; they shall not duplicate
  guest architecture policy. KVM, WHPX, HVF, NVMM, and TCG policy shall be
  explicit and auditable.

- **REQ-015 — QEMU is replaceable.** QEMU shall be one `MachineBackend` beside
  hardware and hosted simulation, all consuming `SimpleOsImageManifestV1`.
  Development VM reuse/control transport may accelerate push/exec/test, but
  cannot satisfy a cold-boot release gate or leak QEMU-only assumptions into
  boot architecture.

- **REQ-016 — Canonical CLI.** The shipped `simple` binary shall expose admitted
  `setup`, `os build`, `os image`, `os run`, `os shell`, `os test`, and
  `os bootstrap` projections plus `--show-plan` and `--print-command` inspection.
  It shall expose `os release` only when it can consume a verified immutable
  candidate without rebuilding or repairing it. `simple run SOURCE -t
  simpleos-*` shall select its runner from the same plans. Planned or source-only
  commands shall be labeled unavailable rather than advertised as working.
  Release publication remains separately authorized.

- **REQ-017 — Bootstrap chain.** Host bootstrap shall converge from the seed to
  parity-checked self-hosted stages and then cross-build the ordinary compiler
  for SimpleOS. `simple os bootstrap` shall build kernel/runtime/compiler/image,
  boot the guest, run guest `simple --version`, compile a fixture in the guest,
  run the guest-produced artifact, and retain bound evidence.

- **REQ-018 — Immutable release qualification.** Qualification shall hash an
  immutable candidate, derive an isolated writable test state, cold-boot through
  the release firmware path, mount NVFS, run SOSIX filesystem evidence, execute
  guest version/run/build/native checks, write a marker, reboot the same derived
  state, and read the marker. `ReleaseEvidenceManifestV1` shall bind candidate,
  derived state, boot sessions, compiler/source/output, persistence, logs, and
  receipts. Only the unchanged original candidate is eligible for promotion.

- **REQ-019 — Evidence and traceability.** Every requirement shall map to a real
  assertion or explicitly identified `MissingEvidence`/unsupported row.
  A real QEMU/TCG boot may prove guest-functional behavior, while source-only,
  modeled, or synthetic evidence cannot. Emulated execution shall not prove
  native-host/device performance or physical-hardware execution. Generated manuals, operator guides,
  architecture/design, tracking records, and final high-capability review shall
  describe the same admitted capabilities without placeholder passes.

- **REQ-020 — Infrastructure-plan closure.** Every open L0–L11 item in
  `simple_infra_optimization_parallel_plan_2026-09-08.md` shall have implemented
  behavior and authoritative evidence. A genuinely external blocker must retain
  an active requirement/TODO, owner, prerequisite, artifacts, exact resume
  command, and final reviewer; blocked or postponed rows do not count as feature
  completion.

- **REQ-021 — Release tiers and packages.** The release matrix shall classify
  targets as Tier A required, Tier B tested, Tier C compile-only, or Experimental.
  The initial required set is Linux x86_64 CLI, Windows x86_64 CLI, macOS arm64
  CLI, and SimpleOS x86_64 QEMU; SimpleOS RV64/AArch64 QEMU and FreeBSD host are
  initially tested-tier, and RV32 SimpleOS is initially compile-only. A SimpleOS
  package shall carry image, kernel ELF, symbols, manifest, checksums, default
  machine spec, and debug source maps; an SDK shall carry the compiler, sysroot,
  standard library, and per-target SimpleOS data. Tier promotion requires the
  evidence defined for that tier and shall not be inferred from compilation.

- **REQ-022 — Shared configuration dimensions.** The SDN configuration authority
  shall model host execution environment, target code-generation profile, and
  execution domain as independent dimensions. Host discovery may admit a host
  provider but shall never silently add target ISA/device features. Configuration
  and environment identities shall participate in cache, binding, startup,
  machine-plan, and evidence invalidation where they affect semantics.

## Acceptance and evidence mapping

| Requirement | Acceptance | Primary planned or existing evidence | Current authority status |
|---|---|---|---|
| REQ-001..002 | AC-2,6 | authority inventory, dependency-direction checks, legacy-owner reference audit, provider boundary tests | Planned/source slices; convergence incomplete |
| REQ-003..004 | UP-AC-001 / AC-3..4 | `test/03_system/app/compiler/feature/parser_framework_spec.spl`; `gpu_parser_readiness_property_spec.spl`; `canonical_parser_sharing_spec.spl`; PF test plan | Existing coverage plus planned unified gate; qualification incomplete |
| REQ-005..007 | UP-AC-002..003 / AC-2,5 | EODL system specs; environment-policy, adapter, startup-owner, provider ABI/lifecycle specs; EODL test plan | Existing/source slices; production admission incomplete |
| REQ-008..009 | AC-2,6 | startup/loader/provider unit and integration suites; unified system plan | Contract convergence and production cutover incomplete |
| REQ-010..13 | UP-AC-004..006 / AC-7,10 | SMPB specs; `simpleos_machine_catalog_projection_spec.spl`; image manifest/builder/NVFS specs; `simpleos_toolchain_deployment_desktop_boot_spec.spl` | Source contracts partly landed; live-guest evidence missing |
| REQ-014..16 | UP-AC-005 / AC-8..9 | QEMU machine/host/CLI projection specs and `--show-plan`/argv scenarios named in the unified test plan | Source contracts partly landed; admitted runner evidence missing |
| REQ-017..18 | UP-AC-006 / AC-10,12 | production toolchain deployment scenario; release evidence manifest unit spec; immutable-candidate/reboot scenarios in unified test plan | End-to-end release verifier not qualified |
| REQ-019 | AC-11..14 | requirements, NFR, architecture, design, system plan, generated manuals, guides, verify report, Astra review receipt | In progress |
| REQ-020 | AC-1,12 | L0–L11 weighted ledger, exact lane receipts and resume commands in the infrastructure plan | Open rows remain; not complete |
| REQ-021 | AC-7,9..12 | release target matrix, package-manifest inspection, per-tier qualification receipts | Planned; no release admission claimed |
| REQ-022 | AC-2,5..6 | host/target/domain cross-product fixtures plus cache/plan invalidation receipts | Planned; authority convergence incomplete |

## Scope exclusions

- This development authority does not authorize tagging, pushing, publishing,
  firmware flashing, destructive physical-media writes, or release promotion.
- Unavailable native hosts/devices may remain explicitly blocked, but their
  requirements remain active and prevent a false completion claim.
- Directory relocation alone is not required; single ownership and enforced
  dependency direction are required.

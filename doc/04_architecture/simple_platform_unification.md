<!-- codex-design -->
# Simple Platform Unification Architecture

**Status:** proposed integration architecture, 2026-09-13

## Decision

SimpleOS is a provider-backed target of one Simple platform. The normative
details remain in the existing parser-framework, environment-optimized dynload,
and SimpleOS multiplatform documents. This ADR defines their joins.

```text
products -> platform contracts -> SOSIX -> hosted/SimpleOS providers
                                      -> SimpleOS services -> private kernel ABI
```

Privileged kernel and driver mechanisms are `mdsoc_only`. Portable provider
admission, tracing, configuration, parsers, loader state machines, and artifact
metadata may use common MDSOC composition without weaving into kernel ownership.

## Versioned integration contracts

- `EnvironmentSnapshotV1`: immutable host/runtime/device facts.
- `ProviderDescriptorV1` and `VariantDescriptorV1`: inert admission metadata.
- `BindingPlanV1`: deterministic generation-pinned selection.
- `ParserProviderV1`: platform adapter/projection over the selected
  `FrontendFacetV1`; it does not define a second frontend ABI.
- `StartupLaunchPlanV1`: pure artifact-to-entry policy.
- `LoaderProviderV1`: file, mapping, protection, lookup, and cache operations.
- `VfsContractV1` and `ProcessLaunchSpecV1`: portable OS semantics.
- `SimpleOsImageManifestV1`: backend-neutral bootable product identity.
- `QemuMachineSpecV1` and `QemuLaunchPlanV1`: declarative guest policy and
  resolved host execution plan.
- `ReleaseEvidenceManifestV1`: binds build, boot, guest compiler, persistence,
  reboot, logs, and receipts to immutable digests.

These names are convergence targets. Existing `StartupPlanV1`,
`StartupLaunchPlan`, `StartupLoadPlan`, `SimpleOsPlatformBuildTarget`, `OsTarget`,
and `MachineProfile` must first be mapped to one authority; a new V1 type must
not become another parallel model.

## Authority boundaries

```text
StartupPlanner: requested interfaces and entry mode
EnvironmentAuthority: executable facts and policy projection
VariantSelector: eligible candidate ranking
LoaderCore: dependency/symbol/relocation/lifecycle state
LoaderProvider: OS mapping and native-library mechanisms
MachinePlanner: guest architecture/device policy
QemuHostAdapter: executable/accelerator/firmware/path discovery
ReleaseVerifier: evidence admission, never runtime selection
```

No owner may recompute another owner's decision. Every handoff carries an
identity/digest and bounded rejection or fallback reasons.

## Parser join

`ParserProviderV1` projects `FrontendFacetV1` through the parser framework's
`ParseDialect` data bundle, immutable arenas, ordered action sink, and legacy
bridge. Canonical scalar, SIMD, and GPU availability remains milestone-specific;
the architecture does not claim planned executors already exist. The independent
legacy parser remains an oracle and migration fallback. Backend
is excluded from semantic cache identity only for qualified grammar/platform
versions whose forced-backend outputs match. Error recovery remains CPU-owned
until a separate equivalence gate promotes it.

## SimpleOS build and run join

The build graph produces kernel, services, platform runtime, optional compiler,
provider variants, NVFS volumes, image manifest, and image. A machine backend
consumes the manifest. Development VM reuse may update a mutable dev overlay.
Release verification hashes an immutable candidate, derives an isolated writable
test disk/overlay, reboots that same test state for persistence proof, records
before/after identities, and promotes only the original admitted candidate bytes.
The image model separately identifies boot carrier, root filesystem, logical
volumes, immutable system snapshot, writable overlay, and user data; NVFS and
FAT32 are not interchangeable labels.

## Startup and hot paths

Startup performs one snapshot per environment epoch and catalog admission, then
reuses an immutable binding plan until affinity/domain, vector-state, policy,
device, loader capability, catalog, or artifact identity changes. Replacement
occurs at a safe boundary; retained pins drain before retirement. Parser
requests, loader lookups, and VM control requests
must not scan full trees, rediscover tools, or spawn discovery subprocesses.
Catalog and launch-plan caches invalidate on environment, policy, artifact,
firmware, executable, or machine-spec digest changes.

## Failure containment

- Baseline kernel/init/loader/selector never require optimized providers.
- `require` returns a typed requirement error; `prefer` records fallback.
- Provider quarantine invalidates affected dependency closures for new bindings;
  existing generation pins drain before their resources retire.
- A failed reusable VM is discarded; it cannot satisfy cold-boot release gates.
- Manifest or evidence digest mismatch fails closed before promotion.

## Consequences

The architecture removes parallel semantics while retaining platform mechanisms.
It adds explicit manifests and receipts, but they replace hidden detection and
host-specific policy. Directory convergence is optional and follows ownership
proof; it is not a prerequisite for the first vertical slice.

## Physical-provider completion boundary

Contract presence is not implementation evidence. Production image composition
requires native retained-root, no-follow, bounded-read, exclusive-publication,
durability, and cleanup mechanisms. Filesystem QEMU lanes reject required weak
provider symbols before launch. The compiler-in-guest cold-boot gate remains a
separate scenario and cannot be inferred from a filesystem fixture.

## Default CLI dispatch migration — 2026-10-01

The default non-debug `os run` source path now consumes the existing sealed
`QemuLaunchPlanV1` authority through `qemu_cli_plan_v1`. The inspection outcome
retains its plan; dispatch validates it and uses its exact executable/argv
through the bounded process facade. Existing artifact admission remains before
dispatch. This creates no new machine, target or provider policy authority.

Four represented named routes also consume sealed plans; other named/GUI
paths remain migration work. The slice has no admitted runtime
evidence and does not close REQ-001/014/016 or the umbrella. Its test/knowledge
gate is [the scoped plan](../03_plan/sys_test/simpleos_sealed_cli_dispatch.md).

`os.qemu_launch_resources_v1` is the shared explicit guest resource owner for
legacy and sealed launchers. It preserves memory/CPU overrides and the ten-core
default without importing the runner's cyclic target/build modules. These are
guest machine settings, independent of host provider admission or target ISA.

The catalog's CLI architecture projection accepts canonical SimpleOS rows,
their aliases and userland identities, while excluding hosted/kernel-only and
board identities. The runner delegates architecture resolution to this owner.
Explicit CLI arguments precede the environment default; unknown discovery is
refused rather than converted to an assumed x86_64 guest. The
[target-identity gate](../03_plan/sys_test/simpleos_cli_target_identity_2026-10-01.md)
is authored but native SSpec/docgen remains UNRUN.

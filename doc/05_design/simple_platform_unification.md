<!-- codex-design -->
# Simple Platform Unification Detail Design

**Date:** 2026-09-13

## Data flow

```text
TargetProfile + BuildProfile
  -> BuildGraph -> SimpleOsImageManifestV1 -> image
HostDiscovery + QemuMachineSpecV1 + image manifest
  -> QemuLaunchPlanV1 -> machine backend -> boot receipt
guest EnvironmentSnapshotV1 + VariantCatalog
  -> BindingPlanV1 -> startup/loader/parser providers
all receipts -> ReleaseEvidenceManifestV1
```

## Contract details

`SimpleOsImageManifestV1` contains schema/version, target tuple, profile, build
and source identities, kernel/services/runtime/provider artifacts and digests,
NVFS format/volume identities, firmware expectations, SOSIX version, entry
service, and debug-symbol/source-map references.

`QemuMachineSpecV1` contains guest target, firmware class, CPU model policy,
memory/CPU limits, storage declarations, display/network/input/serial devices,
accelerator policy, and backend-neutral timeout/control-channel policy.
It is formed by consolidating existing `SimpleOsPlatformBuildTarget`, `OsTarget`,
and `MachineProfile` projections. Four-host discovery logic is migrated from
`scripts/qemu/simple-qemu-settings.shs`, with explicit probe-to-fallback receipts,
rather than reimplemented beside it.

`QemuLaunchPlanV1` adds resolved host OS/arch, QEMU executable and version,
selected accelerator with fallback reason, firmware path/digest, normalized
arguments, temporary resources, control endpoints, and the input spec/image
digests. `--show-plan` renders this object; `--print-command` is a debug view,
not a second plan builder.

`ReleaseEvidenceManifestV1` records the immutable candidate digest, derived
writable-test identity, cold-boot identity, and ordered checks:
NVFS mount, SOSIX filesystem scenario, `simple --version`, guest `run`, guest
`build`, execution of the guest-produced artifact, persistence write, reboot,
persistence read on the same derived test state, before/after disk identities,
and artifact/log/capture digests. Only the original admitted candidate bytes are
eligible for release handoff.

Image metadata models carrier format, root filesystem, volume set, snapshot, and
overlay independently. Current FAT32 and DBFS-backed NVFS paths remain accurately
described during migration.

## Algorithms

Build planning delegates SimpleOS guest aliases/defaults to
`src/os/port/simpleos_multiplatform_build.spl` and delegates canonical tuple
authorization to the selected V2 target registry. Plans retain registry digest,
owner generation, and use identity. Proposed `simpleos-x86_64`-style UX aliases
do not rename current catalog targets until that owner admits them. Host facts
never enter target feature selection. Image assembly is deterministic over an
ordered manifest and fails for missing/digest-mismatched inputs.

Machine planning validates manifest/spec compatibility, discovers only the host
adapter inputs once, ranks admitted accelerators by policy, normalizes paths and
devices, then seals a launch plan. Execution cannot mutate the sealed plan.

Guest provider selection filters descriptors by contract/ABI/trust and exact
environment facts before ranking. CPU and GPU candidate sets are ranked within
their domains; workload policy compares admitted domain plans using retained
crossover evidence.

## CLI projection

`simple setup` writes discoverable host defaults without target assumptions.
`simple os build`, `image`, `run`, `shell`, `test`, and `bootstrap` are projections
over shared plans. `simple os release` consumes a verified immutable candidate;
it does not repair tests, manifests, or images.

## Error model and observability

Use typed errors for target normalization, missing artifacts, incompatible image
and machine specs, unavailable required acceleration/provider, firmware lookup,
boot timeout, guest protocol failure, persistence failure, and evidence mismatch.
Expose timings for build/image assembly, environment/catalog selection, launch,
boot-to-ready, guest request latency, parser backend latency, and max RSS/device
memory. Receipts must remain bounded and redact host secrets.

## Migration rule

Each adapter begins behind the current behavior. Cutover requires parity and a
single authority assertion. Duplicate detectors, startup branches, parser paths,
and QEMU scripts are deleted only after references and release evidence show the
new owner is complete.

Before freezing `StartupLaunchPlanV1`, reconcile the existing frozen
`StartupPlanV1`, metadata-derived `StartupLaunchPlan`, and local
`StartupLoadPlan` through adapters and nominate one serialization authority.
Loader extraction begins by removing direct POSIX/runtime access from SMF
providers behind `LoaderProviderV1`; compiler cache/JIT/symbol ownership moves
only after dependency-direction tests exist.

## Native image and guest-evidence join

The hosted-safe provider retains the root descriptor through close. Relative
components are opened without following links; publication uses a sibling
staging file, syncs bytes, installs without replacement, and syncs the parent.
The image owner emits its manifest only after exact reread and successful close.

Before filesystem boot, artifact admission requires strong serial, NVMe, FAT32,
and runtime providers. Compiler bootstrap additionally binds guest version,
build, execution, and persistence receipts to one image and boot session.

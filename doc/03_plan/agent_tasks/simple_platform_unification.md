# Agent Task Plan: Simple Platform Unification

## Ownership

- Merge owner: primary implementation session for `simple_platform_unification`.
- Final reviewer: best available normal/highest-capability model.
- Documentation lanes used: primary synthesis; Astra architecture review;
  repository-reality audit with parser/environment and SimpleOS/QEMU sublanes;
  Astra test/release review; developer-guide lane.
- Before implementation fan-out, freeze interface names, scenario `step("...")`
  strings, setup/checker helpers (reusing EODL helpers), and fail-fast
  placeholders. Each inherited requirement gets happy, boundary, and error cases
  with real assertions and zero-stub generated manuals.

## Ordered work

1. Verify existing route ownership; propose registry changes separately rather
   than inventing a new authority during implementation.
2. Inventory and reconcile the three startup plans and three overlapping QEMU/
   target models; nominate serialization and discovery authorities.
3. Freeze image, machine, launch-plan, and release-evidence V1 value contracts.
4. Add deterministic codecs/digests and unit tests without behavior cutover.
5. Adapt the current x86_64 SimpleOS build into `SimpleOsImageManifestV1`, with
   separate carrier, filesystem, volume, snapshot, and overlay identities.
6. Implement one QEMU plan builder plus Linux adapter, migrating existing
   four-host shell discovery. A legacy runner may supply
   diagnostic evidence during cutover but cannot issue release authority.
7. Add macOS, Windows, and FreeBSD host adapters using the same machine spec.
8. Project build/image/run/show-plan CLI commands over the shared plans.
9. Complete canonical scalar coverage and legacy reset/append/interpolation/
   diagnostics parity; connect guest selection without changing parser default.
10. Complete SOSIX compiler-host filesystem, VM, process, environment, time,
   entropy, worker wait/wake, and library-discovery obligations.
11. Complete shared-driver migration and same-boot command/evidence transport,
    then the cold-boot x86_64 guest compiler and NVFS persistence gate using
    a derived writable state while preserving original candidate bytes.
12. Promote riscv64 and aarch64 from the same evidence protocol.
13. Promote SIMD parser variants in measured order; stabilize cache identity.
14. Add GPU parser only after CPU canonical parity and crossover evidence.
15. Delete superseded host QEMU policy, detector, parser, and startup duplication.
16. Run production verification and prepare immutable-candidate release handoff;
    publication is a separate authorized release operation.

## Parallel boundaries for implementation

After contracts freeze, safe lanes are manifest/codecs, QEMU host adapters, CLI
projections, guest evidence protocol, and parser qualification fixtures. Each
lane declares write scope, dependencies, acceptance IDs, outputs, and review
gate. No sidecar may rename shared contracts or define alternate plan, receipt,
setup, or checker helpers.

All lanes share one maximum three-cycle correction counter. Target tier matrix
and fresh-boot/same-test-volume persistence gates are declared before
qualification begins.

## 2026-09-13 implementation checkpoint

- Catalog projection: source-landed and Astra-reviewed. Migrated runner and
  machine-profile entrypoints materialize one catalog and fail explicitly for
  unknown targets. Executable/manual/performance evidence awaits an admitted
  pure-Simple runner; legacy scenario-disk pre-resolution remains later work.
- Image manifest V1: source-landed and Astra-reviewed. It separates artifacts,
  carrier, NVFS root/volumes, snapshot, writable overlay, baseline providers,
  firmware, SOSIX, and entry identity. It is descriptive only and grants no
  loader or release authority.
- Canonical identity: source-reviewed fixture pins 2,037 canonical bytes and
  SHA-256 `87fbdf46453452b6f9f6f46c028489b4b59914754049dfb3ceee6a1590c5e9bb`, plus
  exact-maximum and overflow-rejection capacity cases.
- Builder boundary: source-landed fail-closed adapter accepts only independently
  verified, materialized carrier/NVFS-root facts. It explicitly rejects the
  current descriptor fallback and marker-only FAT32 path.
- NVFS emission: source-landed builder hashes the exact geometry-checked device
  bytes before writing and issues a materialization receipt only after a
  successful write; the adapter consumes this receipt without granting release
  authority.
- x86_64 composition: source-landed validation distinguishes the kernel and
  userland triples, checks baseline/profile contents, and binds the candidate
  to the exact NVFS receipt without granting release authority.
- Artifact inclusion: source-landed producer writes authoritative seed bytes,
  reopens persisted DBFS state without compatibility-cache reconstruction,
  verifies length/SHA-256, binds rows to the final root digest, and only then
  projects composer inputs.
- QEMU plans: source-landed sealed machine/launch contracts project guest policy
  from the shared target catalog and bind supplied host facts with
  KVM/HVF/WHPX/NVMM/TCG auto/prefer/require semantics.
- Catalog identity repair and four typed host adapters are source-landed and
  reviewed. Adapters consume target-bound probe facts and preserve existing
  KVM/HVF/WHPX/NVMM-to-TCG policy without owning guest architecture decisions.
- The canonical settings probe owner and CLI `--show-plan`/`--print-command`
  projections are source-landed. Structured lane policy gives sealed-plan
  parity for all six defaults; five default CLI targets are inspectable when
  their real files and tools exist. Normal launch remains on the legacy runner
  until qualified execution proves parity.
- x86_32 compatible executable aliasing, named x86/RISC-V and NVMe scenario
  projection, and inert Windows argv display are source-landed and
  Astra-reviewed. Unsupported ARM/forwarded-network shapes remain fail-closed.
- Next: qualify exact legacy/sealed argv parity on an admitted self-hosted
  runtime, then cut normal launch over without retaining two policy owners.
- Release evidence V1 is source-landed and Astra-reviewed. It is a bounded,
  backend-neutral admission record with cross-session binding, causal receipt
  windows, derived-state persistence identity, and consume-once replay checks;
  evidence producers and actual guest qualification remain open.
- Core frontend parser dispatch now crosses `ParserProviderV1`; legacy remains
  the only executable/default provider and independent oracle. Candidate
  scalar/SIMD/GPU routes reject before mutation pending qualification, and the
  native FlatAstBridge migration is still open.
- StartupPlanV1 and legacy StartupLoadPlan have pure fail-closed projections
  into canonical StartupLaunchPlan. Physical launch still needs cutover and
  admitted parity evidence.
- ProcessLaunchSpecV1 and the SimpleOS SOSIX process-service adapter are
  source-landed. Service-owned liveness/grant resolution and kernel execution
  remain open; no compiler-specific shortcut was added.
- Host environment parser admission now uses the frozen environment-variant
  authority with host/target separation and orthogonal CPU/GPU domains. Live
  GPU inventory and the inherited x86 VBMI validation-mask correction remain
  open.
- Release-evidence production stopped after its third rejected review cycle.
  Resume only after designing an atomic ledger predecessor/sequence transition
  and one prepare/sign/finalize claim identity; do not reuse the rejected draft
  as release authority.
- Blocker: no admitted pure-Simple runner is available here. Rust-seed results
  are diagnostic and cannot close acceptance or justify a capped-lane retry.
- Runtime selection now honors canonical `SIMPLE_BIN` while retaining the
  bootstrap-specific variable as the higher-priority override.
- Active physical slices: native retained-root artifact I/O and pre-QEMU strong
  provider admission. Merge owner: primary Codex; final reviewer: Astra.
- `x64-nvme-fat32` is never compiler-in-guest evidence. Add a distinct compiler
  cold-boot scenario after image and process providers become physical.

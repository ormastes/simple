<!-- codex-research -->
# Simple Platform Unification: Consolidated Local Research

**Date:** 2026-09-13  
**Status:** umbrella integration research; preserves existing feature decisions

## Supplied decision

The user supplied the consolidated target architecture titled **Simple Platform
Unification, Parser Sharing, Environment-Optimized Dynload, and SimpleOS Release
Architecture**. Its controlling decision is retained here:

> SimpleOS is a first-class deployment target of the same Simple platform, not
> a separate build universe.

The proposed common platform owns parsers, AST/HIR/MIR contracts, module
resolution, startup planning, loader semantics, configuration, provider
selection, async completion, VFS/process contracts, debugging, tracing, and
artifact metadata. Hosted systems and SimpleOS differ at provider boundaries;
the SimpleOS kernel alone owns scheduling, MMU, IPC, IRQ, DMA, drivers, and boot.

## Existing repository lanes

This is not a greenfield architecture. Three selected lanes already contain the
normative detail:

1. `parser_framework` freezes shared parse contracts, deterministic scalar
   results, SIMD structural indexes, bounded GPU regions, incremental identity,
   demand-driven allocation, and backend parity evidence.
2. `environment_optimized_dynamic_libraries` freezes
   `EnvironmentSnapshotV1`, `VariantDescriptorV1`, `BindingPlanV1`, admission
   before executable mapping, orthogonal CPU/GPU domains, generation-pinned
   lifecycle, explain receipts, and baseline-safe startup.
3. `simpleos_multiplatform_build` owns SimpleOS target/build portability and
   host-independent build semantics.

The umbrella must compose these contracts. It must not introduce a second
`ParserProvider`, environment detector, loader selector, or QEMU policy source.

## Repository findings and gaps

- Parser and environment-dynload architecture/design documents are mature and
  significantly more detailed than the umbrella proposal. Integration should
  reference them and add cross-lane invariants.
- The current SimpleOS multiplatform architecture/design documents are narrower:
  architecture portability exists, but a complete shared image manifest,
  `QemuMachineSpecV1`, target-native compiler gate, and unified CLI lifecycle are
  not yet expressed as one release architecture.
- Existing worktree changes touch parser and dynload research. This document is
  therefore additive and does not alter those files.
- The knowledge registry has an exact route for environment-optimized dynamic
  libraries but not for this umbrella. The retained receipt records that gap.
- Parser-framework code is currently scalar/lexical Wave 1: optimized requests
  demote to CPU, `auto` selects scalar, and structural-index, parallel-lex, and
  incremental modules remain incomplete. The compiler still enters through the
  legacy `ParserModule`; there is no production `--parser=` surface.
- Environment/catalog/binding candidates exist, but live host probing is not yet
  the single authority and CPU/SIMD detection remains duplicated. These files
  are active candidate work, not proof of production cutover.
- Startup currently has `StartupPlanV1`, `StartupLaunchPlan`, and a local
  `StartupLoadPlan`. Reconcile/adapt these before freezing another plan type.
- Loader ownership still crosses the intended boundary: compiler loader code
  owns major mechanisms and SMF providers directly import POSIX/runtime access.
- QEMU concepts already exist as `SimpleOsPlatformBuildTarget`, `OsTarget`, and
  `MachineProfile`; four-host discovery also exists in shell while the Simple
  runner bypasses it. The plan must consolidate and migrate, not add a fourth
  independent model.
- Image construction is FAT32-centric while optional NVFS is DBFS-backed and is
  also described as a carrier. Future manifests must distinguish carrier,
  filesystem, volume, and overlay identities.
- Current CLI supports only `os build`, `run`, `test`, and `targets`. Other
  commands in the supplied architecture are explicitly target UX.
- The in-guest compiler is an x86_64-focused tool and release-grade native guest
  execution remains blocked. Phase 10 depends on SOSIX exec/process completion,
  shared-driver migration, same-boot control/evidence, and plan reconciliation.

## Consolidated invariants

1. Host execution, code-generation target, and optional execution domain are
   separate identities. No host feature may leak into target semantics.
2. Capability admission answers *can execute*; selection policy answers *should
   execute*. `require` fails closed; `prefer` may fall back; `max` caps selection.
3. CPU ISA variants and GPU providers are siblings in different execution
   domains, never a single scalar-to-GPU ranking ladder.
4. Kernel, init, loader, and selector remain baseline-safe. Optional provider
   failure cannot prevent boot.
5. Parser semantic cache keys omit backend only after forced-backend equality is
   proven for the exact grammar/platform versions.
6. Startup selects requested interfaces, the environment authority admits
   candidates, and the loader binds immutable plans. These are separate owners.
7. Binary parsing is portable; mapping and executable-memory authority remain
   provider-specific.
8. QEMU is a machine backend consuming an image manifest, not an architectural
   dependency of SimpleOS.
9. Release truth includes cold boot, compiler execution in the guest, guest
   compile/execute, persistence, reboot, and manifest-bound evidence.

## Recommended ownership convergence

Prefer contract-first modules under existing common/platform namespaces rather
than a disruptive immediate directory move. New versioned contracts should be
introduced at their existing semantic owner, adapters should migrate consumers,
and duplicate implementations should be deleted only after parity gates pass.

The first integration slice is metadata-only: define the image, machine,
launch-plan, and release-evidence contracts and connect them to existing parser,
variant, startup, loader, SOSIX, and SimpleOS target identities. It changes no
runtime behavior and creates the stable join needed by later slices.

## Research conclusion

The supplied architecture is directionally consistent with repository decisions.
The key correction is sequencing: do not begin with directory migration, GPU
parsing, or a broad CLI rewrite. Freeze the cross-lane identities and receipts,
then connect one baseline x86_64 SimpleOS build/image/run/bootstrap vertical
slice. Promote additional architectures and optimized parsers only from measured,
manifest-bound parity evidence.

## 2026-09-13 execution findings

- The bootstrap wrapper originally ignored canonical `SIMPLE_BIN`; its specific
  override and canonical runtime variable need explicit precedence.
- `x64-nvme-fat32` is a filesystem fixture, not compiler-in-guest evidence. Its
  17 KiB diagnostic image contained weak zero-return serial, NVMe, FAT32, and
  runtime helpers and must be rejected before QEMU.
- The corrected ELF32/EM_386 Multiboot envelope reaches `[BOOT64] call _start`;
  artifact formatting is no longer the immediate blocker.
- Production `simple os image` remains blocked on native retained-root
  no-follow read, exclusive durable publish, and close operations.

# SimpleOS Combined Signed Catalog Boot — Agent Handoff

## Scope

Join the signed nine-record Clang/sysroot release and five-record primary-tool
release before the boot catalog's single irreversible seal. This plan does not
claim that an image was built or a guest launched.

## Shared interfaces

- Host transaction: `HostedSafeArtifactBundleNGrantV1`, one retained root,
  fourteen bounded payload slots, fourteen SCR1 slots, and exactly two named
  release descriptors.
- Guest preparation: `CombinedToolchainCatalogMediaBootPreparedV1` with one
  shared nonempty `release_id`.
- Guest commit: `installed_artifact_boot_compose_and_populate_v1(nil, clang,
  primary)`; primary owns the sole Simplebox row; accepted count is 14.
- Architecture adapters: x86_64, ARM64, and RV64 delegate to the shared owner.

## Work matrix

| Lane | Owner | State | Unblock condition / evidence |
|---|---|---|---|
| Retained-root fourteen-payload host transaction | installer owner | implemented, unverified | Focused owner/spec evidence proving bounded staging, two descriptors, rollback, and atomic publish. |
| Combined boot authentication and single seal | loader owner | implemented, unverified | Focused spec plus live boot receipt proving both releases authenticate before mutation and catalog seals once with 14 records. |
| x86_64 adapter | x86 loader owner | implemented, unverified | Fresh x86_64 guest filesystem compile/link/run and primary-tool receipt. |
| aarch64 adapter | ARM loader owner | implemented, unverified | Fresh aarch64 guest filesystem compile/link/run and primary-tool receipt. |
| riscv64 adapter | RISC-V loader owner | implemented, unverified | Fresh riscv64 guest filesystem compile/link/run and primary-tool receipt. |
| FAT32 materializer | image/filesystem owner | incomplete | Replace the x86_64-only/descriptor fallback split in `ImageBuilder._materialize_primary_artifact` with a target-aware FAT32 producer; retain exact installed-byte and guest-launch receipts. |
| DBFS materializer | DBFS owner | missing | Implement atomic population of payload/SCR1/trust/descriptors into a boot-mounted DBFS image; metadata selecting `dbfs` is insufficient. |
| NVFS materializer | NVFS owner | missing | Implement atomic population of payload/SCR1/trust/descriptors into a boot-mounted NVFS image; metadata selecting `nvfs` is insufficient. |
| i686 sysroot/catalog | x86-32 toolchain owner | blocked | Add i686 package/catalog target, per-target sysroot, CRT/syscalls/libc/Simple runtime, linker layout, signed payload receipt, image adapter, and live FS execution. |
| armv7 sysroot/catalog | ARM-32 toolchain owner | blocked | Extend `src/os/port/llvm/sysroot.shs` beyond driver target mapping with ARMv7 runtime/CRT/syscall/sysroot ownership, then add catalog/image/live evidence. |
| riscv32 sysroot/catalog | RV32 toolchain owner | blocked | Extend `src/os/port/llvm/sysroot.shs` beyond driver target mapping with RV32 runtime/CRT/syscall/sysroot ownership, then add catalog/image/live evidence. |

## Required scenario steps

- `step("Publish one authenticated combined release")`
- `step("Authenticate both descriptors before catalog mutation")`
- `step("Seal exactly fourteen records once")`
- `step("Launch Clang hello world from the mounted filesystem")`
- `step("Launch a primary tool from the mounted filesystem")`
- `step("Reject substituted media before spending launch authority")`

Unavailable rows must fail or report `blocked`; they may not use placeholder
passes or `skip()`. Sidecar lanes: N/A for this documentation-only handoff.
Merge owner: `/root`. Final reviewer: an independent normal/highest-capability
agent. Current implementation and all runtime claims are **unverified**.

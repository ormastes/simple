<!-- codex-design -->
# SimpleOS ARM QEMU FS Toolchain Verification Architecture

This rollout defines one ARM verification contract across `scripts/make_os_disk.shs`,
`src/os/qemu_runner.spl`, the ARM fs-exec entrypoints, and the
launcher/VFS/loader stack.

## Contract Boundaries

- `scripts/make_os_disk.shs` owns host-side image construction and staging of
  the toolchain artifacts, manifests, proof assets, and marker-bearing SMFs.
- `src/os/qemu_runner.spl` owns scenario selection, disk-image materialization,
  host-side image validation, QEMU launch wiring, and serial acceptance checks.
- ARM fs-exec entrypoints own bootstrapping the bounded ARM guest lane without
  claiming wider desktop/runtime closure.
- `src/os/services/vfs/arm_fs_exec_vfs.spl` owns `/sys/apps` to FAT32 aliasing
  and byte resolution for the ARM acceptance media.
- the loader/launcher stack owns turning VFS-resolved bytes into process-backed
  launch proofs and native-toolchain launch markers.

## Shared ARM Verification Contract

The shared ARM contract is architecture-neutral at the verification layer:

- default ARM QEMU targets route to fs-backed verification scenarios
- the required staged app set is `simple_compiler`, `simple_loader`, `llvm`,
  `clang`, and `rust`
- the required live acceptance subset is `simple_compiler`, `simple_loader`,
  `clang`, and `rust`
- the required host checks include manifests, versions, lane metadata, and
  proof assets
- the required guest checks include VFS reads plus process-backed launch
  markers

This boundary lets ARM32 and ARM64 share the acceptance definition even when
their boot mechanics differ.

## Per-Architecture Boot Boundary

The following remain architecture-specific:

- QEMU system binary, CPU, machine, and loader arguments
- boot entry file and linker shape
- ARM32 versus ARM64 serial formatting quirks
- any temporary guest-side trace differences needed to get stable output

The verification layer must not force these into one implementation. The
architecture only requires both ARM lanes to satisfy the same staged-file and
serial-marker contract.

## Verification Data Flow

1. `scripts/make_os_disk.shs` seeds FAT32 media with the ARM toolchain app set,
   manifests, version files, and proof assets.
2. `src/os/qemu_runner.spl` validates those staged artifacts before boot and
   selects the ARM fs-exec target for the scenario.
3. the ARM guest boots, mounts the FAT32-backed VFS lane, and resolves each
   `/sys/apps/...` path through the alias and reader helpers.
4. the loader and launcher paths emit stable process-backed and native-toolchain
   launch markers into serial output.
5. `src/os/qemu_runner.spl` accepts success only when all required serial
   fragments are present.

## Deduplication Shape

Shared helper extraction should target:

- required marker-set construction
- host validation shell command construction
- disk path lookup for ARM fs-exec images
- scenario-to-target routing helpers
- missing-marker reporting

Deduplication should not collapse:

- ARM32 and ARM64 guest entry implementations
- architecture-specific trace workarounds
- per-arch boot command differences in QEMU

The extracted helpers should be reusable by later RISC-V and x86 filesystem
verification lanes, but ARM is the first acceptance target and therefore sets
the contract.

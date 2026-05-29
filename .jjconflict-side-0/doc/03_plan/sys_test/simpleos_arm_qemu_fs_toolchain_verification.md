<!-- codex-design -->
# SimpleOS ARM QEMU FS Toolchain Verification Plan

This document is the primary acceptance plan for filesystem-backed tool launch
under ARM QEMU. It replaces the blocker-style narrative in
`doc/08_tracking/todo/simpleos_fs_exec_qemu_blockers_2026-04-22.md` as the
source of truth for success criteria, verification commands, and staged
follow-up work.

## Acceptance Target

- `arm64-virtio-fat32-smf` and `arm32-virtio-fat32-smf` are the default ARM
  QEMU verification lanes.
- Passing ARM verification requires guest launch from `/sys/apps`, not just
  host-side disk staging.
- The required guest proofs are `/sys/apps/clang`, `/sys/apps/rust`,
  `/sys/apps/simple_compiler`, and `/sys/apps/simple_loader`.
- `/sys/apps/llvm` remains part of host image and metadata validation, but ARM
  live acceptance centers on `clang`, `rust`, `simple_compiler`, and
  `simple_loader`.
- The current host LLVM/native-build environment can still block some
  non-ARM-native lanes; that does not weaken the ARM fs-launch contract.

## Verification Phases

### Phase 1: Host Image Validation

Prove the staged FAT32 image contains the required SMFs, manifests, versions,
and toolchain proof assets before QEMU boots.

Required host-side evidence:

- `SCOMPSMF.SMF`, `SLOADSMF.SMF`, `CLANGSMF.SMF`, `RUSTSMF.SMF`
- `LLVMSMF.SMF` as metadata coverage
- `CLANGMAN.TXT`, `RUSTMAN.TXT`, `LLVMMAN.TXT`, `TOOLSET.SDN`
- version files such as `CLANGVER.TXT` and `RUSTVER.TXT`
- toolchain proof assets such as
  `/usr/share/simpleos/toolchain/clang/pipeline.step` and
  `/usr/share/simpleos/toolchain/rust/pipeline.step`

This phase is satisfied only when the disk image validates the staged
filesystem contract for both ARM32 and ARM64.

### Phase 2: Guest VFS Resolution

Boot the ARM guest through the fs-backed QEMU lane and prove VFS resolution for
each required app under `/sys/apps`.

Required guest-side evidence:

- serial markers showing VFS reads for `/sys/apps/simple_compiler`
- serial markers showing VFS reads for `/sys/apps/simple_loader`
- serial markers showing VFS reads for `/sys/apps/clang`
- serial markers showing VFS reads for `/sys/apps/rust`

Metadata-only disk staging does not satisfy this phase.

### Phase 3: Guest FS-Backed Launch

Prove each required app executes through the filesystem-backed loader path and
emits stable launch markers.

Required guest-side evidence:

- serial markers showing process-backed launch for `simple_compiler`
- serial markers showing process-backed launch for `simple_loader`
- serial markers showing process-backed launch for `clang`
- serial markers showing process-backed launch for `rust`
- serial markers showing native-toolchain launch for `clang` and `rust`
- `TEST PASSED`

The lane is not green if the guest only reads bytes or validates manifests.

### Phase 4: ARM Deduplication Cleanup

Prove ARM32 and ARM64 share the verification contract without flattening real
platform differences.

Required shared-helper scope:

- required tool/app marker sets
- expected serial marker fragments
- disk-image path selection
- scenario-to-target fs-exec routing
- common host-side validation command construction

Explicit non-goal:

- do not force one shared guest entry implementation while ARM32 and ARM64
  still emit different trace and text forms

## Required Commands

Host-side disk/image validation:

```sh
sh scripts/make_os_disk.shs 64 build/os/fat32-arm64.img "" arm64
sh scripts/make_os_disk.shs 64 build/os/fat32-arm32.img "" arm32
```

Live guest verification:

```sh
bin/simple os test --scenario=arm64-virtio-fat32-smf
bin/simple os test --scenario=arm32-virtio-fat32-smf
```

Unit/spec verification:

```sh
bin/simple test test/unit/os/qemu_runner_spec.spl
```

## Unit Coverage Contract

`test/unit/os/qemu_runner_spec.spl` must keep explicit coverage for:

- default ARM QEMU routing to the fs-exec acceptance targets
- ARM32/ARM64 disk image path selection
- host-side staged file validation for required SMFs and manifests
- shared ARM serial marker expectations for both architectures
- scenario-to-target routing that preserves per-arch boot handling

Any new shared ARM helper extraction must add spec assertions for both ARM32 and
ARM64 marker sets.

## Pass Criteria

All of the following must be true:

- host validation confirms staged `clang`, `rust`, `simple_compiler`, and
  `simple_loader` artifacts
- host validation still confirms `llvm` metadata/manifests as part of the
  broader toolchain image contract
- guest serial output confirms VFS resolution for each required app
- guest serial output confirms process-backed launch for each required app from
  `/sys/apps`
- guest serial output confirms `clang` and `rust` native-toolchain launch
  markers
- no acceptance step passes on disk metadata alone without a guest fs-launch
  proof

## Follow-Up Work

After the acceptance lane stays green, continue with:

1. remove stale `hello_world.smf` comments and helper naming that still
   describe the older ARM probe shape
2. extract the shared ARM verification helpers first, but shape them for later
   RISC-V and x86 reuse
3. keep ARM32-specific trace/serial quirks isolated behind shared marker and
   validation helpers
4. advance runtime and scheduler work only after the fs-backed ARM launch
   contract remains explicit and enforced

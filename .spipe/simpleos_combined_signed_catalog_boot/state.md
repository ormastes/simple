# Feature: SimpleOS Combined Signed Toolchain And Primary Catalog Boot

## Task Type

feature

## Refined Goal

Publish the nine Clang/sysroot artifacts and five primary-tool artifacts as one
release identity, authenticate both complete descriptor sets before mutation,
and populate the boot catalog exactly once on x86_64, aarch64, and riscv64.
Keep filesystem materialization, launch, and unavailable 32-bit rows visible as
separate acceptance gates.

## Acceptance Criteria

- AC-1: Image production reads all fourteen payloads through one retained-root,
  bounded transaction, stages one SCR1 per payload and both release
  descriptors, and rolls back atomically on replacement, short read, digest
  drift, descriptor drift, or incomplete staging.
- AC-2: Guest boot authenticates the complete Clang and primary-tool releases
  before opening the irreversible installed-catalog transaction, requires one
  nonempty release ID shared by both descriptors, gives the primary plan sole
  ownership of `/bin/simplebox`, and seals exactly fourteen records once.
- AC-3: x86_64, aarch64, and riscv64 image/boot adapters call the same combined
  owner; no architecture-specific catalog semantics or second seal exists.
- AC-4: FAT32, DBFS, and NVFS each materialize the exact payload, SCR1, trust,
  and descriptor bytes into their boot-visible filesystem and retain a live
  guest receipt proving authenticated launch of Clang hello-world and one
  representative primary tool.
- AC-5: Live x86_64, aarch64, and riscv64 QEMU evidence proves filesystem open,
  catalog authentication, exact target/digest, Clang compile, LLD link,
  hello-world output/exit/reap, primary-tool output/exit/reap, and rejection of
  a substituted descriptor or payload.
- AC-6: i686, armv7, and riscv32 remain blocked until target-specific LLVM
  cross configuration, sysroot/CRT/syscall/libc/Simple-runtime archives,
  linker layout, target-native payload receipts, image materialization, and
  live guest execution exist; no 64-bit receipt promotes a 32-bit row.

## Current State (2026-08-25, static review only)

- Implementation is present but **unverified**. No test, build, SPipe, image,
  QEMU, benchmark, or optimizer command was run in this lane.
- AC-1 through AC-3 have source and focused-spec changes under review, centered
  on `src/os/installer/hosted_safe_artifact_io_v1.spl`,
  `src/os/installer/image_builder.spl`,
  `src/os/kernel/loader/combined_toolchain_catalog_media_boot_v1.spl`, and the
  three 64-bit architecture adapters. Static presence is not PASS evidence.
- AC-4 and AC-5 are open. `ImageBuilder._materialize_primary_artifact` creates
  a real disk only for non-installer x86_64 through the FAT32 disk command;
  other target/backend combinations currently end at an artifact descriptor.
  DBFS/NVFS selection metadata is not a payload materializer or launch receipt.
- AC-6 is blocked. `src/os/port/llvm/sysroot.shs` has runtime construction only
  for x86_64 and aarch64 and rejects other triples at its libc/runtime owner;
  it also selects a dedicated sysroot only for aarch64. The LLVM driver maps
  armv7/riscv32 but that mapping alone does not create a valid sysroot. The
  combined catalog request currently admits only x86_64/aarch64/riscv64.

## External Resume Evidence

Owner: SimpleOS filesystem/image integration lane. Final reviewer: independent
normal/highest-capability reviewer.

Resume only after a prepared self-hosted Simple runtime and target payloads are
available. Run the lane's focused spec once, then produce fresh isolated images
for each 64-bit ISA and each FAT32/DBFS/NVFS backend through the canonical
SimpleOS QEMU settings/collector. Retain image digest, descriptor release ID,
target triple, filesystem generations, catalog count/seal receipt, exact argv,
bounded stdout/stderr, exit/reap, and substitution-rejection evidence. The
exact commands must be added by the materializer implementation owner; no
current command can truthfully exercise all nine filesystem/ISA rows.

## Phase

implement-in-progress; runtime verification blocked/open

## Log

- 2026-08-25: Added narrow tracking for the combined fourteen-record release.
  Recorded implementation as unverified and retained all live and 32-bit gates.

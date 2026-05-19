# SimpleOS In-Guest Toolchain Execution Gap

Date: 2026-05-05

## Problem

The current SimpleOS QEMU evidence proves that Clang and Rust toolchain app
fixtures are present on the FAT32 filesystem, readable through the guest VFS,
valid as x86_64 SMF executable envelopes, and backed by embedded ELF marker
stubs plus manifest/proof files.

It does not prove that the guest can execute a real Clang or Rust compiler
process and produce a compile artifact from an input source file.

## Current Evidence

- `x64-desktop-disk` and `x64-desktop-uefi` emit process-backed `clang` and
  `rust` launch markers plus source/project-input markers that bind the smoke
  launch evidence to guest-side proof paths. These desktop lanes now route the
  Clang/Rust smoke launches through the same x86_64 filesystem-exec spawn
  bridge and require `spawn:image ... stub_bytes=... argv_count=2 env_count=0`
  markers in the serial contract.
- `x64-toolchain-vfs-probe` reads `/sys/apps/clang` and `/sys/apps/rust`,
  parses the SMF executable envelopes, extracts embedded ELF stubs, and verifies
  `SIMPLEOS_X86_64_CLANG_ELF` and `SIMPLEOS_X86_64_RUST_ELF`.
- The probe reads Clang/Rust manifest and pipeline proof files from FAT32 inside
  the guest.
- The probe now calls the x86_64 filesystem-exec spawn bridge for
  `/sys/apps/clang` with `/usr/share/simpleos/toolchain/clang/hello.c` and for
  `/sys/apps/rust` with `/usr/share/simpleos/toolchain/rust/Cargo.toml`. The
  serial log shows `spawn:resolve`, `spawn:bytes`, SMF stub validation through
  `spawn:image ... stub_bytes=... argv_count=2 env_count=0`, and
  `[toolchain-vfs] ok spawn ...` for both apps. The dedicated probe requires
  distinct monotonic guest PIDs (`pid=1` for Clang and `pid=2` for Rust) rather
  than a fixed placeholder PID.
- The same probe emits
  `[toolchain-vfs] compiler-operation-deferred status=standalone-required
  reason=frontend-runtime-not-yet-ported` so this evidence is not mistaken for
  frontend/compiler execution.
- The freestanding SMF parser now uses direct byte-array indexing internally;
  this fixed a baremetal-only failure where ELF-backed SMF packages were read
  from FAT32 but the parser could not find the EOF trailer.
- `bin/simple run src/os/port/deploy_toolchains.spl -- --status` now reports
  the exact readiness of the real guest compiler payload path. Current status
  on 2026-05-05: `llvm-cross NOT BUILT`, `compiler-rt NOT BUILT`,
  `rust-examples NOT BUILT`, `clang-static-guest NOT BUILT`, `rustc-static-guest
  NOT BUILT`, and `toolchain-disk-bake DISABLED`.

## Required Fix

Add a QEMU lane that launches filesystem-backed Clang and Rust compiler
executables inside the guest, passes small source inputs from the FAT32 image,
and verifies a real compile output or a well-defined compiler diagnostic
produced by the in-guest process.

Before that lane can pass, build or provide:

- `build/os/clang_static/bin/clang_static`;
- `build/os/rust_static/bin/rustc_static`;
- `build/os/.bake_include_toolchain` so `disk_image_bake.spl` embeds those
  payloads into the FAT32 image.

`disk_image_bake.spl` now treats that marker as strict: once
`build/os/.bake_include_toolchain` exists, the bake fails if either
`build/os/clang_static/bin/clang_static` or
`build/os/rust_static/bin/rustc_static` is missing. This prevents a
toolchain-enabled image from silently omitting the real compiler payloads.

The lane should fail unless all of these are true:

- the executable bytes are loaded from the guest filesystem;
- the launched process is the compiler app, not a host-side shim;
- the compiler consumes an input source file from the guest filesystem;
- the compiler writes or returns a deterministic output proving frontend and
  driver execution;
- serial markers distinguish successful executable launch from successful
  compiler operation.

## Verification Target

Add a scenario such as `x64-toolchain-exec-probe` and include it in the SimpleOS
real-OS audit once it passes under QEMU.

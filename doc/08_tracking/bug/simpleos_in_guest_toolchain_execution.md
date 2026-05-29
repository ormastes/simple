# SimpleOS In-Guest Toolchain Execution Gap

Date: 2026-05-05
Status: Open

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

## Blocker Analysis (updated 2026-05-29)

Two independent blockers must both be resolved before any real in-guest compiler
execution is possible. Neither is addressable in pure Simple today.

### Blocker 1 — Kernel exec control transfer not wired (x86_64)

`src/os/kernel/loader/x86_64_fs_exec_spawn.spl` implements two spawn paths:

- **Static-seeded path** (`_x86_64_spawn_static_seeded`): reads a hardcoded
  stub size, prints `spawn:image` and `spawn:bytes` serial markers, bumps
  `g_x86_64_fs_exec_next_pid`, and returns the PID. No bytes are loaded from
  FAT32; no process image is built; no task is scheduled.
- **Full VFS path** (`x86_64_fs_exec_spawn_as`): reads SMF bytes from FAT32,
  validates the ELF stub via `smf_extract_executable_stub_for_arch`, prints
  `spawn:image`, and returns the PID. A task struct is never constructed;
  `build_user_process_image_unchecked` and `scheduler_create_bootstrap_user_task_pid`
  are never called from the x86_64 path.

The shared path in `src/os/kernel/loader/fs_exec_spawn.spl` does call
`build_user_process_image_unchecked` + `scheduler_create_bootstrap_user_task_pid`
and returns a `FsExecPrepareResult`, but `fs_exec_spawn_as` stops immediately
after receiving the PID — the "optional live handoff hook" described in the
file header is not wired for x86_64 or any other architecture (ARM64 confirms
this: `arm64_fs_exec_spawn` also returns `prepared.pid` with no handoff call).

Fix required: wire the x86_64 spawn path to call `fs_exec_prepare_spawn` (the
shared path) and add the arch-specific handoff that context-switches into the
newly created task. This is kernel-level work.

### Blocker 2 — No real compiler payloads (clang_static, rustc_static)

`bin/simple run src/os/port/deploy_toolchains.spl -- --status` reports:

```
llvm-cross       NOT BUILT
compiler-rt      NOT BUILT
rust-examples    NOT BUILT
clang-static-guest NOT BUILT
rustc-static-guest NOT BUILT
toolchain-disk-bake DISABLED
```

Even with Blocker 1 fixed, spawning `/sys/apps/clang` or `/sys/apps/rust`
would execute a stub ELF, not a real compiler. The real payloads require an
LLVM cross-build targeting `x86_64-unknown-simpleos` and a Rust cross-build
for the same triple. These are C++/Rust toolchain builds, not pure Simple.

`disk_image_bake.spl` enforces strictness once
`build/os/.bake_include_toolchain` is created: bake fails if either
`build/os/clang_static/bin/clang_static` or
`build/os/rust_static/bin/rustc_static` is missing.

## Required Fix

Resolve both blockers in order:

1. Wire `x86_64_fs_exec_spawn_as` to use `fs_exec_prepare_spawn` (shared path)
   and add the x86_64 arch handoff that context-switches into the bootstrapped
   task. This unblocks real in-guest ELF execution for any guest binary.

2. Build `build/os/clang_static/bin/clang_static` and
   `build/os/rust_static/bin/rustc_static` via the LLVM/Rust cross-build
   pipeline in `src/os/port/llvm/` and `src/os/port/rust/`.
   Touch `build/os/.bake_include_toolchain` and re-bake the FAT32 image.

Once both are ready:

3. Add a `x64-toolchain-exec-probe` QEMU lane (entry point analogous to
   `examples/simple_os/arch/x86_64/toolchain_vfs_probe_entry.spl`) that:
   - spawns `/sys/apps/clang` with `hello.c` as argv[0];
   - verifies a real compile output or well-defined diagnostic via serial;
   - emits `[toolchain-exec] compiler-ran app=clang status=ok` (or `fail`);
   - uses a distinct serial marker from the VFS-only probe so the two lanes
     are not confused.

The lane should fail unless all of these are true:

- the executable bytes are loaded from the guest filesystem;
- the launched process is the compiler app, not a host-side shim;
- the compiler consumes an input source file from the guest filesystem;
- the compiler writes or returns a deterministic output proving frontend and
  driver execution;
- serial markers distinguish successful executable launch from successful
  compiler operation.

## Verification Target

Add `x64-toolchain-exec-probe` and include it in the SimpleOS real-OS audit
once it passes under QEMU. Do not add the lane until Blockers 1 and 2 are
both resolved — a lane that always defers is dead code and contradicts the
audit requirement that the scenario pass.

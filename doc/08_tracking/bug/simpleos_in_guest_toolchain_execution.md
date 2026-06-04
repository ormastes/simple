# SimpleOS In-Guest Toolchain Execution Gap

Date: 2026-05-05
Status: Open — kernel task preparation evidence improved 2026-05-30 and
status gate added 2026-05-30; real compiler payloads and live
compiler-operation proof remain open.

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
  `spawn:image ... stub_bytes=... argv_count=2 env_count=0`,
  `spawn:prepared path=... pid=... entry=... segments=...`, and
  `[toolchain-vfs] ok spawn ...` for both apps. The dedicated probe requires
  distinct monotonic guest PIDs (`pid=1` for Clang and `pid=2` for Rust) and
  prepared scheduler-task markers rather than fixed placeholder PID evidence.
- The same probe emits
  `[toolchain-vfs] compiler-operation-deferred status=standalone-required
  reason=frontend-runtime-not-yet-ported` so this evidence is not mistaken for
  frontend/compiler execution.
- The freestanding SMF parser now uses direct byte-array indexing internally;
  this fixed a baremetal-only failure where ELF-backed SMF packages were read
  from FAT32 but the parser could not find the EOF trailer.
- `bin/simple run src/os/port/deploy_toolchains.spl -- --status` reports
  the exact readiness of the real guest compiler payload path. Current status
  on 2026-05-30: `llvm-cross NOT BUILT`, `compiler-rt NOT BUILT`,
  `rust-examples NOT BUILT`, `clang-static-guest NOT BUILT`, `rustc-static-guest
  NOT BUILT`, `toolchain-disk-bake DISABLED`, and
  `guest-toolchain-exec-gate BLOCKED`.

## Blocker Analysis (updated 2026-05-30)

Two independent blockers must both be resolved before any real in-guest compiler
execution is possible. Neither is addressable in pure Simple today.

### Blocker 1 — Live kernel exec control transfer proof missing (x86_64)

Historical context: earlier on 2026-05-29,
`src/os/kernel/loader/x86_64_fs_exec_spawn.spl` implemented two spawn paths:

- **Static-seeded path** (`_x86_64_spawn_static_seeded`): reads a hardcoded
  stub size, prints `spawn:image` and `spawn:bytes` serial markers, bumps
  `g_x86_64_fs_exec_next_pid`, and returns the PID. No bytes are loaded from
  FAT32; no process image is built; no task is scheduled.
- **Full VFS path** (`x86_64_fs_exec_spawn_as`): read SMF bytes from FAT32,
  validated the ELF stub via `smf_extract_executable_stub_for_arch`, printed
  `spawn:image`, and returned the PID. A task struct was never constructed;
  `build_user_process_image_unchecked` and
  `scheduler_create_bootstrap_user_task_pid` were never called from the
  x86_64 path.

The shared path in `src/os/kernel/loader/fs_exec_spawn.spl` does call
`build_user_process_image_unchecked` + `scheduler_create_bootstrap_user_task_pid`
and returns a `FsExecPrepareResult`, but `fs_exec_spawn_as` stops immediately
after receiving the PID — the "optional live handoff hook" described in the
file header is not wired for x86_64 or any other architecture (ARM64 confirms
this: `arm64_fs_exec_spawn` also returns `prepared.pid` with no handoff call).

Progress 2026-05-29: `fs_exec_prepare_spawn_from_bytes(...)` now lets
architecture-specific loaders reuse the shared process-image and scheduler-task
registration path after they have resolved executable bytes through their own
aliases/caches. The real-byte x86_64 path now calls that helper, so a VFS/FAT32
SMF hit builds a user process image and bootstrap scheduler task before
returning the PID. The synthetic seeded fallback remains only for host/unit
cases where no mounted VFS bytes are available.

Progress 2026-05-30: `fs_exec_prepare_spawn_from_bytes(...)` now emits an
explicit `[fs-exec] spawn:prepared path=... pid=... entry=... segments=...`
marker after `scheduler_create_bootstrap_user_task_pid` succeeds. The
`x64-toolchain-vfs-probe` completion contract now requires that marker for
Clang, Rust, and the Steam 2048 fixture, so the VFS probe cannot pass with only
SMF parse/image markers.

Focused evidence:

```
SIMPLE_LIB=src bin/simple check src/os/kernel/loader/fs_exec_spawn.spl src/os/kernel/loader/x86_64_fs_exec_spawn.spl src/os/toolchain_vfs_probe_contract.spl test/01_unit/os/toolchain_vfs_probe_contract_spec.spl test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/os/toolchain_vfs_probe_contract_spec.spl --mode=interpreter --clean --format json
SIMPLE_LIB=src bin/simple test test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl --mode=interpreter --clean --format json
SIMPLE_LIB=src bin/simple test test/03_system/os/port/x86_64_elf_load_spec.spl --mode=interpreter --clean --format json
SIMPLE_LIB=src bin/simple run src/os/port/deploy_toolchains.spl -- --status
```

Results: check passed; `toolchain_vfs_probe_contract_spec.spl` passed `2/2`;
`x86_64_fs_exec_spawn_spec.spl` passed `2/2`; `x86_64_elf_load_spec.spl`
passed `1/1`; toolchain status still reports missing guest compiler payloads.

Remaining kernel-side gap: the real-byte path now constructs a process image
and scheduler task, but live context transfer into a deterministic x86_64 guest
payload is still not proven. The existing VFS probe intentionally returns after
spawn markers so it can continue checking all payload fixtures; it should not
be counted as compiler-operation or post-entry handoff evidence.

### Blocker 2 — No real compiler payloads (clang_static, rustc_static)

`bin/simple run src/os/port/deploy_toolchains.spl -- --status` reports:

```
llvm-cross       NOT BUILT
compiler-rt      NOT BUILT
rust-examples    NOT BUILT
clang-static-guest NOT BUILT
rustc-static-guest NOT BUILT
toolchain-disk-bake DISABLED
guest-toolchain-exec-gate BLOCKED
```

Progress 2026-05-30: `src/os/port/deploy_toolchains.spl -- --status` now
prints `guest-toolchain-exec-gate` as one explicit gate for real in-guest
compiler execution. The gate remains `BLOCKED` until both
`build/os/clang_static/bin/clang_static` and
`build/os/rust_static/bin/rustc_static` exist and
`build/os/.bake_include_toolchain` is enabled. This prevents prepared-spawn
evidence from being mistaken for compiler-operation evidence.

Focused evidence:

```
SIMPLE_LIB=/tmp/simple-in-guest-toolchain/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple check src/os/port/guest_toolchain_execution_gate.spl src/os/port/deploy_toolchains.spl test/01_unit/os/port/deploy_toolchains_status_spec.spl
SIMPLE_LIB=/tmp/simple-in-guest-toolchain/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple test test/01_unit/os/port/deploy_toolchains_status_spec.spl --mode=interpreter --clean --fail-fast
SIMPLE_LIB=/tmp/simple-in-guest-toolchain/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple run src/os/port/deploy_toolchains.spl -- --status
```

Results: check passed; `deploy_toolchains_status_spec.spl` passed `2/2`;
status ran successfully after the runner fell back from JIT to interpreter on
an existing `process` lowering issue, and reported `guest-toolchain-exec-gate
BLOCKED` with the concrete missing payloads and disabled bake marker.

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

1. Finish live x86_64 handoff evidence for the prepared task path. The
   real-byte spawn path now constructs the process image and task; the missing
   proof is a QEMU lane that transfers into the task and observes deterministic
   guest behavior without confusing that with VFS-only spawn markers.

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

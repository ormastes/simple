# Local research: SimpleOS filesystem toolchain and servers

Date: 2026-07-11

## Findings

- The RV64 HTTP wrapper sends real forwarded TCP requests, but no current
  `build/os/simpleos_riscv64.elf` exists. The retained June transcript is stale,
  and a fresh build currently stops because the selected compiler lacks LLVM.
- No SimpleOS database server exists. The DB checker only greps marker files;
  the historical `examples/11_advanced/simple_db` submodule is an explicitly
  unfinished skeleton with `pass_todo`.
- A 124,602,568-byte static SimpleOS Clang ELF exists at
  `build/os/clang_static/bin/clang_static`. It is not staged, the old bake is
  fixed at 32 MiB, and mounted executable reads cap at 4 MiB.
- Historical ring-3 success proves a small Clang-built output ELF. The SSH demo
  uses a boot preload and does not prove `/usr/bin/clang` ran from mounted FS.
- All canonical Simple role paths are already centralized in
  `initramfs_pack.spl`, `image_builder.spl`, and `disk_image_bake.spl`; reuse one
  target-native payload rather than adding compiler/loader variants.
- No target-native Simple payload currently exists. Existing image/spec evidence
  accepts marker ELFs or a 23-byte `SMF_FAKE_TARGET_SIMPLE`, and live self-host
  scenarios skip.
- Hosted launch metadata selects `filesystem`; only explicit
  `simpleos-baremetal` selects `baremetal_got`. The x86 filesystem bridge still
  has an unkeyed preload shortcut that can substitute `/FSEXEC.ELF` bytes.

## Historical anchors

- `894360a6198`: small on-disk ELF reaches ring 3.
- `d2d67b5960b`: SSH Clang-hello demo, but via boot preload.
- `8117e9bca20`: image role paths for the Simple compiler.
- `doc/08_tracking/bug/simpleos_in_guest_toolchain_execution.md`: real compiler
  execution remains open despite older closed state files.

## Current blockers

1. Pure-Simple deployed compiler is currently replaced by the Rust seed, and
   the fresh RV64 build reports LLVM unavailable.
2. Mounted executable range reads and per-`PT_LOAD` streaming are missing.
3. Real Clang/Simple payloads are not in a sufficiently large install image.
4. No guest DB service handles a real create/write/read request.


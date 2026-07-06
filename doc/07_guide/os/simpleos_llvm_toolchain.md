# SimpleOS LLVM/Clang Toolchain — Where It Lives & How To Build Hello World

Quick-find guide for the LLVM→SimpleOS port. If you are asked to "build hello
world with clang for SimpleOS", start here — the toolchain is **already built**,
just not on the `PATH` and not under the name the disk-bake gate expects.

## Locations (the hard-to-find part)

| What | Path | Notes |
|------|------|-------|
| LLVM/Clang **source** | `/home/ormastes/llvm-project` | Host home dir, **outside the repo**. Clang 20. Used as `LLVM_EXTERNAL_CLANG_SOURCE_DIR`. |
| **Cross clang/lld** (host-run, targets SimpleOS) | `build/os/llvm/cross-x86_64-unknown-simpleos/bin/` | `clang-20` (131 MB), `ld.lld`, `lld`, `llvm-nm`. ~954 MB. This is the compiler you use. |
| aarch64 cross variant | `build/os/llvm/cross-aarch64-unknown-simpleos/` | Same layout for arm64. |
| Host LLVM tblgen tools | `build/os/llvm/host-tools/bin/` | Bootstrap only (tblgen etc.), not clang. |
| **Sysroot** | `build/os/sysroot/` | `lib/crt0.o`, `lib/libsimpleos_c.a`, `share/simpleos/simpleos.ld`. |
| Build driver (Simple) | `src/os/port/llvm/build.spl` | Clones/builds LLVM; `--target x86_64-unknown-simpleos`. |
| Deploy + status | `src/os/port/deploy_toolchains.spl` | `bin/simple run … -- --status` prints the gate report. |

The cross `clang-20` is a **host executable** (Linux ELF) that emits
`x86_64-unknown-simpleos` code — a cross-compiler, not a guest-native binary.

## Build + link hello world (verified)

```sh
BIN=build/os/llvm/cross-x86_64-unknown-simpleos/bin
SR=build/os/sysroot
printf 'int main(void){return 42;}\n' > /tmp/hello.c

$BIN/clang-20 --target=x86_64-unknown-simpleos --sysroot=$SR -c /tmp/hello.c -o /tmp/hello.o
$BIN/ld.lld -T $SR/share/simpleos/simpleos.ld $SR/lib/crt0.o /tmp/hello.o \
    -L $SR/lib -lsimpleos_c -o /tmp/hello.elf

file /tmp/hello.elf      # ELF 64-bit LSB executable, x86-64, statically linked
$BIN/llvm-nm /tmp/hello.elf | grep -E ' _start| main'
#   0000000010000000 T _start
#   0000000010000080 T main
```

Result: a valid, statically-linked `x86_64-unknown-simpleos` ELF. **Compile and
link work today.**

## Running it in-guest — blocked

Actually *executing* the ELF inside SimpleOS under QEMU (SSH in → run) is **not
yet provable**. Two tracked blockers:

1. **Kernel exec handoff** — `test/03_system/os/port/x86_64_elf_load_spec.spl`
   skips the behavioural run: *"blocked on P0-C QEMU smoke (disk image + VFS
   mount)"*. Live context transfer into a spawned guest task is unproven.
2. **Guest-native `clang_static`** — the disk bake / SSH live lane want
   `build/os/clang_static/bin/clang_static` (a static clang that runs **on**
   SimpleOS, not the host cross-compiler above) plus
   `build/os/.bake_include_toolchain`. `--status` gate =
   `guest-toolchain-exec-gate BLOCKED`.

Full detail & remaining steps: `doc/08_tracking/bug/simpleos_in_guest_toolchain_execution.md`.
SSH live-guest harness (gated): `test/03_system/os/simpleos_guest_toolchain_live_spec.spl`
(needs `SIMPLEOS_QEMU_SSH_TOOLCHAIN_LIVE=1`, `sshpass`, and a baked
`build/os/simpleos_disk.img`).

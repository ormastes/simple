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

## Current filesystem-exec status (2026-07-11)

The guest candidate now exists at
`build/os/clang_static/bin/clang_static` (122,233,168-byte static ELF), but it
has **not** passed mounted-filesystem execution. The production x86_64 loader
now opens the exact requested FAT32 path, retains only a bounded ELF header and
program-header prefix, and streams every PT_LOAD directly into its mapped user
frames. It rejects short reads and no longer consults the unkeyed boot preload.
The loader also builds bounded SysV argv/envp/auxv state. This is source-ready,
not QEMU proof: the latest retained production log still predates the fix and
ends `TEST FAILED`. Historical SSH preload success remains invalid evidence.

Completion requires one fail-closed transcript that opens `/usr/bin/clang` from
the mounted image, runs `--version`, compiles a guest `hello.c`, and launches the
resulting mounted ELF. Reject any run containing `spawn:preloaded` as hosted
filesystem proof. The active design and test plan are
`doc/04_architecture/simpleos_filesystem_toolchain_servers.md` and
`doc/03_plan/sys_test/simpleos_filesystem_toolchain_servers.md`.

The companion target-Simple builder is
`sh scripts/os/simpleos-native-build.shs`. It defaults to
`x86_64-unknown-simpleos`, refuses the Rust bootstrap seed, compiles the full
`src/app/cli/main.spl` entry closure with stub fallback disabled, and writes a
target build stamp. Canonical target lowering now keeps the SimpleOS triple and
links user programs against the SimpleOS sysroot; the current deployed
self-hosted runner still times out before focused specs execute. Do not fall
back to the seed.

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

## Running it in-guest — source path implemented, live proof blocked

Actually *executing* the ELF inside SimpleOS under QEMU (SSH in → run) is **not
yet provable**. Two tracked blockers:

1. **Kernel exec handoff** — exact-path streaming and SysV argv/envp population
   are implemented in `x86_64_fs_exec_spawn.spl` and
   `x86_64_fs_exec_ring3.spl`, but a fresh QEMU run has not passed yet.
2. **Guest-native `clang_static`** — the disk bake / SSH live lane want
   `build/os/clang_static/bin/clang_static` (a static clang that runs **on**
   SimpleOS, not the host cross-compiler above) plus
   `build/os/.bake_include_toolchain`. `--status` gate =
   `guest-toolchain-exec-gate BLOCKED`. Historical `build_clang_disk.shs`
   evidence proves LLVM bitcode only. The current lane requests
   `-emit-obj /hello.o` and fails unless the guest dump is x86-64 ELF REL with
   `main` and exit status 0. Embedded LLD now builds into the guest binary, the
   static relink has zero undefined symbols, and the wrapper has fail-closed
   guest object/link/execute phases. It has not produced live proof because the
   available pure-Simple CLIs fail while native-building the QEMU kernel before
   guest boot; see
   `doc/08_tracking/bug/simpleos_clang_fs_pure_compiler_native_build_2026-07-11.md`.
   Run it with a proven self-hosted compiler, for example:
   `SIMPLE_BUILD_COMPILER=build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple sh scripts/os/build_clang_disk.shs`.
   The wrapper rejects Rust-seed provenance and requires exact `-c` output `2`
   before starting the kernel build.
   **On desktop SimpleOS this static path
   is DEPRECATED — see the launch-policy section below.**

Full detail & remaining steps: `doc/08_tracking/bug/simpleos_in_guest_toolchain_execution.md`.
SSH live-guest harness (gated): `test/03_system/os/simpleos_guest_toolchain_live_spec.spl`
(needs `SIMPLEOS_QEMU_SSH_TOOLCHAIN_LIVE=1`, `sshpass`, and a baked
`build/os/simpleos_disk.img`).

## Desktop SimpleOS launch policy — static `clang_static` is DEPRECATED

On **desktop SimpleOS**, the guest-native `clang_static` workaround
(`src/os/port/llvm/clang_static.shs` re-linking the cross objects into one
self-contained static ELF, gated by `guest_toolchain_execution_gate_detail` on
`build/os/clang_static/bin/clang_static` + `build/os/.bake_include_toolchain`)
is **deprecated**. It stands in for a real loader — bake one special binary
instead of launching an ordinary ELF **from the filesystem**. That is not how a
general OS runs programs.

**Proper model (general OS filesystem launch).** The toolchain is an ordinary
statically-linked `x86_64-unknown-simpleos` ELF — exactly what the cross
compiler already produces (see *Build + link hello world* above). It is:

- **Placed at a proper filesystem location** — canonical `/usr/bin/clang`,
  resolved by the guest shell `PATH` (`/usr/bin:/sys/apps`, see
  `src/os/apps/shell/path_search.spl`) — **not** a `*.SMF` alias baked into the
  app-registry allowlist; **or**
- **Pointed to by an env path** — host-side `SIMPLEOS_TOOLCHAIN_DIR` tells the
  disk bake where to stage the toolchain tree, so the on-disk location is not
  hardcoded.

…and **launched via the general filesystem-exec loader** (the ring-3 FS-exec
track, `FR-SOS-020+` in
`doc/02_requirements/os/simpleos/simpleos_os_subsystem_feature_requests.md`):
shell resolves the path → reads the on-disk ELF → maps PT_LOAD segments → enters
ring-3. No static-relink step, no registry allowlist, no GOT special-casing.

The `.got`/`.got.plt` placement in `share/simpleos/simpleos.ld` **stays** — that
is correct static-ELF linking, orthogonal to this deprecation.

**Migration.** New work targets the FS-exec loader + `/usr/bin/clang` location.
`clang_static.shs` and the static `guest_toolchain_execution_gate` requirement
remain only as a legacy fallback until the FS-exec lane proves an ordinary
on-disk toolchain ELF runs in ring-3, then are removed from the desktop lane.

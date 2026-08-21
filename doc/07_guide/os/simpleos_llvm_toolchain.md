# SimpleOS LLVM/Clang Toolchain — Where It Lives & How To Build Hello World

> **Restart12 status (2026-08-14):** any 2026-08-06 paths or boot proofs below
> are historical and do not establish current deployment acceptance. This
> worktree has no current `build/os/clang_static/bin/lld_static` or cross-tree
> `bin/ld.lld`. A host cross linker is not the required guest tool:
> B-GUEST-LLD closes only on a validated static x86_64 SimpleOS ELF with
> hash/dependency receipts. Current authority:
> `doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.

For the related pure-Simple POSIX, startup argv, host mmap, and SimpleOS VFS
provider map, see
[`simpleos_posix_host_interface_index.md`](../app/llm/simpleos_posix_host_interface_index.md).
That index is a discovery aid, not additional LLVM/Clang live evidence.

Quick-find guide for the LLVM→SimpleOS port. If you are asked to "build hello
world with clang for SimpleOS", start here.

> **Build status (verified on-disk 2026-08-06): the cross toolchain is NOT
> prebuilt. You must build it before any `clang`/`ld.lld` command in this guide
> will run.** Three-stage status as measured:
>
> | Stage | Output | State today |
> |---|---|---|
> | 1 `host-tools` | `build/os/llvm/host-tools/` | **PRESENT** — `bin/` has `llvm-tblgen`, `clang-tblgen`, `llvm-min-tblgen`, `llvm-lit`; `build.ninja` present |
> | 2 `cross` | `build/os/llvm/cross-<triple>/` | **NOT BUILT** — x86_64 dir holds only `CMakeCache.txt`/`CMakeFiles`/`CPack*.cmake`: no `bin/`, no `build.ninja`. aarch64 dir does not exist at all |
> | 3 `compiler-rt` | `build/os/sysroot/lib/clang/<ver>/lib/<triple>/*.a` | not staged |
>
> Current 2026-08-20 worktree inspection: no cross-tree or populated sysroot is
> present. `build/os/clang_static/bin/clang_static` exists only as a 16 KiB
> all-zero data placeholder and is not executable evidence. Do not reuse older
> size/path claims below as current admission.
>
> Build it with:
>
> ```sh
> LLVM_SRC=/home/ormastes/llvm-project sh src/os/port/llvm/build.shs
> # or a single stage: … build.shs host-tools | cross | compiler-rt
> # per-target:        SIMPLE_TARGET=aarch64-unknown-simpleos … build.shs
> ```
>
> Rebuilding the cross stage is Lane C1 of
> `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`.

## LLVM source fork

The port builds from a **fork**, not upstream LLVM:

- Repo: `https://github.com/ormastes/llvm-project.git`, branch **`simpleos`** (Clang 20).
- Local checkout: `/home/ormastes/llvm-project` (branch `simpleos`, HEAD
  `59612206386553df81efc06ec0421acf646d49ef` = `596122063`).
- `src/os/port/llvm/build.spl:71` pins `LLVM_REVISION` to that **same sha**, so the
  pin and the fork tip agree as of 2026-08-06. (`build.spl:70` holds `LLVM_REPO`.)
  `build.shs` instead uses whatever `$LLVM_SRC` (default `~/llvm-project`) points
  at — it does not itself checkout the pin, so verify the checkout's HEAD when
  using the shell driver.

## Locations (the hard-to-find part)

| What | Path | Notes |
|------|------|-------|
| LLVM/Clang **source** | `/home/ormastes/llvm-project` | **PRESENT.** Host home dir, **outside the repo**. `ormastes/llvm-project` branch `simpleos`, Clang 20. Used as `LLVM_EXTERNAL_CLANG_SOURCE_DIR`. |
| **Cross clang/lld** (host-run, targets SimpleOS) | `build/os/llvm/cross-x86_64-unknown-simpleos/bin/` | **NOT BUILT — directory holds only CMakeCache/CMakeFiles.** Once stage `cross` runs it holds `clang-20`, `ld.lld`, `lld`, `llvm-nm` (expect ~131 MB clang, ~954 MB tree). This is the compiler the rest of this guide assumes. |
| aarch64 cross variant | `build/os/llvm/cross-aarch64-unknown-simpleos/` | **ABSENT** (not even configured). Same layout as x86_64 once built via `SIMPLE_TARGET=aarch64-unknown-simpleos`. |
| Host LLVM tblgen tools | `build/os/llvm/host-tools/bin/` | **PRESENT** (`llvm-tblgen`, `clang-tblgen`, `llvm-min-tblgen`, `llvm-lit`). Bootstrap only — not clang. |
| **Sysroot** | `build/os/sysroot/` | **NOT PRESENT in the current worktree.** Rebuild and bind the exact target contents before use. |
| Guest-native static clang | `build/os/clang_static/` | **INVALID PLACEHOLDER.** The current 16 KiB all-zero `bin/clang_static` is not an ELF/SMF executable. Deprecated for desktop SimpleOS — see launch-policy section. |
| Disk-bake toolchain marker | `build/os/.bake_include_toolchain` | **ABSENT.** |
| Build driver (shell, stages) | `src/os/port/llvm/build.shs` | `LLVM_SRC=/home/ormastes/llvm-project sh src/os/port/llvm/build.shs` → stages `host-tools`, `cross`, `compiler-rt`. |
| Build driver (Simple) | `src/os/port/llvm/build.spl` | Clones/builds LLVM; `--target x86_64-unknown-simpleos`. |
| Deploy + status | `src/os/port/deploy_toolchains.spl` | `bin/simple run … -- --status` prints the gate report. |

When built, the cross `clang-20` is a **host executable** (Linux ELF) that emits
`x86_64-unknown-simpleos` code — a cross-compiler, not a guest-native binary.

## Simple-native toolchain (distinct from clang)

This guide covers the **clang/LLVM** cross-toolchain. There is a separate
**Simple-native** toolchain: the Simple compiler itself cross-built *for*
SimpleOS. `TargetOS::SimpleOS = 5` is a first-class target OS beside
`Linux/Windows/MacOS`, with triples `x86_64-`, `aarch64-`, `riscv64-unknown-simpleos`.

| What | Path | Notes |
|------|------|-------|
| Per-arch Simple compiler for SimpleOS | `bin/release/<arch>-unknown-simpleos/simple` | **ABSENT today** — `x86_64-` and `riscv64-unknown-simpleos/` dirs exist but are **EMPTY**, and there is no `aarch64-` dir (verified 2026-08-06). Rebuild with `bin/simple build simpleos`. When built: ~4 MB static EXEC per arch; boot-proven 2026-07-14 (historical) |
| Builder (opt-in subcommand) | `bin/simple build simpleos [arch...]` → `scripts/ci/build-simpleos-toolchain.shs` → `src/app/ci/build_simpleos_toolchain.spl` | per-arch native-build → fail-closed `readelf` gate → stamp → install |

`bin/simple build simpleos` builds all three SimpleOS arches (optionally filter
by passing arch names); it is **opt-in** so a plain `bin/simple build` stays
host-only and fast (that default produces only
`bin/release/x86_64-unknown-linux-gnu/simple`). The subcommand and the CI script
run the same builder. Boot/FS-exec staging is proven on all three arches (x86_64
OVMF, riscv64 OpenSBI, aarch64 EL1). In-guest *run* of the Simple **interpreter**
is PROVEN on x86_64 under real OVMF (2026-07-14, `fe9fbd8c2285`):
`ssh root@guest /usr/bin/simple /hello.spl` prints "hello from simple on
simpleos" (gate `scripts/os/ssh_simple_hello_uefi.shs`, rung L4b PASS). The last
blocker was the guest lexer's `src[start:pos].join("")` (a native value-type
array-slice + join) returning `""`, so every identifier token came out empty and
nothing resolved — fixed with a char-index loop. **Lesson: native array `[s:e]`
slice + `.join()` is unreliable in guest-run code; use index loops.** The deployed
*full CLI* still has separate blockers (`env_set` ABI, #99 redeploy); the
interpreter goal was reached via the focused `simpleos_tool` payload. Full 3-arch
status:
`doc/03_plan/os/in_guest_clang_selfhost_board_plan.md` (§ Simple compiler/loader
on SimpleOS).

## HISTORICAL, COMMIT-PINNED (2026-07-13): clang object emission proven under OVMF

**Evidence class: commit-pinned historical proof at `7cf0b6aec3a`. The artifacts
it produced are NOT on disk today** (the cross clang/lld it used are unbuilt, see
build status above), so this is not a claim about the current tree. Re-proving it
against a fresh build is Lane C3 of the toolchain self-host bootstrap plan.

As proven at commit `7cf0b6aec3a`, the full ladder ran under **OVMF pflash (real
UEFI firmware, no QEMU `-kernel`)**: GRUB-EFI → multiboot → ring-3 sshd →
in-guest `clang -cc1 -emit-obj /hello.c → /hello.o` on the FAT32 volume →
`getfile` retrieves a byte-exact ET_REL/EM_X86_64 object → host link → exit 7.
Reproduce (requires the cross toolchain to be built first):

```sh
SKIP_STAGE=0 SKIP_KERNEL=0 sh scripts/os/scp_retrieve_over_ssh_uefi.shs
```

This proves filesystem-resident Clang `cc1` object emission and byte-exact
retrieval. It does not prove in-guest linking followed by ring-3 execution of
the linked program; that remains open in
`.spipe/simpleos_filesystem_toolchain_servers/state.md`.

Layout facts you must know before touching the link bases (2f fix):
- Ring-3 payloads (`simpleos.ld` in the sysroot, generated by
  `src/os/port/llvm/sysroot.shs`) link at **`0x40000000` (1 GiB)** — moved from
  `0x10000000`, which sat inside the OVMF kernel's `.bss` band.
- Guest mmap base is **`0x50000000`** (`src/os/kernel/ipc/syscall.spl`).
- The OVMF/GRUB-EFI kernel links at **128 MB** via
  `examples/09_embedded/simple_os/arch/x86_64/linker_128mb.ld`; its ~211 MB
  NOBITS `.bss` spans `[0x08000000, ~0x16400000)` — nothing user-side may link
  or mmap there. QEMU `-kernel` lanes still use `linker_low1mb.ld` (1 MB base).

Remaining: in-guest link/execute proof and physical mini-PC bring-up — see
`doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md`
(HIGH gap: no physical NIC driver; only virtio-net exists).

## Previous filesystem-exec status (2026-07-11, superseded)

A guest candidate was once produced at
`build/os/clang_static/bin/clang_static` (122,233,168-byte static ELF). **That
file is absent today** — `build/os/clang_static/` does not exist (verified
2026-08-06) — and it never passed mounted-filesystem execution. The production x86_64 loader
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

## Build + link hello world — NOT currently reproducible (toolchain unbuilt)

These are the correct invocations, and they are kept verbatim, but **`$BIN` below
does not exist until the `cross` stage is built** (see build status at the top).
Run `LLVM_SRC=/home/ormastes/llvm-project sh src/os/port/llvm/build.shs` first.

There is no commit-pinned evidence attached to this particular block: the
`7cf0b6aec3a` proof covers the in-guest `-cc1` ladder above, **not** this
host-side compile+link sequence. Treat the sample `llvm-nm` output below as
illustrative of the expected shape, not as a recorded run.

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

Expected result once built: a valid, statically-linked
`x86_64-unknown-simpleos` ELF. Note the `_start`/`main` addresses shown above are
from an older `0x10000000` link base; the current `simpleos.ld` links ring-3
payloads at `0x40000000` (see the layout facts above), so re-verify the numbers
rather than copying them.

## Running it in-guest — source path implemented, live proof blocked

Actually *executing* the ELF inside SimpleOS under QEMU (SSH in → run) is **not
yet provable**. Two tracked blockers:

1. **Kernel exec handoff** — exact-path streaming and SysV argv/envp population
   are implemented in `x86_64_fs_exec_spawn.spl` and
   `x86_64_fs_exec_ring3.spl`, but a fresh QEMU run has not passed yet.
2. **Guest-native `clang_static`** — the disk bake / SSH live lane want
   `build/os/clang_static/bin/clang_static` (a static clang that runs **on**
   SimpleOS, not the host cross-compiler above) plus
   `build/os/.bake_include_toolchain` — **both absent on disk today (verified
   2026-08-06)**. `--status` gate =
   `guest-toolchain-exec-gate BLOCKED`. Historical `build_clang_disk.shs`
   evidence proves LLVM bitcode only. The current lane requests
   `-emit-obj /hello.o` and fails unless the guest dump is x86-64 ELF REL with
   `main` and exit status 0. As of the last recorded build (not reproducible
   today — `build/os/clang_static/` is gone), embedded LLD built into the guest
   binary and the static relink had zero undefined symbols; the wrapper has
   fail-closed
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
Canonical deployment/desktop harness:
`test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl`. It has
no opt-in success path: unavailable production wrapper, admitted image, or live
receipt evidence fails with `blocked:`.

### Reading the supporting SSpec results

The canonical supporting specs are intentionally narrower than the live
deployment harness. `os_compiler_bootstrap_spec.spl` is now explicitly a
source-contract inventory and does not check the Rust seed or `bin/simple`.
`simpleos_guest_toolchain_wrapper_spec.spl` runs the real
guest-wrapper dispatcher against controlled host fixtures; it proves routing,
target reporting, and rejection of unsupported host fallback, but not guest
execution. `simpleos_deploy_image_simple_toolchain_spec.spl` calls the real
image builder and proves marker/provenance rejection; it does not prove that an
image booted. Only `simpleos_toolchain_deployment_desktop_boot_spec.spl`, its
production wrapper, and same-run receipts may establish live desktop/toolchain
acceptance. File-existence inventories and Rust-seed artifacts are not release
evidence. Executable specs live once under `test/03_system/os/`; manuals mirror
them under `doc/06_spec/03_system/os/`.

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

## Artifact build admission (v1)

Path existence, a non-empty directory, `.bake_include_toolchain`, and a
structurally parseable ELF/SMF are not build provenance. They remain `PARTIAL`
or `BLOCKED` in `deploy_toolchains.spl`.

Every target artifact must first pass
`GuestToolchainArtifactBuildReceiptV1` in
`src/os/port/guest_toolchain_artifact_build_receipt.spl`. The receipt freezes:

- the exact x86_64, AArch64, or RV64GC SimpleOS target triple and tool role;
- an explicit builder path (never host `PATH` or the Rust bootstrap seed), the
  builder bytes hash, builder-source hash, provenance hash, full source
  revision, dependency manifest, and build-environment digest;
- exact argv with separate target and target-isolated output-path bindings;
- first-build and independent-rebuild sizes and SHA-256 digests; and
- canonical target-matched executable structure: complete ELF, or a canonical
  executable SMF whose embedded ELF also passes the target loader.

The admission function re-hashes every supplied builder, builder source,
provenance, bounded source-revision bundle, dependency manifest,
build-environment manifest, and output byte array. Outputs live under
`build/os/toolchain-artifacts/<target>/`; legacy
`build/os/clang_static/bin/clang_static` cannot be admitted by path alone.
Byte-identical build admission is still not guest execution or ledger PASS:
signature/trust, freshness, image continuity, filesystem launch, and live
compile/link/run receipts remain required.

`used_path_lookup` and `used_host_fallback` are candidate declarations, not
proof of their own absence. They fail structural admission when asserted, but
only a signed execution receipt binding the actual launch can authorize the
corresponding negative claim.

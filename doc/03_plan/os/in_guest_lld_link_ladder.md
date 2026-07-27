# In-guest ld.lld link ladder (rungs 3-6)

Lane: P6 (toolchain), SimpleOS production harden parallel plan
(`doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md`). Source of
the ladder numbering: master plan §13,
`doc/01_research/domain/simpleos_production_host_master_plan.md`:

> Strictly sequential gate ladder: (1) clang --version via PATH/FS-exec, (2)
> cc1 emits object, (3) ld.lld starts via FS-exec, (4) LLD links guest
> object, (5) resulting ELF starts from FS, (6) expected status+output, (7)
> full clang driver, ...

Rungs 1-2 are **proven** (`scripts/os/scp_retrieve_over_ssh_uefi.shs`, OVMF
board proxy, clang `-cc1 -emit-obj` writes a byte-exact `.o` to NVMe). This
doc and the sibling gate script (`scripts/os/ssh_lld_link_uefi.shs`) cover
rungs 3-6. Status as of 2026-07-27: **authored, not yet executed**
(PREPARED-POSTPONED — see `.spipe/simpleos_harden_p6_toolchain/state.md`).

## The 4 rungs

| Rung | Requirement | Gate script step | Serial/SSH evidence |
|---|---|---|---|
| 3 | `/usr/bin/ld.lld` starts via ordinary FS-exec and prints its version | step 7, "rung3" | `LLD <version>` in serial log after `ssh ... /usr/bin/ld.lld --version` |
| 4 | ld.lld links the guest-generated object into an ELF | step 7, "rung4" | `persist /hello.elf -> OK` in serial log after `ssh ... /usr/bin/ld.lld -T /simpleos.ld -o /hello.elf /crt0.o /hello.o` |
| 5 | The resulting ELF starts from the filesystem | step 7, "rung5" | `ring3 deferred` dispatch line in serial log after `ssh ... /hello.elf` |
| 6 | It returns an expected status and output | step 7, "rung6" | `returned rc=0` (or the chosen expected code) in serial log + matching SSH channel output |

Rung 3 deliberately reuses the **no-fork direct FS-exec dispatch idiom**
already proven for `clang -cc1` and `/usr/bin/simple` (absolute path bypasses
the sshd canned-fixture branch — see `ssh_simple_hello_uefi.shs` header note
3). This sidesteps the fork constraint recorded in
`doc/03_plan/os/in_guest_clang_selfhost_board_plan.md`: *"No in-guest linking
in Phase 1. `ld`/lld needs fork too."* — that constraint is about the clang
**driver** forking a `cc1` child process; invoking `ld.lld` as the top-level
SSH-dispatched program needs no fork at all, exactly like `clang -cc1` itself
does not.

## Prerequisites

### 1. `lld_static` guest-native binary — NOT YET BUILT

`src/os/port/llvm/clang_static.shs` already supports relinking the
cross-built LLD into a static SimpleOS-native ELF, the same mechanism the
proven cc1 gate uses for `clang_static`:

```sh
SIMPLEOS_LLVM_TOOL=lld sh src/os/port/llvm/clang_static.shs
# -> build/os/clang_static/bin/lld_static
```

Verified statically (2026-07-27) that this has never been run on this host:
- `build/os/clang_static/` does not exist at all (neither `clang_static` nor
  `lld_static` has ever been produced here).
- `build/os/llvm/cross-x86_64-unknown-simpleos/build.ninja` does not exist —
  the upstream LLVM cross build tree is incomplete/cleaned on this host, so
  even `bin/lld` (the object `clang_static.shs` relinks from) has not been
  cross-compiled. Producing it requires `sh src/os/port/llvm/build.shs cross`
  first, a multi-hour LLVM build — out of scope for a bounded static-first
  task.
- `build/os/sysroot/` (crt0.o, libc++, `simpleos.ld`) DOES already exist —
  the Phase-3 sysroot stage is not a blocker.

### 2. Multi-file guest image stager — NOT YET AUTHORED

`scripts/os/fsexec_mkimg_big.spl` (used for `clang_static`) and
`scripts/os/fsexec_mkimg_simple.spl` (used for `/usr/bin/simple`) each stage
exactly **one** big ELF payload plus **one** small companion file. The link
ladder needs `lld_static` PLUS at least: a guest object (`/hello.o`), a crt
object (`/crt0.o`), and a linker script (`/simpleos.ld`) staged
simultaneously. No such stager exists in this repo today. A new one (working
name `scripts/os/fsexec_mkimg_lld.spl`) is required; it is **out of lane
P6's exclusive-path scope** for this increment (exclusive paths are limited
to `scripts/os/ssh_lld_link_uefi.shs`, this doc, and the lane state file) and
is therefore the primary blocker recorded below.

The general desktop disk image builder (`scripts/os/make_os_disk.c` /
`.shs`) was also checked: it stages LLVM/clang/rust only as
`status=standalone-required` placeholder manifests
(`/usr/share/simpleos/toolchain/{llvm,clang,rust}/...`), not as staged
executables — confirming no existing image build path stages a working
`ld.lld` binary anywhere in the tree today.

### 3. A guest-target object to link

Any `x86_64-unknown-simpleos` `.o` file — the byte-exact object retrieved by
`scripts/os/scp_retrieve_over_ssh_uefi.shs`'s getfile step is a natural
candidate (already proven byte-valid ET_REL/EM_X86_64), or a fresh
host-cross-compiled object via the toolchain from `src/os/port/llvm/build.shs`.

### 4. Host tooling — already present on this host

Verified present (2026-07-27, via the script's own prerequisite gate):
`grub-mkstandalone`, `qemu-system-x86_64`, `sshpass`, `OVMF_CODE_4M.fd`,
`OVMF_VARS_4M.fd`. Not a blocker.

## Exact resume command

```sh
sh scripts/os/ssh_lld_link_uefi.shs
```

Env overrides available: `SEED`, `LLD_BIN`, `GUEST_OBJ`, `CRT0_OBJ`,
`LINKER_SCRIPT`, `SKIP_STAGE`, `SKIP_KERNEL`, `QEMU_MEM`, `BOOT_WAIT`,
`SSH_PORT`. The script's step-0 prerequisite gate fails closed (exit 1,
prints every missing artifact with a build hint) and does not launch QEMU
until every prerequisite above is satisfied.

## Expected evidence artifacts (once run)

- `build/os/ssh_lld_link_uefi.serial.log` — full serial transcript, gated on
  by the script itself (rungs 3-6 + the existing L1-L3 UEFI boot ladder).
- `build/os/elfexec_lld/fat32-lld.img` — staged guest image (lld_static +
  crt0.o + guest object + linker script).
- `build/os/simpleos_ssh_ring3_uefi128_lld.elf` — the 128 MiB-base kernel
  used to boot this gate (same base/layout as the proven clang/simple OVMF
  gates, for the same `.bss`-band-clearance reason documented in
  `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md` "2f RESOLVED").

## Current blockers (summary)

1. `lld_static` not built — needs `sh src/os/port/llvm/build.shs cross`
   (multi-hour) then `SIMPLEOS_LLVM_TOOL=lld sh src/os/port/llvm/clang_static.shs`.
2. `scripts/os/fsexec_mkimg_lld.spl` multi-payload stager not authored —
   out of this lane's exclusive-path scope; needs its own task/lane.
3. No guest `.o` staged for the link input yet (unblocked once a prior
   cc1-gate run's retrieved object, or a fresh cross-compiled one, is placed
   at `build/os/elfexec_lld/hello.o`).
4. Dedicated QEMU run slot — parallel lanes are running QEMU concurrently;
   this increment intentionally does not launch QEMU (STATIC-FIRST, bounded).

See `.spipe/simpleos_harden_p6_toolchain/state.md` for the lane-tracking form
of this same blocker list.

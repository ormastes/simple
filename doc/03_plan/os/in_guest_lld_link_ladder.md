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
| 3 | `/LLD.ELF` starts via ordinary FS-exec and prints its version | step 7, "rung3" | `LLD <version>` in serial log after `ssh ... /LLD.ELF -flavor gnu --version` |
| 4 | lld links the guest-generated object into an ELF | step 7, "rung4" | `[oo-nvme] persist ...HELLO.ELF -> OK` in serial log after `ssh ... /LLD.ELF -flavor gnu -T /SIMPLEOS.LD -o /HELLO.ELF /CRT0.O /HELLO.O /LIBC.A` |
| 5 | The resulting ELF starts from the filesystem | step 7, "rung5" | `[fs-exec] heap:stream-open-ok path=/HELLO.ELF` in serial log after `ssh ... /HELLO.ELF` |
| 6 | It returns an expected status and output | step 7, "rung6" | `returned rc=0` (or the chosen expected code) in serial log + matching SSH channel output |

### Two guest-side constraints the rung commands encode (verified 2026-08-06)

**Root-only 8.3 names.** SimpleOS FAT32 *reads* traverse subdirectories
(`baremetal_stubs.c` `_fat32_find_path` splits on `/` and descends, and
`_fat32_make_8_3_name` uppercases the query, so lowercase and `/usr/bin/...`
would resolve). *Writes* do not: `fat32_write_file` goes through
`_fat32_find_root_dir_slot`, which never leaves the root cluster, and there is
no mkdir and no LFN create. The rung-4 output must therefore be a root 8.3
name, and lane C4 (plan line 152) requires the same of every staged input. All
rung commands use uppercase root 8.3 paths so what is typed is byte-identical
to what is on disk. Note `libc++.a` cannot keep its name — `+` is not a legal
8.3 character — so it is staged as `/LIBCXX.A`.

**`-flavor gnu` is mandatory.** `clang_static.shs` relinks the ninja target
`bin/lld` — the *generic multiplexer*, not `bin/ld.lld` — into
`build/os/clang_static/bin/lld_static`. The ring-3 loader passes the resolved
path as `argv[0]` (`x86_64_fs_exec_ring3.spl` `_build_sysv_stack_frame`:
`binary_path` is `argv[0]`, `argc = argv.len() + 1`), so lld sees
`argv[0] = "/LLD.ELF"`, which its argv[0]-based flavor detection cannot map to
the ELF driver; without an explicit flavor it aborts with *"lld is a generic
driver"*. `src/os/port/llvm/test_smoke.spl:78` already passes `-flavor gnu`
for the same reason. Argv budget is not a concern: sshd tokenizes on spaces
only and the ring-3 startup frame allows 64 argv items within one 4 KiB page.
Because `/LLD.ELF` is not `/FSEXEC.ELF`, sshd takes the heap-stream branch,
which *preserves* argv (the `/FSEXEC.ELF` branch discards it).

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

### 2. Multi-file guest image stager — AUTHORED 2026-08-06 (no longer a blocker)

`scripts/os/fsexec_mkimg_big.spl` (used for `clang_static`) and
`scripts/os/fsexec_mkimg_simple.spl` (used for `/usr/bin/simple`) each stage
exactly **one** big ELF payload plus **one** small companion file. The link
ladder needs `lld_static` PLUS at least: a guest object (`/HELLO.O`), a crt
object (`/CRT0.O`), a libc archive (`/LIBC.A`) and a linker script
(`/SIMPLEOS.LD`) staged simultaneously.

`scripts/os/fsexec_mkimg_lld.spl` now does this. Like `fsexec_mkimg_big.spl`
it emits only a FAT32 **structural prefix**; the big payloads are appended raw
by the caller, because a 100 MB-class `lld_static` cannot be held in a Simple
array under the seed interpreter. Shape:

- small files (each ≤ 256 KiB) come from a fixed 8.3 candidate table under
  `build/os/elfexec_lld/stage/` and are materialised **inside** the prefix;
- big payload 1 is `LLD.ELF` (size from `payload_size.txt`), big payload 2 is
  the optional `LIBCXX.A` (`libcxx_size.txt`);
- **no subdirectories at all** — unlike `fsexec_mkimg_big.spl`, which builds a
  `/usr/bin` FHS skeleton — because the guest write path is root-only;
- `SPARE_CLUSTERS = 256` (8 MiB) of free clusters follow the last payload so
  the in-guest FAT32 write path has room for the linked ELF. The 16-cluster
  (512 KiB) reserve `fsexec_mkimg_big.spl` uses for a bare `.o` is not enough
  for a statically linked binary.
- the caller consumes the printed `fsexec_mkimg_lld_status=ok ...` line
  (`payload1_padded_bytes`, `total_bytes`) to do
  `cat prefix LLD.pad [LIBCXX.A] > img && truncate -s total_bytes img`.

Verified host-side 2026-08-06 with a synthetic 4 MB payload plus the real
sysroot `crt0.o`/`simpleos.ld`/`libsimpleos_c.a`/`libc++.a`: `fsck.fat -n -v`
reports a clean *"6 files, 191/447 clusters"* with a 256-cluster free
remainder, and every staged file byte-compares equal when read back at its
computed cluster offset.

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
   **This is now the only structural blocker.**
2. ~~multi-payload stager~~ — RESOLVED, see prerequisite 2 above.
3. No guest `.o` staged for the link input yet (unblocked once a prior
   cc1-gate run's retrieved object, or a fresh cross-compiled one, is placed
   at `build/os/elfexec_lld/hello.o`).
4. Dedicated QEMU run slot — parallel lanes are running QEMU concurrently;
   this increment intentionally does not launch QEMU (STATIC-FIRST, bounded).

Confirmed 2026-08-06 by running the gate: the step-0 prerequisite guard exits
before QEMU with exactly two MISSING lines (`lld_static`, `hello.o`).

## Lane C5 smoke matrix

`test/03_system/os/qemu/sys_qemu_lld_link_smoke_matrix_spec.spl` holds the four
C5 rows — (a) in-guest compile+link+run `hello.c`, (b) two-TU C program, (c)
C++ hello against `/LIBCXX.A`, (d) `-O0` vs `-O2` byte-compared against the
host cross build of the same `.i`. Rows are fail-closed and classify as
`pass` / `missing-media:<path>` / `boot-fail:<marker>`; `skip()` is never used.
A row only passes when the retained serial transcript carries every marker of
that row (via the shared `classify_serial`, with `[wf-diag]` treated as a
FAT32-write failure) — presence of a log file is never itself a pass. Row (d)
additionally byte-compares the retrieved objects against the host cross build.
Today, with the toolchain absent, it reports **5 examples, 4 failures** —
the four rows visibly RED with
`blocked:<row>` + `CLASSIFIED: missing-media:build/os/clang_static/bin/clang_static`,
and the infrastructure row green.

See `.spipe/simpleos_harden_p6_toolchain/state.md` for the lane-tracking form
of this same blocker list.

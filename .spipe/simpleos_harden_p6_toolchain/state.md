# Lane P6 — Toolchain (ld.lld ladder)

## Goal
Master-plan §13 / tranche item 13 (§24.13): close ladder rungs 3-6 of the
in-guest LLVM toolchain — `ld.lld` starts via ordinary FS-exec (rung 3),
links a guest-generated object into an ELF (rung 4), the resulting ELF
starts from the filesystem (rung 5), and returns an expected status+output
(rung 6). Rungs 1-2 (clang --version, cc1 emits object) are already proven
under OVMF (`scripts/os/scp_retrieve_over_ssh_uefi.shs`).

## Status: PREPARED-POSTPONED

This increment is **STATIC-FIRST and bounded by instruction**: author an
honest, correctly-structured gate + ladder doc; do **not** launch QEMU
(parallel lanes are running QEMU concurrently on this host; the run itself
is deferred to a dedicated slot). The gate script exists and is real — its
own step-0 prerequisite check is what currently prevents it from reaching
the QEMU boot section, not a stub or placeholder. Verified by actually
running it (see "Verification performed" below): it fails closed with exit 1
and never invokes `qemu-system-x86_64`.

## Owner
P6 / toolchain lane, SimpleOS production harden parallel plan
(`doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md`).

## Files produced this increment
- `scripts/os/ssh_lld_link_uefi.shs` — the rungs-3-6 gate script, modeled
  closely on `scripts/os/ssh_simple_hello_uefi.shs` and
  `scripts/os/scp_retrieve_over_ssh_uefi.shs` (OVMF pflash boot only, never
  `-kernel`, never relies on `isa-debug-exit` for the verdict — board-runnable
  rule). Has its own fail-closed prerequisite gate as step 0.
- `doc/03_plan/os/in_guest_lld_link_ladder.md` — the 4 rungs, prerequisites,
  resume command, expected evidence artifacts, blockers.
- This file.

## Is ld.lld already staged in the guest image? **NO.**

Verified statically (2026-07-27), evidence paths:
- `build/os/clang_static/` does not exist on this host at all — neither
  `clang_static` nor `lld_static` has ever been produced here, even though
  `src/os/port/llvm/clang_static.shs` supports `SIMPLEOS_LLVM_TOOL=lld` to
  produce `build/os/clang_static/bin/lld_static` (same relink mechanism the
  proven cc1 gate uses for `clang_static`; see that script's `case "$TOOL"`
  dispatch, `src/os/port/llvm/clang_static.shs:55-59`).
- `build/os/llvm/cross-x86_64-unknown-simpleos/build.ninja` does not exist —
  the upstream LLVM cross build tree is incomplete/cleaned on this host, so
  `bin/lld` (the object `clang_static.shs` would relink) has not even been
  cross-compiled. `build/os/llvm/cross-x86_64-unknown-simpleos/` and
  `build/os/llvm/host-tools/` directories exist but are stale/empty of a
  buildable ninja graph.
- `build/os/sysroot/` (crt0.o, libc++, `simpleos.ld`) DOES already exist —
  not a blocker.
- `scripts/os/make_os_disk.c` (the general desktop disk-image builder) was
  checked directly: it stages LLVM/clang/rust only as
  `status=standalone-required` placeholder manifests
  (`/usr/share/simpleos/toolchain/{llvm,clang,rust}/...`,
  `make_os_disk.c:932-934`), never a working `ld.lld` binary.
- `scripts/os/fsexec_mkimg_big.spl` / `scripts/os/fsexec_mkimg_simple.spl`
  (the only two working guest-image stagers in the repo) each stage exactly
  ONE big ELF payload + one small companion file — neither can stage
  `lld_static` + crt0.o + a guest object + a linker script simultaneously,
  which the link rungs need.

Conclusion: **no path in this repository stages a working `ld.lld` into any
SimpleOS guest image today.** This is a genuine, previously-undocumented gap
(now recorded in the ladder doc), not merely an unexecuted-but-ready gate.

## Missing prerequisites (in dependency order)
1. **`lld_static` build product** — `sh src/os/port/llvm/build.shs cross`
   (multi-hour LLVM cross build) then
   `SIMPLEOS_LLVM_TOOL=lld sh src/os/port/llvm/clang_static.shs`.
2. **Multi-payload guest image stager** — a new script (working name
   `scripts/os/fsexec_mkimg_lld.spl`) that stages `lld_static` + `crt0.o` +
   a guest object + `simpleos.ld` in one FAT32 image. Not authored: writing
   new `.spl` staging logic is outside this lane's exclusive-path scope for
   this increment (exclusive paths: `scripts/os/ssh_lld_link_uefi.shs`,
   `doc/03_plan/os/in_guest_lld_link_ladder.md`, this state file).
3. **A guest-target `.o` to link** — reuse a byte-exact object retrieved by
   `scripts/os/scp_retrieve_over_ssh_uefi.shs`'s getfile step, or
   cross-compile a fresh one, staged at `build/os/elfexec_lld/hello.o`.
4. **A dedicated QEMU run slot** — parallel lanes are running QEMU
   concurrently right now; this increment intentionally does not contend for
   that resource.

Host tooling (`grub-mkstandalone`, `qemu-system-x86_64`, `sshpass`, OVMF
firmware) is already present on this host — verified via the script's own
prerequisite gate output; NOT a blocker.

## Exact resume command
```sh
sh scripts/os/ssh_lld_link_uefi.shs
```
Fails closed today (exit 1) printing every missing prerequisite from the
list above with a build hint. Once prerequisites 1-3 land it will attempt
the real OVMF boot + SSH ladder (rungs 3-6) exactly as the two proven
sibling gates do; env overrides: `SEED`, `LLD_BIN`, `GUEST_OBJ`, `CRT0_OBJ`,
`LINKER_SCRIPT`, `SKIP_STAGE`, `SKIP_KERNEL`, `QEMU_MEM`, `BOOT_WAIT`,
`SSH_PORT`.

## Retained artifacts location (once run)
- `build/os/ssh_lld_link_uefi.serial.log` — serial transcript (L1-L3 UEFI
  boot ladder + rungs 3-6).
- `build/os/elfexec_lld/fat32-lld.img` — staged guest image.
- `build/os/simpleos_ssh_ring3_uefi128_lld.elf` — kernel used for this gate.

## Verification performed this increment
- `sh -n scripts/os/ssh_lld_link_uefi.shs` — POSIX shell syntax OK.
- `sh scripts/os/ssh_lld_link_uefi.shs` (actually executed, no `--dry-run`
  flag needed — the script's own prerequisite gate makes this safe) — output:
  ```
  [lld-link] MISSING: build/os/clang_static/bin/lld_static -- build: ...
  [lld-link] MISSING: scripts/os/fsexec_mkimg_lld.spl -- multi-payload ...
  [lld-link] MISSING: build/os/elfexec_lld/hello.o -- a guest-target ...
  [lld-link] ===== RESULT: PREPARED-POSTPONED -- prerequisites not met, QEMU NOT launched =====
  ```
  Exit code 1. `qemu-system-x86_64` was never invoked (confirmed: no QEMU
  process spawned, no serial log produced). crt0.o, the linker script, and
  all host tools (grub-mkstandalone/qemu-system-x86_64/sshpass/OVMF) passed
  their checks — only the 3 items above are outstanding.

## Postponement is recorded, not faked
No rung above was claimed PASS. The gate script exists, is syntactically
valid, mirrors the proven sibling gates' structure and evidence contract,
and was proven to fail closed rather than silently no-op or fabricate a
serial log. Executing rungs 3-6 for real is deferred to a session that (a)
has budget for the multi-hour LLVM cross build, (b) authors the multi-payload
stager (a separate, larger task), and (c) has a free QEMU slot.

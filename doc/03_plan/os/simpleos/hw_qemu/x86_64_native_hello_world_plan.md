# SimpleOS x86_64 QEMU Native Hello World Plan

Date: 2026-08-04

## Objective

Boot SimpleOS under x86_64 QEMU, use a native ELF produced by the Simple
compiler, execute it inside the guest, and capture exact `Hello World` evidence.

## Acceptance criteria

1. A fresh native x86_64 Simple program is compiled with stub fallback disabled.
2. QEMU boots the patched SimpleOS kernel from an isolated worktree.
3. The guest loads and executes the fresh ELF rather than a bundled substitute.
4. Captured guest/SSH evidence contains exact `Hello World` output and a
   successful program exit.

Each criterion is verified once. Work stops after convergence or after three
build/fix/verify cycles.

## Ownership and isolation

- Worktree and merge owner: Codex root lane.
- Final reviewer: Codex root lane after QEMU evidence capture.
- Parallel review lanes: build-capability review, VMM-anchor review, and QEMU
  artifact review are complete; they do not own active source edits.
- Canonical repository changes: none. All compatibility edits and generated
  evidence remain under `/private/tmp/simple-phase2-native-hello-20260804`.
- Unrelated dirty compiler, GPU, QEMU, and bootstrap work is preserved.

## Current evidence

- Complete: Phase 3 host Cranelift compiler
  `/Users/ormastes/simple/build/native_probe/simple` built the Phase 2 focused
  SimpleOS compiler at `bin/release/x86_64-unknown-simpleos/simple`.
- Compiler SHA-256:
  `91828e55fac193e6b695cf6f2aac782d6af11889fd1147f25533ab850284273e`.
- Complete: the strict FAT image at
  `build/os/elfexec_simple/fat32-simple.img` contains byte-identical compiler
  aliases at `/usr/bin/simple`, `/bin/simple`, and all four `/sys/apps/simple*`
  paths. `/HELLO.SPL` contains exact `Hello World` source.
- Complete: Phase 3 Cranelift built the SSH/fsexec kernel at
  `build/os/simpleos_ssh_ring3_uefi128_laneb.elf`; its final ELF checker passes.
- Complete: QEMU/OVMF/GRUB boot reached the SimpleOS SSH accept loop, loaded
  the 2.9 MiB Phase 2 compiler into a private CPL3 address space, and opened
  `/HELLO.SPL` from NVMe after the shared-root fix.
- Evidence: `build/native_probe/desktop_toolchain_ui/object-emit-cycle2-hang.serial.log`
  and `build/os/ssh_simple_hello_uefi.serial.log`.
- Blocked after the third fresh fix/diagnostic cycle: the Phase 2 compiler
  consumed one vCPU for seven minutes after `post-read`; the equivalent native
  macOS focused compiler isolated a MIR trap in
  `plan_synthetic_driver_registration` (`field access on nil receiver`). Two
  concrete attribute-default fixes did not remove the trap.
- Additional native-link prerequisite: neither Phase 2 nor Phase 3 contains a
  guest-native `/usr/bin/ld.lld`. Phase 3 is arm64 Mach-O and cannot execute in
  SimpleOS. No matching local, release, or GitHub Actions artifact exists.

## Converged implementation fixes

- The archive helper now selects `llvm-ar` on macOS for Phase 3 SysV archives.
- A separate SimpleOS compiler-runtime object owns the target-only ABI bridges
  without displacing the pure-Simple runtime.
- Equal-second payload/stamp mtimes are accepted only when the stamped SHA-256
  still matches the exact ELF.
- The architecture-owned x86_64 VMM publishes its PML4 root through the shared
  runtime anchor. Page-map/read/unmap/translate operations now consume that
  anchor, and NVMe BAR mapping fails closed instead of logging false success.
- The focused compiler now links with the staged `/usr/lib/SIMAIN.O`, removing
  the guest Clang dependency while retaining a real external-link boundary.
- The SSH evidence wrapper now retains the real SSH exit code and requires the
  configured marker, so transport failure cannot pass. It can also reuse a
  previously verified EFI/kernel artifact on macOS and detects prefixed GRUB.

## Remaining execution steps

1. In a fresh capped session, fix the concrete `HirFunction` layout/attribute
   invariant exposed by `plan_synthetic_driver_registration`; require the host
   focused diagnostic to emit an x86_64 ET_REL object before another QEMU boot.
2. Build a genuine x86_64 SimpleOS `lld_static` from the pinned LLVM 20 fork in
   CI or an isolated build host. The CI lane must also build/reuse libc++abi,
   libunwind, and compiler-rt; Phase 3 alone is not a guest-linker substitute.
3. Rebuild the Phase 2 focused compiler, stage `lld_static` as
   `/usr/bin/ld.lld`, retain `/usr/lib/SIMAIN.O`, and rebuild the strict image.
4. In one final fail-closed QEMU lane run `/usr/bin/simple --version`, then
   `/usr/bin/simple compile --native /HELLO.SPL -o /TMP/HELLO.ELF`, then execute
   `/TMP/HELLO.ELF`; require exact `Hello World` and exit 0.
5. Add the executable SSpec and mirrored operator manual, update state/guide,
   perform one final high-capability review, and stop on PASS.

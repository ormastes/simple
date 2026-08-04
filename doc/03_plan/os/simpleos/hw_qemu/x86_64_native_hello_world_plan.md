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

- Complete: Phase 3 Cranelift compiler
  `/Users/ormastes/simple/build/native_probe/simple` built a fresh focused
  SimpleOS compiler at `bin/release/x86_64-unknown-simpleos/simple`.
- Compiler SHA-256:
  `91828e55fac193e6b695cf6f2aac782d6af11889fd1147f25533ab850284273e`.
- Complete: the strict FAT image at
  `build/os/elfexec_simple/fat32-simple.img` contains byte-identical compiler
  aliases at `/usr/bin/simple`, `/bin/simple`, and all four `/sys/apps/simple*`
  paths. `/HELLO.SPL` contains exact `Hello World` source.
- Complete: Phase 3 Cranelift built the SSH/fsexec kernel at
  `build/os/simpleos_ssh_ring3_uefi128_laneb.elf`; its final ELF checker passes.
- Complete: QEMU/OVMF/GRUB boot reached the SimpleOS SSH accept loop and loaded
  the 2.9 MiB compiler into a private CPL3 address space.
- Evidence: `build/native_probe/desktop_toolchain_ui/version-gate-cycle3.log`
  and `build/os/ssh_simple_hello_uefi.serial.log`.
- Blocked after the third boot/fix cycle: the remote command used
  `/usr/bin/simple simple --version`. The loader already prepends argv[0], so
  the compiler interpreted `simple` as a source filename. The correct command
  is `/usr/bin/simple --version` with no dummy token.
- Additional native-link prerequisite: the image has no guest-native
  `/usr/bin/ld.lld`. The focused compiler also generates its entry wrapper by
  invoking `clang`; the next lane should use the already-staged
  `/usr/lib/SIMPLEEN.O` or stage a guest-native clang.

## Converged implementation fixes

- The archive helper now selects `llvm-ar` on macOS for Phase 3 SysV archives.
- A separate SimpleOS compiler-runtime object owns the target-only ABI bridges
  without displacing the pure-Simple runtime.
- Equal-second payload/stamp mtimes are accepted only when the stamped SHA-256
  still matches the exact ELF.
- The architecture-owned x86_64 VMM publishes its PML4 root through the shared
  runtime anchor; the loader then created a real private user address space.
- The SSH evidence wrapper now retains the real SSH exit code and requires the
  configured marker, so transport failure cannot pass.

## Remaining execution steps

1. Start a fresh capped boot lane and run `/usr/bin/simple --version` without
   the extra `simple` token. Do not rerun any command from this exhausted lane.
2. Stage a genuine x86_64 SimpleOS `ld.lld`, and make the focused linker consume
   `/usr/lib/SIMPLEEN.O` instead of invoking an absent guest clang (or stage a
   genuine guest-native clang).
3. Rebuild the focused compiler/image once, then run
   `/usr/bin/simple compile --native /hello.spl -o /hello-native`.
4. Execute `/hello-native` once and require exact `Hello World` plus exit 0.
5. Add the executable SSpec and mirrored operator manual, update the state and
   guide, perform one final high-capability review, and stop on PASS.

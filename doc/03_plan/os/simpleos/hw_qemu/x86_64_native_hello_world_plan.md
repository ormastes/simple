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

- Complete: fresh native ELF at
  `build/native_probe/desktop_hello/hello.elf`.
- Complete: compiler evidence at
  `build/native_probe/desktop_hello/compile.log`.
- Complete: staged FAT disk containing `/HELLO.ELF` at
  `build/native_probe/desktop_hello/qemu/disk.img`.
- Complete: isolated VMM root-anchor workaround in `vmm_core.spl` and
  `baremetal_stubs.c`.
- Complete: UEFI/GRUB packaging skeleton under
  `build/native_probe/hello_qemu/ssh/`.
- Blocked: cycle 3 reached its 45-minute external timeout without producing
  `build/os/simpleos_ssh_hello_native.elf` or a compiler diagnostic.
- Verified unusable for this lane: the phase-2 and phase-3 bootstrap bridge
  artifacts are 123 KB seed wrappers whose `native-build` command reports that
  full Simple lowering/codegen is unavailable.

## Fix cycles

### Cycle 1 — complete, failed with actionable parser error

The kernel closure reached `rsa_pubkey.spl` and rejected an enum destructuring
`if val` pattern. The isolated source now uses the established exhaustive
`match` form. No canonical file was edited.

### Cycle 2 — complete, failed with architecture-variant parser errors

The deployed compiler parsed the first architecture variants in
`process_image.spl`, then rejected later repeated multiline definitions. The
isolated x86_64 build copy now retains only the x86_64 implementation of that
private helper; canonical multi-architecture source is unchanged.

### Cycle 3 — complete, timed out

The final cache-preserving build remained CPU-active but reached the 45-minute
external guard (`RC=124`). It produced neither a kernel ELF nor a diagnostic;
the captured log is empty. The three-cycle cap is exhausted, so no fourth build
or QEMU attempt is permitted in this lane.

## Remaining execution steps

1. Obtain a full-driver phase-4/self-hosted compiler that completes the x86_64
   LLVM kernel closure within the guard, or fix/measure the compiler timeout in
   a fresh scoped lane.
2. Produce and validate `build/os/simpleos_ssh_hello_native.elf` once.
3. Copy the kernel to the prepared UEFI ESP as `/boot/kernel.elf`.
4. Boot QEMU with the staged FAT disk, NVMe device, serial capture, and SSH
   forwarding on host port 42322.
5. Wait for the guest SSH accept loop, then execute `/HELLO.ELF` once.
6. Capture SSH output and the serial log, verify exact `Hello World` and exit
   success, stop QEMU, report convergence, and stop work.

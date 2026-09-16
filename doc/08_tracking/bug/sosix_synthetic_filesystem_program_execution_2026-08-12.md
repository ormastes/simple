# SOSIX filesystem-program receipts are synthetic on x86_32, ARM32, and RISC-V

## Status

Open, release-blocking. Retained Linux diagnostic rows prove FAT media access,
directory enumeration, package/header validation, and marker-based launch-state
construction. They do not prove that a filesystem program executed.

## Exact synthetic paths

- `examples/09_embedded/simple_os/arch/x86_32/initrd_fs_exec_probe_entry.spl`
  - `x86_32_dispatch_installed_syscall_abi` scans the initrd for fixed strings
    and returns fixed pids `2001`/`2002`.
  - `spl_start` treats those positive integers as execution success.
- `examples/09_embedded/simple_os/arch/arm32/boot/baremetal_stubs.c`
  - `arm32_load_smf_process` reads a FAT file, validates ELF class, endianness,
    machine, entry, and a marker string, then records a synthetic pid/entry.
  - `rt_arm32_smf_cli_load` returns that validation result; it never transfers
    control to the loaded entry or observes program output/exit.
- `examples/09_embedded/simple_os/arch/common/riscv_common.h`
  - `riscv_load_smf_process` follows the same copy/header/marker/synthetic-pid
    model used by `rt_riscv_smf_cli_load`; no loaded instruction executes.
- `examples/09_embedded/simple_os/arch/{riscv32,riscv64}/smoke_entry.spl` and
  `examples/09_embedded/simple_os/arch/arm32/fs_exec_entry.spl` print launch
  success after the validation helpers return.
- `scripts/os/make_os_disk.c::elf_image` creates the fallback package payload
  from an ELF header/program header plus a marker string. It contains no real
  target program instruction stream at the declared entry `0x1000`.

Consequently, current `SMF_CLI_LAUNCH_OK`, x86_32 `app execution ok`, GUI
launch/render, and `TEST PASSED` markers are diagnostic package/load receipts,
not arbitrary filesystem-program execution evidence. Adding BEGIN/stdout/END
markers around these branches would fabricate target output and rc.

## Unblock contract

Each promoted guest must satisfy one of these real execution models:

1. Stage a target-machine executable containing actual instructions, map its
   loadable segments with correct permissions/relocations, transfer control
   through the guest scheduler/user-entry ABI, and capture target-origin writes
   plus the actual exit syscall/status; or
2. Stage a defined guest bytecode program and execute it through a real
   in-guest interpreter whose bytecode identity, stdout writes, and returned rc
   are derived from the mounted file.

The serial contract must be emitted by the execution owner and include:

```text
FS_PROGRAM_BEGIN path=<mounted path> identity=<target payload hash or immutable id>
FS_PROGRAM_STDOUT <exact target-produced output>
FS_PROGRAM_END rc=0
```

Acceptance must turn red for a changed payload/hash, invalid instruction or
bytecode, missing write, nonzero exit, entry not reached, host-side/canned
output, fixed pid-only dispatch, or a package that is only header/marker bytes.
Only after that sabotage coverage passes may descriptors require these markers
or a matrix row claim arbitrary-program proof.

## Evidence disposition

The diagnostic artifacts under
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/diagnostic/` remain useful
FAT/list/load evidence. They must remain non-PASS and must not be renamed or
copied into collector rows as filesystem execution receipts.

## Static audit of reusable real-execution owners (2026-08-12)

### x86_32

An earlier retained receipt claims a real target program:

- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_32/20260811T090000Z/serial.log`
- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_32/20260811T090000Z/evidence.env`

It records `FS_PROGRAM_BEGIN`, `hello from x86_32 filesystem program`, and
`FS_PROGRAM_END exit=0 target_native=true`, with kernel hash
`032f2aaf9133f145af3df0a18dcf2b31e1704f7343404c7dba0ee0f15844fe78` and
image hash `791b9873310380a969e3aafb08a5de20ad3f487cd098946053d9570c864bd8db`.
However, current tracked source contains no producer for those markers and its
only live mechanism is `x86_32_int80_probe_handler` plus kernel-origin
`rt_x86_32_trigger_int80`; that proves a kernel-triggered trap/`iret`, not a
CPL3 filesystem payload. The old transcript is therefore not a reusable
implementation owner until its exact source/artifact lineage is recovered and
the payload instruction bytes and privilege level are independently audited.

Minimal honest slice: stage one real i386 ELF with code that invokes a
user-callable `int 0x80` debug-write and exit ABI; add a CPL3 entry trampoline
with user CS/SS and stack (the existing handler/dispatcher may own the return
side); load its PT_LOAD bytes from `QEMUNONC`-style initrd FAT traversal; capture
the actual write and exit status. Do not reuse fixed pid dispatch.

### ARM64

This is the most complete reusable lane. Owners are:

- `examples/09_embedded/simple_os/arch/arm64/boot/crt0.S`:
  `arm64_enter_user_virtual`, EL0 `eret`, VBAR SVC handling, and return to the
  saved EL1 frame.
- `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`:
  `rt_arm64_enter_recorded_user_live`, `rt_arm64_handle_user_svc`, and
  `rt_arm64_exec_probe_live_real` (real mapped AArch64 instructions, EL0 SVC,
  actual exit code).
- `examples/09_embedded/simple_os/arch/arm64/user_fsexec_src/mounted_elf.S`:
  a real mounted target containing SVC instructions.
- `src/os/kernel/loader/arm64_fs_exec_spawn.spl`: filesystem prepare/handoff
  owner, though its own comment correctly says the marker package is not yet
  EL0 execution proof.

Minimal slice: replace the inline two-instruction probe source with PT_LOAD
bytes derived from the mounted `mounted_elf.S` artifact, preserve the existing
user-AS mapping/`arm64_enter_user_virtual` path, extend
`rt_arm64_handle_user_svc` with a bounded debug-write operation whose bytes
come from EL0 memory, and use its existing exit return as `FS_PROGRAM_END rc`.
Hash the mounted file before entry and bind BEGIN to that hash/path.

### RISC-V 64

Reusable production-shaped owners already exist:

- `src/os/kernel/arch/riscv64/user_entry.spl::dispatch_enter_user_blocking`
  selects the scheduled user task, switches SATP, executes `fence.i`, calls
  `_rv64_enter_user`, restores kernel SATP, and returns the exit code.
- `src/os/kernel/arch/riscv64/trap_vector.spl::_rv64_enter_user` saves a kernel
  frame and executes `sret`; the trap vector owns return-to-supervisor.
- `src/os/kernel/loader/riscv64_fs_exec_spawn.spl` already connects filesystem
  prepare to that blocking handoff.
- `src/os/kernel/loader/executable_source.spl::_minimal_rv64_exec` contains real
  RV64 instructions for debug-write, getpid, and exit, but is synthesized in
  memory rather than loaded from the FAT path.

Minimal slice: serialize the existing `_minimal_rv64_exec` bytes as the actual
mounted test file (or stage an equivalent target ELF), make the fs-exec path
consume those mounted bytes rather than `resolve_executable_bytes` synthesis,
then route through `riscv64_fs_exec_spawn_ring3`. Bind BEGIN to mounted hash,
capture syscall-60 output in the trap/syscall owner, and use the returned
`dispatch_enter_user_blocking` status for END rc.

### RISC-V 32

The repository has `_minimal_rv32_exec` instruction generation and RV32 task
image construction, but no RV32 counterpart to the complete RV64
`dispatch_enter_user_blocking`/`_rv64_enter_user` saved-frame `sret` owner was
found in this audit. Current RV32 smoke uses the shared synthetic load helper.

Minimal slice: port the RV64 blocking user-entry interface to RV32 widths and
Sv32 context/trap layout, including saved kernel frame, user `sret`, syscall
debug-write/exit dispatch, and returned exit status; then stage the existing
real `_minimal_rv32_exec` bytes as a mounted ELF and feed them through the
filesystem loader. This is a new architecture owner, not a marker change.

### ARM32

No ARM32 user-mode entry/return owner analogous to ARM64 `eret` or RV64 `sret`
was found. `arm32_load_smf_process` stops after ELF validation and synthetic
pid/entry storage. Existing `svc #0x123456` usage is a kernel/firmware service
call and is not a user-process exception path.

Minimal slice: add an ARMv7 user-mode context owner (user page tables or the
lane's explicitly documented flat isolation model), CPSR mode/user stack entry,
SVC vector dispatch for bounded debug-write and exit, and a saved kernel return
frame. Stage a real ARM ELF with `svc` write/exit instructions from FAT, map its
PT_LOAD bytes, and derive stdout/rc from that trap path. ARM64 code can inform
the contract but cannot be copied as an AArch32 control-transfer implementation.

### Recommended implementation order

1. ARM64: mounted ELF bytes into the already-live EL0/SVC/exit path.
2. RV64: mounted ELF into the already-complete scheduler/SATP/`sret` path.
3. x86_32: recover the old receipt's source or implement a genuine CPL3
   `int 0x80` entry around the existing handler.
4. RV32: port the RV64 saved-frame user-entry owner to Sv32/RV32.
5. ARM32: create the missing user-entry/SVC/return owner.

No architecture may claim completion merely because an embedded proof binary
or inline instruction probe runs; the bytes must be read from the mounted path
whose identity is printed in BEGIN.

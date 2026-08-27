<!-- codex-design -->
# SimpleOS real filesystem program execution boundary

## Decision

Use a real freestanding ELF payload for each guest ISA. Share the filesystem-to-loader request, process lifecycle, two-call user ABI, and receipt schema across x86_32, ARM32, RISC-V 32, and RISC-V 64. Do not route acceptance through the current marker-only or synthetic-PID launch paths.

A Simple guest-bytecode payload is rejected for this slice. It would be portable, but no admitted in-guest interpreter currently proves instruction fetch, stdout, and termination on these guests. Adding one would make the interpreter a larger prerequisite than the execution boundary being tested. Bytecode may be added later as a second program format after the ELF boundary passes.

## Required boundary

The future architecture-neutral owner exposes one value-threaded operation:

`fs_program_execute_v1(request, filesystem, loader, scheduler, user_io) -> FsProgramExecutionResultV1`

`FsProgramExecutionRequestV1` contains `path`, expected SHA-256, argv, environment, caller process/capability identity, execution nonce, stdout byte limit, and deadline. The path is canonical and absolute. The first payload is `/sys/apps/fs_exec_probe.elf`; argv contains only that path and the nonce; environment is empty.

`FsProgramExecutionResultV1` contains status/reason, filesystem object identity and generation, exact file size/hash, ELF class/machine/entry, mapped segment count, scheduler task identity/generation, observed-start sequence, captured stdout bytes and truncation flag, exit kind/code, and start/finish sequence. A numeric PID alone is never success evidence.

The owner performs these transitions in order:

1. Resolve and read the named filesystem object through the mounted guest filesystem owner; hash the exact bytes read.
2. Reject hash, ELF class, endianness, machine, segment bounds/overlap, executable-entry, relocation, W^X, or address-space-policy mismatch before creating a task.
3. Reserve a scheduler task identity, create a fresh address space, map only validated load segments, install a bounded user stack containing argv, and commit the task once.
4. Record `started` only after the scheduler observes the target entry executing in user mode.
5. Accept only two user operations: `write_stdout(buffer, length)` and `exit(code)`. x86_32 lowers these through `int 0x80`, ARM32 through `svc`, and RISC-V through `ecall`; register decoding is ISA-private but returns the same architecture-neutral event values.
6. Capture at most 256 stdout bytes. Reject invalid user ranges, calls from another task generation, a second exit, timeout, fault, or capture overflow. Reap the exact task generation before publishing completion.

The initial payload writes exactly `SIMPLEOS_FS_EXEC_OK arch=<arch> nonce=<nonce>\n` in one or more bounded writes and exits with code `37`. A nonzero target code prevents a wrapper from equating “spawn returned” or a default zero with program completion.

## Ownership and ports

- Filesystem owner: canonical lookup/read and immutable object identity.
- ELF loader owner: validation and mapping plan; never schedules or fabricates output.
- Scheduler/process owner: task generation, user-mode start observation, fault/exit, and reap.
- ISA trap adapter: register decoding/encoding only; forwards authenticated task identity.
- Execution coordinator: orders the owners and constructs the receipt. It owns no page tables, filesystem cache, or synthetic PID allocator.
- Serial/QEMU probe: prints a receipt only after validating the completed result; it does not manufacture lifecycle fields.

All mutable owner values are explicitly returned and reinstalled. If a live filesystem, scheduler, address-space, or trap owner cannot be installed honestly, execution returns `blocked:owner-not-installed`; it must not call a compatibility spawn helper.

## Artifact contract

Each payload is an ELF32 little-endian executable for x86_32, ARM32, or RISC-V 32, or ELF64 little-endian for RISC-V 64. It is static, has no interpreter, dynamic section, unresolved symbol, TLS, constructor, allocator, libc, or writable-executable segment. Its build receipt records source hash, compiler identity, target triple, ELF hash, and image hash. The image builder must copy those exact bytes into the canonical path and retain a post-image readback hash.

The serial receipt is nonce-bound and includes one line per lifecycle event followed by:

`FS_PROGRAM_EXEC_RESULT status=pass arch=<arch> path=/sys/apps/fs_exec_probe.elf stdout_sha256=<hex> exit_kind=exited exit_rc=37 nonce=<nonce>`

PASS requires agreement among image readback hash, guest file hash, ELF metadata, task generation, stdout bytes/hash, nonce, and reaped exit code.

## Failure semantics

Missing or stale media is blocked. Invalid executable, wrong hash/ISA, mapping failure, user fault, forged/stale task identity, stdout overflow, timeout, missing reap, wrong output, or wrong exit code is failed. No marker, prepared task, returned PID, loader parse, or scheduler registration alone is execution evidence.

## Implementation order

1. Define the pure request/result and lifecycle validator with sabotage specs.
2. Add the minimal two-operation user ABI and ISA adapters.
3. Connect the existing real filesystem, ELF mapping, address-space, and scheduler owners without compatibility spawn paths.
4. Build and image-stage each ELF payload with retained hashes.
5. Enable one guest at a time; keep every unconnected guest blocked.

## Implementation status (2026-08-12)

- **ARM64 — implemented, static contract PASS 10/10.** The mounted `/FSEXEC.ELF` PT_LOAD bytes feed the existing EL0 entry/SVC-return owner; the payload emits bounded nonce-derived stdout and exits with `37`. `test/01_unit/os/kernel/arch/arm64_user_exit_return_contract_spec.spl` passed all 10 examples. This is static/simulator evidence only: no fresh QEMU boot has yet proved the mounted bytes executing at EL0, so ARM64 remains pending live admission.
- **RV64 — implemented, focused diagnostic PASS.** `rv64_real_exec_payload.spl` builds the nonce-bound RV64 ELF, `riscv64_fs_exec_spawn.spl` requires the target nonce marker in the exact mounted FAT bytes, and the trap/user-entry path restores the saved S-mode continuation before exact-child reap. The canonical smoke entry, nonce reader, VFS mount, and matrix markers were recovered after a concurrent overwrite; their source/static and freestanding C gates pass. This remains non-live evidence pending the frozen production compiler and fresh QEMU execution.
- **RV32 — pure payload boundary implemented, focused diagnostic admission covered, live blocked.** The ELF32 builder/simulator proves nonce-bound `ecall 60` bytes and exit `37`; exact mounted-byte admission still returns `-95` with `rv32-sv32-live-entry-not-installed`. The bounded implementation audit found no explicit-root Sv32 mapper/destructor, no U-mode trap vector or saved supervisor continuation, and no implementation for the declared RV32 context externs. The exact unblock contract is recorded in `doc/08_tracking/bug/rv32_sv32_user_entry_trap_owner_missing_2026-08-12.md`.
- **x86_32 — real payload/static gate PASS, live blocked.** `mounted_elf32.S` contains real i386 instructions for bounded caller-supplied nonce stdout through `int 0x80` syscall 60 and exit `37`; `check-simpleos-x86-32-user-elf.shs` passed ELF32/i386/executable-PT_LOAD/opcode checks. The focused Simple ownership spec hit the existing 120-second test-daemon worker timeout before executing examples, so it is not a spec PASS. The live lane has only a DPL3 IDT gate invoked from ring 0; GDT/TSS user selectors, PT_LOAD/user-address-space mapping, user stack/`iret` entry, and exit-return/reap ownership remain absent.
- **ARM32 — source/static live lifecycle implemented, QEMU pending.** The ELF32/ARM EABI payload, private L1/frame owners, authenticated transition token, vector/SVC return, parent-authoritative exit/reap, nonce-bound mounted-byte staging, and canonical entry are present. The real FAT listing walker was recovered after a concurrent overwrite. Static sabotage and ARMv7 syntax gates pass, but no fresh production-toolchain QEMU receipt proves the live User transition, so the matrix row remains BLOCKED.
- **x86_64 — real CPL3 mechanism exists, matrix integration blocked.** The filesystem streaming loader maps real ELF64 `PT_LOAD` segments, enters CPL3 through `iretq`, handles syscall 60, and returns syscall-0 status through a saved kernel frame. The current matrix entry never calls that owner and the fs-exec media builder does not default-stage a nonce-bound x86_64 payload. More importantly, the existing path explicitly runs outside the scheduler task lifecycle and leaks its address space, so it cannot prove the required child-generation exit/reap contract. The exact resume boundary is recorded in `doc/08_tracking/bug/x86_64_matrix_real_fs_exec_not_integrated_2026-08-12.md`.

No architecture is complete until a fresh bounded QEMU run correlates mounted-file identity, target-origin stdout, actual exit code, and reap. Static PASS never promotes a matrix row.

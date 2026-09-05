# Authenticated admission six-target dispatch v1

## Scope

The production authenticated filesystem admission path already reads an exact
open binding once, hashes it once, verifies its signed manifest, derives an ELF
layout, and mints consume-once loader authority. Its architecture dispatch was
limited to x86-64, AArch64, and RV64 even though the canonical ELF layout owner
supports all six SimpleOS userland architectures.

`executable_loader_architecture_for_target_v1` now projects the exact target
identity into that existing ELF owner for x86-64, x86-32, AArch64, ARM32,
RV64, and RV32. It accepts only `os = simpleos`, `abi = simpleos`,
and the canonical architecture spellings `x86_64`, `x86`, `aarch64`, `arm`,
`riscv64`, and `riscv32`. Build aliases such as `x86_32`, `arm32`, and
`riscv64gc` remain rejected rather than becoming a second target vocabulary.

## Authority and resource behavior

The projection is pure and allocation-free. Its comparison work is
O(|os| + |arch| + |abi|). It does not read a path, allocate a
catalog slot, verify a signature, mint a token, or weaken the existing exact
manifest/admission target equality checks. Production admission still performs
one bounded image read, one SHA-256 pass, one manifest hash/signature check,
one ELF layout pass, and one authority issue.

This increment does not populate the installed-artifact catalog, install guest
tool payloads, map a process, dispatch a scheduler task, or claim QEMU/physical
execution. Those ownership gates remain active.

## Acceptance coverage

`test/01_unit/os/kernel/loader/executable_admission_target_matrix_v1_spec.spl`
covers all six canonical spellings and rejects aliases, wildcard components,
and foreign operating systems. Per user instruction, the spec was authored but
not executed in this lane.

# SimpleOS compiler/filesystem QEMU routes are absent

Status: implementation in progress

The 18-cell x86/ARM/RISC-V filesystem toolchain matrix previously delegated to
a checker that hard-blocked every non-x86_64 architecture. Its nominal x86_64
scenario is also absent from the QEMU scenario catalog. Existing ARM/RISC-V
fs-exec kernels prove filesystem presence or a limited interpreter handoff but
do not emit the strict compiler/filesystem protocol and do not compile and run
`/HELLO.SPL` as `/TMP/HELLO`.

The first fix establishes a shared, fail-closed guest workflow and protocol
owner. Remaining work is deliberately not claimed complete: add authenticated
fw_cfg readers, real per-architecture process adapters/kernels, scenario
catalog entries, and live retained QEMU receipts. The 32-bit rows also require
target-native payload provisioning before they can leave BLOCKED state.

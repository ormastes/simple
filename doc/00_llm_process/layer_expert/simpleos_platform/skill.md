# Layer expert: SimpleOS platform execution

## Ownership

- Kernel/device drivers own NIC, block, GPU and interrupt mechanisms.
- Syscall owners validate and copy user pointers before kernel access.
- VFS/loader owns filesystem provenance and executable mapping.
- VFS admits `fsync`/`fdatasync` only when the mounted backend advertises
  `DurableSync`; an in-memory WAL flush counter is not a device barrier.
- Server/DB owners retain protocol, authentication, transaction and durability
  semantics; platform code supplies bounded I/O rather than protocol bypasses.
- Evidence controllers own process/QEMU/ADB lifetime and encoded receipts, not
  target mutable state.

## Cross-target rules

ARM64 QEMU, x86 QEMU and physical QRB2210 are distinct capability rows. A
backend or receipt from one cannot promote another. An ARM64 guest on an x86_64
host uses TCG and may prove correctness, not native performance. UNO Q Linux
userspace proves board identity only unless the retained transcript proves the
SimpleOS boot/runtime and filesystem launch.

Every runtime boundary must be the smallest owner facade. Record
`runtime_need`, `facade_checked`, `chosen_path`, and `rejected_shortcuts` before
adding raw runtime plumbing. User pointer/length pairs are range-checked and
copied; errors fail closed. Device children return bounded results to the
parent owner for validation and deterministic commit.

Canonical feature knowledge is in
`doc/00_llm_process/feature_expert/simpleos_server_execution_matrix/skill.md`.
The full cross-subsystem hardening contract and current fail-closed boundary are
also recorded in
`doc/00_llm_process/feature_expert/simpleos_complete_os_hardening/skill.md`.

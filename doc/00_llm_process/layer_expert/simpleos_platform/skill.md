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
# Server protocol boundary update (2026-08-21)

SimpleOS protocol status is tracked in
`doc/07_guide/os/simpleos_server_protocol_status.md`. Platform adapters must not
fork protocol reachability policy: HTTP ALPN and HTTP/SSH capability reporting
share `simpleos_server_protocol_capabilities`, and unsupported transports stay
absent until their production owner exists. Never turn unknown TLS ALPN into
H1, advertise H3 without QUIC, or bypass SFTP's
canonical VFS capability gates with ambient host filesystem access. Live server evidence requires admitted target tooling
and configured credentials.

## Server credential media staging (2026-08-22)

The cross-target disk writer stages KEY/CRT/PK8/MAN through bounded
descriptor-backed snapshots and verifies the exact FAT bytes before atomic
no-clobber publication. x86_64, AArch64, and RV64 use the same credential
contract. Missing, malformed, symlinked, unsafe-mode, changed, mismatched, or
oversized inputs fail before publishing an image; pre-existing images are
preserved. Windows intentionally rejects server-secret staging until an
equivalent no-reparse descriptor boundary is implemented.

## Server-data namespace Phase A contract (2026-08-22)

Syscall ordinals 116–119 are reserved for the future server-data namespace but
have no dispatcher or callable wrapper. `server_data_namespace_v1.spl` freezes
pointer-free C-layout IDs, rights, receipts, states, caps, and pure transition
decisions. Scalar receipts never authorize access: a future kernel owner must
look up and match its stored task-generation, epoch, lease-generation, and
128-bit nonce record. Do not advertise readiness before the distinct DBFS
medium and sole transactional owner from the architecture plan exist.

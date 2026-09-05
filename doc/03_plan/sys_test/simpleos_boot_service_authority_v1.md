# SimpleOS boot service authority v1 test plan

- REQ-BOOT-001: only pinned policy plus a sealed signed catalog and live VFS
  admission can create a service authority.
- REQ-BOOT-002: publication creates one nonzero task with equal concrete,
  pledged Scheduler and IPC pouches.
- REQ-BOOT-003: a valid authority issues exactly one recipe-bound lease;
  replay, target drift, catalog drift, and task exit fail closed.
- REQ-BOOT-004: x86_64, ARM64, and RV64 use the same owner transaction; their
  adapters supply only target/pin configuration.

Unit coverage must exercise policy validation, provenance uniqueness, rollback,
and lifecycle revocation.  A system scenario must retain per-target serial
logs and receipt hashes for filesystem server launch.  It must fail, rather
than merely annotate, when QEMU, media, or the signed input is unavailable.

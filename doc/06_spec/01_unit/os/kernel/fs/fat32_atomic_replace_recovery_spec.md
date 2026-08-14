# FAT32 RecoverableReplaceV1 focused checks

The executable source is
`test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl`.
These checks cover the bounded journal codec and state machine; they do not
claim fresh-boot durability.

| ID | Operator-visible check |
|---|---|
| FAR-001 | Two edits to one LBA coalesce into one complete final image. |
| FAR-002 | Distinct images commit in ascending LBA order; pre-COMMITTED remains old. |
| FAR-003 | Payload corruption invalidates a bank; invalid/ambiguous banks fail closed. |
| FAR-004 | An already-free saved cursor advances idempotently; mismatched FAT state is repair-required. |
| FAR-005 | Capability reports exactly 16 sectors (8192 bytes) and accepts an EOC cursor. |
| FAR-006 | Missing durability, traversal, any route except exact `/SERVER.TMP` → `/SERVER.DB`, overflowed journal extents, non-root after-image LBAs, new-chain reclamation, and more than four images are rejected. |
| FAR-007 | A newer DONE bank wins and is not replayed. |
| FAR-008 | RecoverableReplaceV1 is withheld until mount recovery completes. |
| FAR-009 | Recoverable replacement remains a typed capability distinct from ordinary non-atomic `rename_at`. |

Recovery reads every FAT copy. An interrupted copy-repair may contain only the
saved next pointer or FREE; it rewrites all copies, flushes, and rereads every
copy as FREE before advancing the durable cursor or publishing DONE. Candidate
old/new chains and namespace aliases are walked with volume-bounded fuel and
must be acyclic and disjoint before COMMITTED.

The companion system manual at
`doc/06_spec/03_system/os/server/fat32_database_replace_reboot_spec.md` defines
the still-required fresh-QEMU-process evidence and intentionally red runner.

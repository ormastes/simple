# FAT32 recoverable atomic replace — TLDR

FAT32 rename remains non-atomic.  SimpleOS gains a separate, fail-closed
`RecoverableReplaceV1` capability for allowlisted root database files only.

- A provisioned, fixed 16-sector extent holds two checksummed copy-on-write
  journal banks; missing/invalid storage or durable flush means Unsupported.
- The filesystem mutation owner records complete final directory-sector
  images before changing metadata.  Same-sector changes are coalesced;
  different sectors are replayed before mount publication.
- Old clusters are reclaimed with a durable current/next cursor, then a newer
  DONE record prevents replay of an older committed bank.
- Recovery is idempotent and completes before the root cache/filesystem becomes
  visible.  Corruption or ambiguity fails closed rather than guessing.
- The canonical DB still performs temp write + sync + replace.  Only its final
  target operation maps to this capability; ordinary `rename_at` is unchanged.
- Promotion requires FAR-001..009 crash injection and a fresh-QEMU-process
  public DB read from the same writable image.  UNO Q requires separate reboot
  evidence; GPU work never owns filesystem commit.

Next: `doc/05_design/os/fat32_atomic_replace_recovery.md` and
`doc/03_plan/agent_tasks/fat32_atomic_replace_recovery.md`.

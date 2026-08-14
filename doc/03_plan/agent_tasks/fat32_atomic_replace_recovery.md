# Agent plan: FAT32 recoverable database-root replacement

## Fixed interfaces and invariants

Primary design is
`doc/04_architecture/os/fat32_atomic_replace_recovery.md`; detail contract is
`doc/05_design/os/fat32_atomic_replace_recovery.md`.  Interface names are
`AtomicReplaceRecoveryLevel`, `AtomicReplaceRecoveryCaps`,
`fat32_atomic_replace_caps`, `fat32_atomic_replace`, and
`fat32_atomic_replace_recover`.  Spec helpers and manual step text are fixed in
the detail design.  Any missing oracle stays `fail(...)`.

## Parallel lanes

1. **Journal/provisioning lane:** image descriptor, fixed two-bank extent,
   codec/CRC/generation validation, corrupt/torn-bank unit fixtures.
2. **Filesystem transaction lane:** mutation lock, identity validation,
   same/different-sector image construction, ordered publish, cursor-based FAT
   reclamation.  Must not change ordinary `rename_at` semantics.
3. **Mount/recovery lane:** recover before publish, root cache refresh,
   idempotent replay and fail-closed mount/capability behavior.
4. **Runtime/server lane:** bind canonical database final replace to the typed
   capability and promote persistence caps only from successful recovery/flush.
5. **Fault/reboot evidence lane:** FAR-001..009 deterministic sector/flush
   crash matrix, then fresh-QEMU-process public DB read on the same image;
   physical UNO Q evidence remains a separate required cell.

Each lane owns only its named files and returns an encoded result/evidence
receipt to the filesystem merge owner.  No mutable filesystem object, block
buffer, or raw pointer crosses agents/tasks.  Journal and namespace mutation
remain single-owner and bounded.

## Merge and review

- Lower-model sidecars: N/A for authority-bearing protocol decisions.  They
  may enumerate crash points only after the fixed interface/spec vocabulary
  above, and their matrix must be reviewed rather than accepted directly.
- Merge owner: SimpleOS FAT32 filesystem owner.
- Final reviewer: highest-capability architecture/verification model,
  independent of implementation lanes.
- Maximum three verify/fix cycles.  No release or readiness promotion until
  all exact specs and fresh-boot evidence pass.

## Ordered gates

- [ ] Provisioner reserves and validates exactly 16 non-overlapping sectors.
- [ ] Dual-bank codec survives every torn header/payload/image case.
- [ ] Same-sector and different-sector final images are correct and bounded.
- [ ] COMMITTED/reclaim/DONE ordering is durable and idempotent.
- [ ] Recovery completes before mount publication and cached-root exposure.
- [ ] Capability remains Unsupported for every missing prerequisite.
- [ ] Canonical database adapter consumes the capability without semantic fork.
- [ ] FAR-001..009 pass with no placeholders.
- [ ] Fresh ARM QEMU process reopens the same disk and public DB protocol reads
      exactly the acknowledged generation at every crash point.
- [ ] UNO Q repeats CPU DB/file/server and reboot proof; GPU acceleration is a
      compute-only lane and does not own or weaken filesystem commit.

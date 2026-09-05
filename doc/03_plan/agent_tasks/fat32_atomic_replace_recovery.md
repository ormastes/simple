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

- [x] Provisioner reserves and validates exactly 16 non-overlapping sectors.
      — verified `src/os/kernel/fs/fat32_atomic_replace.spl:15`
      `FAT32_REPLACE_JOURNAL_SECTORS = 16`, `:239 fat32_replace_extent_valid`,
      `:459` descriptor sector-count check
- [x] Dual-bank codec survives every torn header/payload/image case.
      — verified codec `fat32_atomic_replace.spl:129 struct Fat32ReplaceRecord`
      / `:359` header encode, `:41 enum Fat32ReplaceCrashSeam` fault seams;
      oracle `test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:105`
      `describe "FAR-003: corrupt and torn banks"` (green run pinned by the
      FAR-001..009 box below, still open)
- [x] Same-sector and different-sector final images are correct and bounded.
      — verified `test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:82`
      `"FAR-001: same-sector coalescing"`, `:93 "FAR-002: distinct ordered images"`
      over `src/os/kernel/fs/_Fat32Filesystem/atomic_replace_transaction.spl`
      (green run pinned by the FAR-001..009 box below, still open)
- [x] COMMITTED/reclaim/DONE ordering is durable and idempotent.
      — verified `fat32_atomic_replace.spl:28 enum Fat32ReplaceState {Committed,
      Reclaim, Done}`, `:429 fat32_replace_reclaim_transition`; oracles
      `FAR-004: repeated replay and reclamation` (spec `:125`), `FAR-007: DONE
      tombstone` (`:177`) (green run pinned by the FAR-001..009 box below,
      still open)
- [x] Recovery completes before mount publication and cached-root exposure.
      — verified `src/os/kernel/fs/_Fat32Filesystem/mount_and_read.spl:76`
      calls `fat32_atomic_replace_recover_device` before `root_dir_data` is
      published; `mount_owner.spl:36 fn fat32_atomic_replace_recover`; oracle
      `FAR-008: mount-before-publish` (spec `:205`)
- [x] Capability remains Unsupported for every missing prerequisite.
      — verified `fat32_atomic_replace.spl:176 fat32_atomic_replace_unsupported_caps`,
      `:186 fat32_atomic_replace_caps_for(journal_valid, durable_flush,
      recovery_complete)`; oracle `FAR-006: fail-closed policy` (spec `:153`)
- [x] Canonical database adapter consumes the capability without semantic fork.
      — verified `src/os/apps/servers_user/database_persistence_adapter.spl:9-12`
      imports `fat32_atomic_replace_caps`, `:65` combines it with
      `rt_simpleos_file_atomic_caps()`; kernel route guard
      `src/os/kernel/ipc/syscall_file.spl:789 fat32_atomic_replace_path_allowed`
- [ ] FAR-001..009 pass with no placeholders.
      - status 2026-09-05: all nine `describe` blocks exist in
        `test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl`
        with 0 `fail(`/`pending(` placeholders; a green RUN is not recorded —
        on this host `bin/simple` has no `test` command and `simple_seed test`
        aborts on an unrelated parse error in `src/app/io/mod.spl`, so the box
        stays open until a runner verdict is captured.
- [ ] Fresh ARM QEMU process reopens the same disk and public DB protocol reads
      exactly the acknowledged generation at every crash point.
- [ ] UNO Q repeats CPU DB/file/server and reboot proof; GPU acceleration is a
      compute-only lane and does not own or weaken filesystem commit.

## Acceptance

Runnable oracles for the remaining open boxes: `test/03_system/plan_acceptance/fat32_atomic_replace_recovery_spec.spl`
(tagged `@tag:in-development`; one `it` per open box — see
`doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md`).

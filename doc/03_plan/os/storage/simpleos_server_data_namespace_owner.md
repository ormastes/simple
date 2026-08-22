# Implementation plan: second-medium DBFS server namespace

Architecture authority: `doc/04_architecture/os/storage/simpleos_server_data_namespace_owner.md`.

## Acceptance criteria

1. x86_64, AArch64, and RV64 QEMU commands attach distinct root and persistent server-data images; discovery binds serial, role, and UUID rather than probe order.
2. Exactly one `ServerDataNamespaceOwnerV1` owns the server medium, `BlockDevice`, `DbFsDriver`, mount identity, lease table, and recovery/quarantine state.
3. Userspace can acquire only launcher-granted subtree leases and use bounded sync/atomic-replace calls. Forged, stale, reused-task, cross-task, traversal, rights-escalated, and post-revocation operations fail closed.
4. Unmount drains admissions, revokes leases, closes exact-generation handles, waits for active operations, syncs, and unmounts the exact identity. Ambiguity quarantines.
5. Atomic replace is crash consistent at every data/journal/publish/checkpoint boundary, is capped at 16 MiB per independently atomic object, and has one streaming payload pass using a reusable 64 KiB buffer.
6. Two boots of the same data image on every architecture prove in-guest persistent readback and recovery; corrupt or duplicate media proves quarantine.
7. Existing root media and ordinary POSIX VFS behavior remain unchanged. No C/Rust replacement or raw block access is introduced.
8. Optimizer output, same-workload timing, allocation/I/O counts, and peak RSS meet the architecture thresholds.

## Frozen helper and interface names

All lanes target the exact shared names in the architecture document. System specs use these helpers before any sidecar starts:

- `setup_server_data_image_v1(arch, image_path)`
- `setup_server_data_qemu_v1(arch, root_image, data_image)`
- `check_server_data_boot_receipt_v1(log, arch, boot_index)`
- `check_server_data_recovery_receipt_v1(log, expected_generation)`
- `check_server_data_perf_receipt_v1(before, after)`

Manual steps use exactly the seven `step("...")` strings listed in architecture section 9. Any unfinished helper or scenario must call `fail("server-data namespace implementation incomplete")`; `pass_todo` and tautological assertions are forbidden.

## Ordered delivery

### Phase A — contracts and deterministic models

- Add `src/lib/common/contracts/os/server_data_namespace_v1.spl` with fixed-layout IDs, grants, rights, states, and receipts.
- Add pure state-transition helpers for acquire/revoke/drain/recovery decisions and exhaustive specs.
- Reserve ABI slots 116–119 without changing any later ordinal; add static ABI parity tests for Simple, SDK header, and all architecture entry paths.

Gate: contract compile, invalid state transitions rejected, ABI numbers identical on x86_64/AArch64/RV64.

### Phase B — pure-Simple media and transport

- Add the pure-Simple image provisioner and verify reopen/checksum/role/UUID.
- Add serial-aware virtio discovery and transport adapters: x86 virtio PCI; ARM/RV virtio MMIO. Reject duplicate/root/read-only/no-flush candidates.
- Extend QEMU command builders with the exact second-medium options from the architecture.

Gate: byte-level image spec and transport-injected discovery specs. No live `DbFsDriver` yet.

Transport discovery model status (2026-08-22): implemented as
`server_data_virtio_probe.spl` with injected behavioral coverage.  The model is
bounded to 64 fixed scalar candidates, makes one linear visit, allocates no
secondary candidate/index collection, binds one expected target transport,
requires write plus flush support, and returns only a fixed scalar acquisition
descriptor.  Live PCI/MMIO enumeration remains deliberately unconnected until
the target owners can prove serial, role/UUID, read-only, and flush facts; this
status is not device or namespace readiness.  Image provisioning and live
target transport evidence remain open Phase-B work.

### Phase C — unique owner and mount identity

- Implement `ServerDataNamespaceOwnerV1` with one internal construction route. It receives no caller-created live driver candidate.
- Narrow the existing VFS owner to `ServerDataMountTablePortV1`; add exact mount identity and per-mount live-handle evidence instead of copying/replacing `MountTable`.
- Register DBFS device state once; prohibit public registration/unregistration for this instance.

Gate: construction count is one, driver/device escape scans are zero, copied owner/driver cannot be constructed, exact mount generation required.

### Phase D — lease/grant/syscall surface

- Implement bounded O(1) lease table (4,096 slots), at most 1,024 active operation pins, kernel entropy nonce issuance, task-generation binding, subtree canonicalization, launcher grant installation, scheduler exit revocation, and no inheritance.
- Add shared syscall handlers, copy-in/out validation, SDK types/wrappers, errno mapping, and architecture parity.
- Route web to `/srv/data/web` and DB server to `/srv/data/db`; do not grant SSHD by default.

Gate: forged/stale/cross-task/traversal/right-escalation/exhaustion tests and real service-launch grant tests.

### Phase E — commit, drain, recovery, quarantine

- Implement streaming atomic replace through the existing DBFS device commit owner, with a 16 MiB object cap, 64 KiB reusable copy-in buffer, at most 4,096 extents/4,112 journal records, data/journal/publish/checkpoint ordering, and immutable receipt.
- Implement synchronized drain/revoke/close/sync/exact-unmount with the documented non-nesting lock protocol, R1-protected active-pin predicate, epoch-tagged `drain_wait_sequence` event/condition, lost-wakeup-safe `wait_while_sequence`, acquire/release ordering, and 30-second QEMU/test drain deadline.
- Add deterministic fault injection after every write/flush boundary and verify recovery or quarantine from the same bytes.

Gate: no torn value is observable, no leaked old/new extent is live after recovery, post-revoke handle use fails, cleanup ambiguity quarantines.

### Phase F — QEMU and performance evidence

- Add two-boot persistent-image system scenarios for all three architectures, plus deterministic interrupted-commit reboot and corrupt/duplicate-media cases.
- Run 1,000 × 4 KiB, four sequential and separately atomic 16 MiB objects (64 MiB aggregate), interrupted-16-MiB recovery, and 32-lease baselines once before and once after; capture p50/p95, wall time, bytes/flushes, allocation evidence, and peak RSS. Do not describe or test the four-object workload as one atomic 64 MiB transaction.
- Run the Simple optimizer once on each touched hot-path `.spl`; fix meaningful regression or record a measured bug.

Gate: all acceptance evidence is real, architecture performance limits pass, and root filesystem non-regression remains green.

## Lane ownership

Each production file has one lane. Cross-lane edits require merge-owner approval; lanes commit independently only after their focused tests pass.

| Lane | Sole file ownership | Deliverable |
|---|---|---|
| Contract/ABI | `src/lib/common/contracts/os/server_data_namespace_v1.spl`, `src/os/kernel/types/syscall_types.spl`, `src/os/sdk/include/simpleos.h`, `src/os/libc/simpleos_*server_data*`, ABI parity specs | frozen records, ordinals, wrappers |
| Media/QEMU | `src/app/simpleos_server_data_image/**`, server-data additions in QEMU command builders/scripts, media fixture specs | reproducible distinct image and attachment |
| Transport | `src/os/services/vfs/server_data_virtio_probe.spl`, target-specific server-data virtio adapter files | serial/UUID-bound `BlockDevice` acquisition |
| VFS identity | `src/os/services/vfs/server_data_mount_table_port.spl`, narrowly reviewed additions to `vfs_boot_state.spl` and `MountTable` | exact mount/handle/drain port |
| Owner/lease | `src/os/services/vfs/server_data_namespace_owner.spl`, owner/lease unit specs | sole state owner and bounded leases |
| DBFS commit/recovery | server-data-specific additions under `src/lib/nogc_sync_mut/db/dbfs_driver/`, fault harness and DBFS recovery specs | ordered replace/recovery/quarantine |
| Syscall/grants | `src/os/kernel/ipc/syscall_server_data.spl`, dispatcher wiring, launcher/scheduler grant and revocation files | authorized user boundary |
| Service adoption | web and DB launcher/config files only | separate real subtree use |
| System/perf evidence | `test/03_system/os/qemu/simpleos_server_data_reboot_spec.spl`, generated/manual spec doc, check runner, perf fixture | multiarch reboot and measured evidence |

Lower-model sidecars: contract parity, injected transport cases, and QEMU log checker may use Codex Spark/Claude Haiku after frozen names exist. `ServerDataNamespaceOwnerV1`, DBFS commit/recovery, mount draining, syscall authorization, and final perf conclusions require normal/highest-capability implementation and review. Merge owner: SimpleOS storage/VFS owner. Final reviewer: a separate normal/highest-capability agent with no production-file ownership in these lanes.

## Review checklist

- No injected live driver/device candidate and no competing root/server medium owner.
- No raw pointer, dynamic object, driver handle, or mount ID crosses userspace.
- No lock is held while waiting on arbitrary userspace; device I/O is serialized inside the owner transaction, with checked unlock.
- Lock review proves the sole nested edge is DBFS commit-owner R2 → block queue R3. Scheduler R0, namespace R1, and MountTable R4 locks do not nest; acquire, pin, revoke, task-exit, replace, drain, and exact-unmount linearization points match the architecture.
- Drain concurrency tests force completion immediately before and after the drainer releases R1, inject spurious wakeups, reuse neither stale epoch nor stale sequence, and prove that zero is observed under R1 or the bounded wait deterministically quarantines; no wakeup may be lost.
- Boundary buffers are bounded and independently copied or streamed; move/revoke invalidation is tested.
- Syscall review proves fixed-header/path copy-in precedes admission, payload copy-in uses one reusable 64 KiB buffer, no user page survives a chunk, faults leave only unreachable pre-commit extents, and receipt copy-out failure cannot undo a committed replace.
- Unknown task generation, mount generation, access range, media identity, or durability capability fails closed.
- Algorithmic complexity is stated before allocation/layout/hoisting/dispatch changes; measurements compare identical workloads.
- All executable specs live under `test/`; `doc/06_spec` contains Markdown only.

## Verification commands (run once per acceptance criterion)

Use the admitted pure-Simple runtime only:

- `bin/simple check src/lib/common/contracts/os/server_data_namespace_v1.spl`
- `bin/simple check src/os/services/vfs/server_data_namespace_owner.spl`
- `bin/simple test test/02_integration/os/storage/server_data_namespace_owner_spec.spl`
- `bin/simple test test/02_integration/os/storage/server_data_crash_recovery_spec.spl`
- `bin/simple test test/03_system/os/qemu/simpleos_server_data_reboot_spec.spl`
- `sh scripts/audit/direct-env-runtime-guard.shs --working`
- `sh scripts/audit/direct-env-runtime-guard.shs --staged`
- `find doc/06_spec -name '*_spec.spl' | wc -l` (must be `0`)

QEMU evidence is run once as one matrix gate, not as repeatedly green per-architecture commands. If the runtime/bootstrap is unavailable, record the exact missing artifact and do not substitute the Rust seed or invent timing/RSS results.

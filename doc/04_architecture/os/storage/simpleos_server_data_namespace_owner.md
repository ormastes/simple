<!-- codex-architecture -->
# Server data namespace on a second persistent DBFS medium

**Status:** Proposed implementation contract  
**Scope:** x86_64, AArch64, and RV64 SimpleOS guests under QEMU  
**Non-goals:** replacing pure Simple with C/Rust, making DBFS the boot/root medium, or exposing a raw block device to a server

## 1. Decision

SimpleOS shall attach a distinct persistent medium for server state and mount its DBFS volume at `/srv/data`. The kernel-resident `ServerDataNamespaceOwnerV1` is the sole mutable owner of the medium's `BlockDevice`, its `DbFsDriver`, its mount identity, all issued leases, and recovery/quarantine state. Servers receive only an opaque generation-and-nonce lease plus ordinary path/file syscalls scoped below their granted subtree. They never receive a `BlockDevice`, `DbFsDriver`, `DriverInstance`, `MountTable`, driver handle, or mount identifier.

This is a second medium, not a partition or reserved LBA range on the root image. Root filesystem failure and server-data recovery therefore have separate fault domains. The same architecture-neutral owner and syscall code is used on all three architectures; only boot-time virtio discovery differs.

## 2. Existing seams and required consolidation

The implementation consumes these existing contracts rather than introducing sibling copies:

- `std.fs_driver.block_device.BlockDevice` and `BlockDeviceDurabilityPortV1` are the device/durability traits.
- `std.db.dbfs_driver.dbfs_driver.DbFsDriver` and its existing `device_commit_owner.spl` retain DBFS's internal durable commit logic.
- `std.fs_driver.mount_table.MountTable` remains the only path-to-driver and generational file/dir handle registry.
- `os.services.vfs.vfs_boot_state.spl` is the current canonical mount-table state owner. It must stop exposing copy/mutate/replace transactions for the `/srv/data` mount; `ServerDataNamespaceOwnerV1` calls a narrow mount-table port owned by that module.
- ABI 79 remains the read-only DBFS mount-capability query. It is not a lease and cannot authorize I/O.

The existing module-global DBFS device registry is a compatibility implementation detail. For the server-data instance it must have exactly one registration, created and destroyed only by `ServerDataNamespaceOwnerV1`; a copied `DbFsDriver` must not register or unregister it.

## 3. Exact shared names

The first implementation lane freezes these names before parallel coding.

### Common pointer-free contracts

File: `src/lib/common/contracts/os/server_data_namespace_v1.spl`

- `ServerDataNamespaceIdV1 { value: u64 }`
- `ServerDataLeaseIdV1 { generation: u64, nonce_hi: u64, nonce_lo: u64 }`
- `ServerDataGrantV1 { namespace_id: ServerDataNamespaceIdV1, task_id: u64, task_generation: u64, rights: u32, subtree_hash: u64 }`
- `ServerDataLeaseReceiptV1 { lease: ServerDataLeaseIdV1, grant: ServerDataGrantV1, owner_epoch: u64, state: u32 }`
- `ServerDataCommitReceiptV1 { namespace_id: ServerDataNamespaceIdV1, mount_generation: u64, durable_generation: u64, journal_lsn: u64, content_hash: u64 }`
- `ServerDataRecoveryReceiptV1 { namespace_id: ServerDataNamespaceIdV1, selected_generation: u64, replayed_records: u64, discarded_records: u64, quarantined: bool, reason_code: u32 }`
- `ServerDataNamespaceStateV1`: `Unavailable`, `Recovering`, `Mounted`, `Draining`, `Quarantined`.
- Rights: `SERVER_DATA_RIGHT_READ`, `WRITE`, `CREATE`, `REMOVE`, `RENAME`, `SYNC`, and `ATOMIC_REPLACE`; there is no mount, raw-device, grant-delegation, or arbitrary-path right.

All records are scalar/fixed-layout. Paths and payloads cross the syscall boundary as bounded copied byte spans and are validated before allocation. A lease is an unforgeable kernel lookup key, not self-authenticating proof.

### Kernel owner and ports

Files:

- `src/os/services/vfs/server_data_namespace_owner.spl`: `ServerDataNamespaceOwnerV1`
- `src/os/services/vfs/server_data_mount_table_port.spl`: `ServerDataMountTablePortV1`
- `src/os/services/vfs/server_data_virtio_probe.spl`: `ServerDataVirtioProbeV1`

Owner entrypoints:

- `server_data_namespace_boot_v1()`
- `server_data_namespace_acquire_v1(task_id, task_generation, grant_request)`
- `server_data_namespace_revoke_v1(caller, lease)`
- `server_data_namespace_atomic_replace_v1(caller, lease, relative_path, bytes)`
- `server_data_namespace_sync_v1(caller, lease)`
- `server_data_namespace_unmount_v1(caller)`
- `server_data_namespace_status_v1(caller)`

The owner contains the only live `BlockDevice`, `DbFsDriver`, `MountId`, mount epoch, lease table, journal transaction state, and quarantine bit. The port exposes only `mount_unique`, `begin_drain`, `live_handle_count`, `close_task_handles`, and `unmount_exact`; it never returns `MountTable` or `DriverInstance`.

## 4. Media provisioning and QEMU attachment

The canonical provisioning app is pure Simple:

`src/app/simpleos_server_data_image/main.spl`

It creates a fixed-size sparse-safe raw image, writes both DBFS superblock/checkpoint replicas through the same DBFS formatter used by production, flushes, reopens, and validates UUID, sector size, block count, empty-root generation, and checksum. Default size is 256 MiB; tests may use 32 MiB. Image identity includes a random 128-bit volume UUID and the fixed role string `simpleos-server-data-v1`. Reusing a root image, a zero UUID, or a role mismatch fails closed.

The QEMU command builders attach the root image first and server data second, with stable serial `simpleos-server-data-v1`:

| Guest | Machine | Data attachment |
|---|---|---|
| x86_64 | `q35` | `-drive if=none,id=sosdata,format=raw,file=... -device virtio-blk-pci,drive=sosdata,serial=simpleos-server-data-v1` |
| AArch64 | `virt` | `-drive if=none,id=sosdata,format=raw,file=... -device virtio-blk-device,drive=sosdata,serial=simpleos-server-data-v1` |
| RV64 | `virt` | `-drive if=none,id=sosdata,format=raw,file=... -device virtio-blk-device,drive=sosdata,serial=simpleos-server-data-v1` |

Discovery matches the virtio serial/role and DBFS UUID, never “second probe result” alone. Duplicate matches, a boot-volume UUID match, read-only media when write access is requested, unsupported sector size, or missing flush support prevent the mount. x86 PCI transport and ARM/RV MMIO transports each return the same `BlockDevice` contract to the owner.

## 5. Ownership and lease state machine

Execution domains are explicit:

| State/data | Canonical owner | Boundary class |
|---|---|---|
| virtio queue, `BlockDevice`, `DbFsDriver` | `ServerDataNamespaceOwnerV1` | never crosses |
| `MountTable` and virtual handles | VFS boot-state module | narrow synchronous port |
| namespace lease | owner lease table | opaque lease ID copied to task |
| request path/data | calling task | bounded copy into owner transaction |
| commit/recovery receipt | owner | frozen copied scalar receipt |

The lease lookup key is `(task_id, task_generation, owner_epoch, nonce_hi, nonce_lo)`. Both nonce words come from kernel entropy after boot entropy admission and are nonzero; generation and nonce exhaustion fail closed. A PID alone is never an identity because task IDs may be reused. A lease is bound to one canonical subtree and cannot be transferred or delegated.

Resource bounds are part of the security contract:

- at most 4,096 live or terminal-uncollected lease slots per namespace epoch;
- at most 1,024 concurrently pinned namespace operations, and at most one replace commit at a time;
- at most 4,096 data extents and 4,112 journal records for one 16 MiB replace transaction;
- 4,096-byte canonical relative paths, 64 KiB syscall streaming chunks, and 1 MiB maximum recovery scratch;
- 30 seconds from entering `Draining` to active-operation quiescence under QEMU/system-test policy (production may configure a shorter deadline, never an unbounded wait).

Capacity exhaustion returns `EBUSY`, `ENOSPC`, `E2BIG`, or enters quarantine where ownership is ambiguous; arrays and replay tables never grow past these caps.

State transitions:

```text
Unavailable -> Recovering -> Mounted -> Draining -> Unavailable
                      |          |          |
                      +----------+----------+-> Quarantined
```

`acquire` is admitted only in `Mounted`. Every operation revalidates task ID, task generation, owner epoch, nonce, rights, and canonical subtree before opening a VFS handle. On task exit, the scheduler sends one generation-bound revocation command; stale exit notifications cannot revoke a later task generation.

Unmount is synchronized: atomically enter `Draining`, reject new acquisition and I/O, revoke leases, close that generation's task-owned handles, wait for the bounded active-operation count to reach zero, sync DBFS, verify `MountTable` has no handles for the exact mount identity, then `unmount_exact(mount_id, mount_generation)`. A timeout or close/sync/unlock failure enters `Quarantined`; it never copies or replaces the table to escape live handles.

### Lock hierarchy and linearization

Locks are ranked only where nesting is unavoidable:

```text
R0 Scheduler task table (snapshot task generation, then release)
R1 ServerDataNamespaceOwnerV1 state/lease/op-pin mutex
R2 DBFS device commit-owner mutex
R3 BlockDevice queue lock
R4 VFS MountTable owner mutex
```

The only permitted nested edge is `R2 -> R3`, internal to a DBFS device transaction. `R0`, `R1`, and `R4` are never held while acquiring another ranked lock. In particular, no namespace-owner lock is held during block I/O, user copying, quiescence waits, or MountTable calls, and `R2` and `R4` are never held together. Checked unlock failure at any rank makes the affected authority indeterminate and quarantines it.

- **Acquire:** snapshot `(task_id, task_generation)` under R0 and release R0; under R1 revalidate owner epoch/state/grant, allocate the bounded lease slot and nonce, and publish the slot. Publication under R1 is the acquire linearization point.
- **Operation pin:** copy fixed request header and path before R1; under R1 validate task generation, epoch, nonce, rights, subtree, state, and capacity, then increment the exact lease and namespace active counts. The increment is the admission linearization point. R1 is released before payload streaming or DBFS work. Completion reacquires R1 only to publish the terminal receipt and decrement both counts. If the namespace count becomes zero while `Draining`, completion increments the epoch-owned `drain_wait_sequence` under R1, publishes that increment with release ordering, releases R1, and signals the generation-tagged drain event.
- **Explicit revoke:** under R1 mark the exact lease terminal and reject future pins. That mark is the revoke linearization point. Already-pinned operations may finish; revoke never frees their slot until their pin count reaches zero.
- **Task exit:** snapshot the exiting task identity under R0 and release it; under R1 mark all leases matching both task ID and task generation terminal in one bounded scan. The R1 batch mark is the task-exit linearization point. A stale generation changes nothing.
- **Replace:** after the operation pin, acquire R2, stream/copy data into fresh extents and durably append the journal commit, then publish the new DBFS namespace generation while still under R2. That root/generation publication is the replace linearization point. Release R2 before reacquiring R1 to record the receipt and release the pin.
- **Drain/unmount:** under R1 change `Mounted -> Draining`, revoke every lease, and snapshot the exact mount identity; the state transition is the drain linearization point. Quiescence uses an R1-protected predicate plus a generation-tagged event/condition, never polling an unsynchronized scalar. Each loop acquires R1 with acquire ordering, verifies the same owner epoch and `Draining` state, and reads `active_operation_count`. Zero observed under R1 is the quiescence linearization point. Otherwise the drainer snapshots `drain_wait_sequence`, releases R1, and performs a deadline-bounded `wait_while_sequence(owner_epoch, observed_sequence)`. That primitive registers/checks the epoch and sequence atomically with sleeping and returns immediately if a completion already advanced the sequence, preventing a lost wakeup between unlock and block; spurious wakeups simply repeat the predicate loop. Pin completion decrements under R1 and, on transition to zero, release-publishes a sequence increment before signaling. Epoch mismatch, sequence exhaustion, event failure, or the 30-second deadline quarantines. After quiescence, run DBFS sync under R2 and release it; call close/check/unmount under R4 and release it; finally under R1 publish `Unavailable` and increment owner epoch. Exact unmount under R4 is the external namespace-removal linearization point. Any failed phase publishes `Quarantined` under R1 instead.

## 6. Atomic journal replace and crash behavior

`server_data_namespace_atomic_replace_v1` is the only server-facing whole-object commit primitive. It accepts one canonical relative path and at most 16 MiB of data. The kernel:

1. Copies and validates request metadata once; canonicalizes the path once and verifies the subtree prefix.
2. Streams the payload into fresh DBFS extents while computing its content hash; it does not form a second whole-payload array.
3. Appends a bounded journal intent containing old/new inode generations, target path hash, extent list, byte count, and content hash.
4. Flushes data then journal/commit using `BlockDeviceDurabilityPortV1`.
5. Atomically publishes the namespace root/generation through DBFS's existing commit owner.
6. Flushes the checkpoint, retires old extents after publication, and returns `ServerDataCommitReceiptV1`.

The syscall does not copy 16 MiB into a kernel array. It first copies a fixed-size scalar header, validates integer addition/ranges, copies at most 4,096 path bytes plus one terminator into owner scratch, canonicalizes once, and admits an operation pin. It then walks the caller range in at most 64 KiB chunks. For each chunk it validates that exact user range, copies once into a reusable fixed-capacity kernel buffer, updates the streaming content hash, and writes fresh DBFS extents before reusing the buffer. User pages are not retained, shared, or trusted after each copy. A copy fault aborts before journal commit; already-written fresh extents remain unreachable and are reclaimed by recovery. The fixed receipt is copied out only after durable publication; copy-out failure does not roll back an already committed replace, and status lookup by lease exposes its terminal receipt.

The 4,096-extent bound assumes the minimum admitted 4 KiB extent size. The journal reserves at most one intent row per extent plus 16 transaction/root/checkpoint rows, hence 4,112 records. Recovery uses streaming journal validation with at most 1 MiB total scratch, including two 64 KiB I/O buffers, page/checksum state, and bounded extent/replay indices; media requiring more index state is quarantined rather than allocated without bound.

Recovery selects the newest checksum-valid superblock/checkpoint pair, replays only complete committed records, discards uncommitted fresh extents, verifies monotonic generations and extent bounds, and publishes one `ServerDataRecoveryReceiptV1`. Any checksum-valid but contradictory roots, generation regression, out-of-range extent, duplicate volume identity, failed flush, or owner-unlock ambiguity quarantines the namespace read/write. Quarantine permits privileged status/evidence reads only; there is no automatic reformat or fallback to the root disk.

## 7. User syscall ABI and authorization

Reserve ABI ordinals 116–119 by renaming the existing reserved enum slots without renumbering later syscalls:

- 116 `ServerDataAcquire`: copied request `(subtree_ptr, subtree_len, rights)`; returns a lease into a caller-provided fixed receipt buffer.
- 117 `ServerDataRevoke`: `(generation, nonce_hi, nonce_lo)`; idempotent only for the same terminal lease.
- 118 `ServerDataStatusSync`: operation selector `STATUS` or `SYNC`, lease words, fixed output receipt pointer/length.
- 119 `ServerDataAtomicReplace`: lease words plus pointer/length pairs for canonical relative path and data.

`simpleos.h` exposes `simpleos_server_data_*_v1` wrappers with fixed-width C-layout receipt structs. Architecture entry stubs do not interpret the payload; the shared syscall dispatcher performs copy-in/copy-out and routes to the same owner. Negative returns use existing errno mapping: `EINVAL`, `EACCES`, `ESTALE`, `EBUSY`, `EIO`, `EROFS`, `ENOSPC`, `E2BIG`.

Acquisition additionally requires a nondelegable kernel `ServerDataNamespaceGrantV1` installed by the service launcher. Grant policy binds package identity, executable admission digest, task generation, subtree, and rights. Web gets `/srv/data/web`; DB server gets `/srv/data/db`; SSHD gets no server-data grant unless an explicit subsystem requires it. Child processes inherit nothing by default. `CAP_RIGHT_WRITE` or device grants do not imply this grant.

## 8. Performance and memory contract

Complexity is assessed before micro-optimization:

- Lease lookup must be expected O(1) with a bounded open-addressed table, not a linear scan of all tasks.
- Mount resolution remains O(number of mounts) in v1 but path canonicalization occurs once per request; the owner caches exact `/srv/data` mount identity, never a mutable driver copy.
- Atomic replace is O(payload bytes + changed DBFS pages), with one payload read and no quadratic concatenation; one call/object is capped at 16 MiB.
- Recovery is O(journal bytes + live extent records), with streaming validation and bounded page buffers rather than retaining the journal.
- Active operations, leases, journal records, path length (4096), replace payload (16 MiB), and recovery scratch memory are all bounded. Queue/request descriptors use structure-of-arrays only if measured scans justify it; opaque ABI layouts remain fixed.
- Hot loops hoist lease identity, rights, mount identity, sector size, and extent bounds. Trait dispatch occurs per extent batch, not per byte or sector where the block interface supports batching.

Acceptance captures the same workload before/after: 1,000 4 KiB replaces plus sync; four separately named 16 MiB objects written sequentially (64 MiB aggregate, each independently atomic, with no cross-object transaction claim); cold recovery after an injected interrupted 16 MiB commit; and 32 concurrent service leases. Record wall time, p50/p95 request latency, bytes read/written, flush count, allocation count/bytes where supported, and peak RSS. No regression over the pre-owner DBFS path above 5% is accepted unless tied to the security boundary with evidence; peak RSS during the 64 MiB aggregate/four-object workload must remain below baseline + 4 MiB and must not scale with aggregate bytes. Run the Simple optimizer on every touched `.spl` hot-path file, preserving API and receipts.

## 9. Required evidence

Correctness specs use real backing bytes and fail-fast placeholders until implemented. Shared manual step names are frozen as:

- `step("provision second DBFS medium")`
- `step("boot with root and server-data media")`
- `step("acquire generation-bound server lease")`
- `step("replace and sync server state")`
- `step("inject crash before commit publication")`
- `step("reboot the same server-data image")`
- `step("reject stale lease and verify recovered bytes")`

Unit/integration evidence covers forged/stale/cross-task leases, traversal and alias paths, rights, nonce/generation exhaustion, duplicate media, live-handle unmount, every write/flush crash boundary, corrupt replicas, quarantine, and exact one-owner registration. QEMU boots each architecture twice against the same server-data image and proves: first boot writes `hello-from-<arch>` through the user syscall; the VM is terminated at a deterministic journal boundary; second boot reports recovery and reads either the prior committed value or the new fully committed value, never torn/empty bytes. Host-side image inspection is supporting evidence only; in-guest readback is mandatory.

## 10. Consequences

### Positive

- One physical and logical authority prevents copied value-semantic drivers from becoming competing storage owners.
- Separate media makes server persistence and crash recovery independently testable across all target architectures.
- Server processes gain least-authority filesystem access without raw device or mount authority.

### Negative

- Four new ABI calls and coordinated scheduler/VFS/DBFS work are required.
- Draining may block unmount until bounded operations finish; indeterminate cleanup quarantines rather than attempting recovery in place.

### Neutral

- Existing root NVFS/FAT32/DBFS boot behavior remains unchanged.
- The first version supports whole-object atomic replacement; general multi-file transactions remain kernel-private.

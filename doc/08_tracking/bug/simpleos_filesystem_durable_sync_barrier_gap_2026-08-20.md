# SimpleOS filesystem durable-sync barrier gap

- Severity: P1 release blocker (REQ-4, REQ-5)
- Owner: block-device/VFS durability owner
- Final reviewer: SimpleOS hardening merge owner
- Status: PARTIAL — portable FAT32/NVFS recovery slice implemented; mounted
  NVFS/NVFS-POSIX and admitted hardware evidence remain open

## Evidence

`src/lib/nogc_async_mut/fs_driver/mount_table.spl` gates `fsync` and
`fdatasync` on `Capability.DurableSync`. RamFS, FAT32, NVFS, and NVFS-POSIX
remain fail-closed because their current write/WAL paths do not prove a device
cache flush, FUA ordering, or crash-stable commit. An in-memory WAL LSN or flush
counter is not durable evidence.

The DBFS device-backed slice is implemented. `device_commit_owner.spl` owns the
stored `BlockDevice`, append cursor, blob bindings, two bounded namespace slots,
pending generation, and last acknowledged generation. File data is appended on
fresh sector boundaries; each namespace entry binds its blob checksum. A
pending generation overwrites only the non-durable slot until `BlockDevice.flush`
returns `Ok(true)`, after which it becomes the new durable slot. Recovery checks
slot and blob integrity and falls back to the older valid generation. Hosted
DBFS and a device whose default `flush` reports unavailable still fail closed.
All DBFS device-owner mutation and recovery reads are serialized by one
runtime-backed raw mutex on audited hosted targets. Mount registration fails closed if lock creation or
acquisition is unavailable, and no transition result is published unless the
unlock outcome is successful. Driver values retain only instance identity and
never copy the lock or durability authority. The compact mount no longer
registers a parallel `RawNvmeArena` owner; passthrough appends consume the same
locked append cursor as file blobs.

SimpleOS is explicitly not admitted by this mutex. The facade reaches
`spl_mutex_*`; hosted `runtime_thread.c` provides pthread/critical-section
exclusion, but `src/os/kernel/net/thread_shim.spl` and x86 SimpleOS
`boot/primitives.c` are unconditional-success/no-op stubs. DBFS checks the
canonical platform before lock acquisition, returns `FsError.Unsupported` from
registration, and exposes
`missing-simpleos-atomic-compare-exchange-or-scheduler-exclusion` as its
machine-readable blocker. A positive stub handle is never durability evidence.

Mount dispatch is extracted into `mount_driver_dispatch.spl`. DBFS is split
into `dbfs_driver.spl`, `namespace_io.spl`, and `device_commit_owner.spl`; every
file is below 800 lines and only the commit owner stores device durability state.

## Unblock condition

Complete the same real-owner flush/FUA and fault/remount matrix for FAT32, NVFS,
and NVFS-POSIX, then run the admitted self-hosted integration and mission gate.
DBFS's focused matrix is `dbfs_durable_commit_spec.spl`; it covers acknowledged
reboot reconstruction, unavailable/failed flush, a torn higher generation,
total checkpoint corruption, interleaved two-device transition isolation, and
the bounded 64-entry compact checkpoint.

## 2026-08-20 FAT32/NVFS recovery update

- `block_device_owner.spl` is now the single process-local owner used by both
  NVFS arena and superblock I/O; the former duplicate trait-object registries
  were removed. A successful write is never treated as a flush.
- The NVFS arena header now uses two checksum-valid sequence slots. `fsync`
  orders data flush, header publication, and metadata flush; restart recovery
  selects the highest valid sequence, falls back after a torn latest slot,
  rejects corrupt/capacity-incompatible records, and refuses sequence wrap.
- NVFS superblock replicas are each barrier-published and checksum-validated;
  one corrupt replica reconstructs from its peer and two corrupt replicas fail
  closed.
- FAT32 is split into core, directory, file-operation, and owned-I/O modules,
  all below 800 lines. Its file handles are generation-stamped and bounded to
  65,536 slots. A mounted FAT32 driver advertises `DurableSync` only after its
  concrete device acknowledges a flush, then routes fsync/fdatasync through
  dirty-cluster writeback plus another acknowledged flush.
- Native/example NVFS and NVFS-POSIX no-op sync paths now return
  `FsError.Unsupported`; their handle/refcount allocators reject exhaustion.
- Behavioral evidence is defined in
  `test/02_integration/storage/fs_recovery_conformance_spec.spl`, with FAT32,
  NVFS, and NVFS-POSIX success/failure rows and no source-text oracle.

This does not promote the mounted stdlib `NvfsDriver` or `NvfsPosixDriver` to
`DurableSync`: their file namespace/write paths are not yet bound to the
recoverable arena commit owner. That wiring and admitted self-hosted/QEMU or
physical power-cut execution remain the release blocker.

## Residual evidence blockers

- The current admitted Stage 2 compiler may compile/native-build only and may
  not run SSpec, so the focused behavioral matrix still needs an admitted
  self-hosted test-runner execution.
- Hardware acceptance still needs the generation-bound NVMe adapter to pass its
  reset/I/O serialization gate, followed by a real controller flush and
  physical/QEMU power-cut remount campaign.
- The compact driver's module stores are a single serialized VFS execution
  domain. Concurrent cross-thread filesystem entry remains unsupported until a
  canonical synchronized command ingress owns these arrays.

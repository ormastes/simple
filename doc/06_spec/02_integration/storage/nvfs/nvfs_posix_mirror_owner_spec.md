# nvfs posix mirror owner spec

Status: **2/2 PASS — non-admitting host-memory diagnostic, cycle one**. Retained historical seed only; no current Phase1, self-hosted, native, VM, hardware, or release qualification.

Source: `test/02_integration/storage/nvfs/nvfs_posix_mirror_owner_spec.spl`

Source SHA-256: `c9cee2dc793fef7238dc17964921ff3d499af9660dfc37df47d29b86d4eed96d`

Requirement: `REQ-NVFS-MOUNT-ISOLATION` — each mounted provider owns its namespace, bytes, and explicit backing device. Hosted creation is not remount persistence.

## Acceptance scenarios

- does not mirror hosted writes into a registered unrelated device.
- does not let an undersized ambient device fail an explicit owned-device write.

## Evidence boundaries

The actual DBFS owner, NVFS operation leases, and explicit `MemBlockDevice` backing are exercised by these authored assertions. They are not mocked persistence. Memory-backed block I/O is not physical NVMe, crash recovery, or Windows/Linux/BSD qualification. The frozen source passed the host-only diagnostic described below. Authored UNRUN comments in its exact source are preserved as part of the tested snapshot.

## Diagnostic evidence

- Inputs: `build/phase-one-storage-gui-diagnostic/nvfs-isolation-host-cycle-one-inputs.sdn` (345 input hashes matched before/after).
- Log: `build/phase-one-storage-gui-diagnostic/nvfs_posix_mirror_owner_spec/cycle-one.log`; 1715 ms; peak observed process-tree RSS 397356 KiB; exit 0; quiescent 1.
- Producer SHA-256: `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`.
- Actual status: `build/phase-one-storage-gui-diagnostic/nvfs-isolation-host-cycle-one-status.sdn`. No rerun or hardware action.

## Executable source

```simple
"""NVFS ordinary writes never acquire an ambient block-device mirror; UNRUN."""
# @req REQ-NVFS-MOUNT-ISOLATION
# @manual: primary
use std.spec.*
use std.spec.step
use std.fs_driver.types.{Path, OpenFlags}
use std.fs_driver.nvfs_posix_driver.{NvfsPosixDriver}
use std.fs_driver.nvfs_arena.{nvfs_arena_set_block_device}
use std.fs_driver.mem_block_device.{MemBlockDevice}
use std.fs_driver.block_device.{BlockDevice}

var _ambient_write_attempts: i64 = 0

struct ObservedAmbientDevice:
    inner: MemBlockDevice

impl BlockDevice for ObservedAmbientDevice:
    fn read_sector(lba: u64) -> Result<[u8], text>:
        self.inner.read_sector(lba)

    me fn write_sector(lba: u64, data: [u8]) -> Result<bool, text>:
        _ambient_write_attempts = _ambient_write_attempts + 1
        var owned = self.inner
        val result = owned.write_sector(lba, data)
        self.inner = owned
        result

    fn sector_size() -> u32: self.inner.sector_size()
    fn sector_count() -> u64: self.inner.sector_count()
    fn mirror_identity() -> u64: self.inner.mirror_identity()

fn write_ambient_isolation_fixture(driver: NvfsPosixDriver):
    val path = Path(raw: "/ambient-independent.bin")
    val handle = driver.open(path, OpenFlags.read_write().with_create()).unwrap()
    expect(driver.pwrite(handle, 0, [9u8, 0u8, 255u8]).unwrap()).to_equal(3)
    expect(driver.pread_bytes_handle(handle, 0, 8).unwrap()).to_equal([9u8, 0u8, 255u8])
    driver.close(handle).unwrap()

describe "NVFS rejects ambient device authority":
    it "does not mirror hosted writes into a registered unrelated device":
        step("Register a writable ambient device and write a hosted file")
        val device = ObservedAmbientDevice(inner: MemBlockDevice.new(256u64, 512u32))
        nvfs_arena_set_block_device(device)
        _ambient_write_attempts = 0
        write_ambient_isolation_fixture(NvfsPosixDriver.new("ambient-hosted"))
        expect(_ambient_write_attempts).to_equal(0)

    it "does not let an undersized ambient device fail an explicit owned-device write":
        step("The selected device remains authoritative despite an unusable mirror")
        val ambient = ObservedAmbientDevice(inner: MemBlockDevice.new(1u64, 512u32))
        nvfs_arena_set_block_device(ambient)
        _ambient_write_attempts = 0
        var driver = NvfsPosixDriver.new_on_owned_device(
            "ambient-explicit", MemBlockDevice.new(1024u64, 512u32), 760004u64, 0, 1024).unwrap()
        write_ambient_isolation_fixture(driver)
        expect(driver.close_owned_device().unwrap()).to_equal(true)
        expect(_ambient_write_attempts).to_equal(0)
```

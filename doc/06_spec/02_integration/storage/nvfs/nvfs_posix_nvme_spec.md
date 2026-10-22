# nvfs posix nvme spec

Status: **2/2 PASS — non-admitting host-memory diagnostic, cycle one**. Retained historical seed only; no current Phase1, self-hosted, native, VM, hardware, or release qualification.

Source: `test/02_integration/storage/nvfs/nvfs_posix_nvme_spec.spl`

Source SHA-256: `9b4e493f2535d375d50a8db642e4bc3daf9e7b0b9e6bf5461c7cd1c97a42b0a3`

Requirement: `REQ-NVFS-MOUNT-ISOLATION` — each mounted provider owns its namespace, bytes, and explicit backing device. Hosted creation is not remount persistence.

## Acceptance scenarios

- keeps equal paths on two owned devices independent.
- does not resurrect an unlinked path after a retained handle is written.

## Evidence boundaries

The actual DBFS owner, NVFS operation leases, and explicit `MemBlockDevice` backing are exercised by these authored assertions. They are not mocked persistence. Memory-backed block I/O is not physical NVMe, crash recovery, or Windows/Linux/BSD qualification. The frozen source passed the host-only diagnostic described below. Authored UNRUN comments in its exact source are preserved as part of the tested snapshot.

## Diagnostic evidence

- Inputs: `build/phase-one-storage-gui-diagnostic/nvfs-isolation-host-cycle-one-inputs.sdn` (345 input hashes matched before/after).
- Log: `build/phase-one-storage-gui-diagnostic/nvfs_posix_nvme_spec/cycle-one.log`; 2321 ms; peak observed process-tree RSS 407632 KiB; exit 0; quiescent 1.
- Producer SHA-256: `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`.
- Actual status: `build/phase-one-storage-gui-diagnostic/nvfs-isolation-host-cycle-one-status.sdn`. No rerun or hardware action.

## Executable source

```simple
"""Explicit block-device NVFS persistence contracts; UNRUN.

The legacy filename is retained. MemBlockDevice exercises the same explicit
BlockDevice boundary; these cases make no hardware NVMe qualification claim.
"""
# @req REQ-NVFS-MOUNT-ISOLATION
# @manual: primary
use std.spec.*
use std.spec.step
use std.fs_driver.types.{Path, OpenFlags}
use std.fs_driver.nvfs_posix_driver.{NvfsPosixDriver}
use std.fs_driver.mem_block_device.{MemBlockDevice}
use std.fs_driver.error.{FsError}

describe "NVFS explicit block-device ownership":
    it "keeps equal paths on two owned devices independent":
        step("Open two distinct device owners with the same file path")
        val dev_a = MemBlockDevice.new(1024u64, 512u32)
        val dev_b = MemBlockDevice.new(1024u64, 512u32)
        var first = NvfsPosixDriver.new_on_owned_device(
            "device-a", dev_a, 760002u64, 0, 1024).unwrap()
        var second = NvfsPosixDriver.new_on_owned_device(
            "device-b", dev_b, 760003u64, 0, 1024).unwrap()
        val path = Path(raw: "/same.bin")
        val a = first.open(path, OpenFlags.read_write().with_create()).unwrap()
        first.pwrite(a, 0, [1u8, 0u8, 255u8]).unwrap()
        expect(second.stat(path).unwrap_err()).to_equal(FsError.NotFound)
        val b = second.open(path, OpenFlags.read_write().with_create()).unwrap()
        second.pwrite(b, 0, [2u8, 128u8]).unwrap()
        first.fsync(a).unwrap()
        second.fsync(b).unwrap()
        expect(first.pread_bytes_handle(a, 0, 8).unwrap()).to_equal([1u8, 0u8, 255u8])
        expect(second.pread_bytes_handle(b, 0, 8).unwrap()).to_equal([2u8, 128u8])
        first.close(a).unwrap()
        second.close(b).unwrap()
        first.close_owned_device().unwrap()
        second.close_owned_device().unwrap()
        step("Reopen both actual devices and recover each independent payload")
        var reopened_a = NvfsPosixDriver.new_on_owned_device(
            "device-a-reopened", dev_a, 760002u64, 0, 1024).unwrap()
        var reopened_b = NvfsPosixDriver.new_on_owned_device(
            "device-b-reopened", dev_b, 760003u64, 0, 1024).unwrap()
        val read_a = reopened_a.open(path, OpenFlags.read_only()).unwrap()
        val read_b = reopened_b.open(path, OpenFlags.read_only()).unwrap()
        expect(reopened_a.pread_bytes_handle(read_a, 0, 8).unwrap()).to_equal([1u8, 0u8, 255u8])
        expect(reopened_b.pread_bytes_handle(read_b, 0, 8).unwrap()).to_equal([2u8, 128u8])
        reopened_a.close(read_a).unwrap()
        reopened_b.close(read_b).unwrap()
        reopened_a.close_owned_device().unwrap()
        reopened_b.close_owned_device().unwrap()

    it "does not resurrect an unlinked path after a retained handle is written":
        step("Unlink while retaining the inode through its open handle")
        var driver = NvfsPosixDriver.new("unlink-owner")
        val path = Path(raw: "/unlinked.bin")
        val handle = driver.open(path, OpenFlags.read_write().with_create()).unwrap()
        driver.pwrite(handle, 0, [3u8, 4u8]).unwrap()
        driver.unlink(path).unwrap()
        expect(driver.pwrite(handle, 0, [5u8]).unwrap()).to_equal(1)
        expect(driver.pread_bytes_handle(handle, 0, 8).unwrap()).to_equal([5u8, 4u8])
        expect(driver.stat(path).unwrap_err()).to_equal(FsError.NotFound)
        driver.close(handle).unwrap()
        expect(driver.open(path, OpenFlags.read_only()).unwrap_err()).to_equal(FsError.NotFound)
```

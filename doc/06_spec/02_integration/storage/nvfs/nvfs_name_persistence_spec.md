# nvfs name persistence spec

Status: **2/2 PASS — non-admitting host-memory diagnostic, cycle one**. Retained historical seed only; no current Phase1, self-hosted, native, VM, hardware, or release qualification.

Source: `test/02_integration/storage/nvfs/nvfs_name_persistence_spec.spl`

Source SHA-256: `297da55ebb90415e47efe9a0ae093bbe420ba2d765b1f19bd0c2796a985aae5d`

Requirement: `REQ-NVFS-MOUNT-ISOLATION` — each mounted provider owns its namespace, bytes, and explicit backing device. Hosted creation is not remount persistence.

## Acceptance scenarios

- recovers names and bytes after closing and reopening the same owned device.
- does not expose names from an independent hosted instance.

## Evidence boundaries

The actual DBFS owner, NVFS operation leases, and explicit `MemBlockDevice` backing are exercised by these authored assertions. They are not mocked persistence. Memory-backed block I/O is not physical NVMe, crash recovery, or Windows/Linux/BSD qualification. The frozen source passed the host-only diagnostic described below. Authored UNRUN comments in its exact source are preserved as part of the tested snapshot.

## Diagnostic evidence

- Inputs: `build/phase-one-storage-gui-diagnostic/nvfs-isolation-host-cycle-one-inputs.sdn` (345 input hashes matched before/after).
- Log: `build/phase-one-storage-gui-diagnostic/nvfs_name_persistence_spec/cycle-one.log`; 2012 ms; peak observed process-tree RSS 389484 KiB; exit 0; quiescent 1.
- Producer SHA-256: `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`.
- Actual status: `build/phase-one-storage-gui-diagnostic/nvfs-isolation-host-cycle-one-status.sdn`. No rerun or hardware action.

## Executable source

```simple
"""NVFS names persist only through their explicitly selected backing device.

UNRUN source acceptance. Hosted constructors create independent namespaces;
they do not simulate remount by importing process-global path records.
"""
# @req REQ-NVFS-MOUNT-ISOLATION
# @manual: primary
use std.spec.*
use std.spec.step
use std.fs_driver.types.{Path, OpenFlags}
use std.fs_driver.nvfs_posix_driver.{NvfsPosixDriver}
use std.fs_driver.mem_block_device.{MemBlockDevice}
use std.fs_driver.error.{FsError}

describe "NVFS names belong to the selected backing":
    it "recovers names and bytes after closing and reopening the same owned device":
        step("Write and synchronize one exact owned device")
        val dev = MemBlockDevice.new(1024u64, 512u32)
        var first = NvfsPosixDriver.new_on_owned_device(
            "name-first", dev, 760001u64, 0, 1024).unwrap()
        val path = Path(raw: "/data.bin")
        val handle = first.open(path, OpenFlags.read_write().with_create()).unwrap()
        expect(first.pwrite(handle, 0, [0x00u8, 0xabu8, 0xffu8]).unwrap()).to_equal(3)
        first.fsync(handle).unwrap()
        first.close(handle).unwrap()
        expect(first.close_owned_device().unwrap()).to_equal(true)
        step("Reopen the same device without any process path mirror")
        var second = NvfsPosixDriver.new_on_owned_device(
            "name-second", dev, 760001u64, 0, 1024).unwrap()
        expect(second.stat(path).unwrap().size).to_equal(3)
        val reopened = second.open(path, OpenFlags.read_only()).unwrap()
        expect(second.pread_bytes_handle(reopened, 0, 8).unwrap()).to_equal([0x00u8, 0xabu8, 0xffu8])
        second.close(reopened).unwrap()
        expect(second.close_owned_device().unwrap()).to_equal(true)

    it "does not expose names from an independent hosted instance":
        step("Create a file in one hosted namespace")
        var first = NvfsPosixDriver.new("name-hosted-first")
        val path = Path(raw: "/private.bin")
        val handle = first.open(path, OpenFlags.read_write().with_create()).unwrap()
        first.pwrite(handle, 0, [0xabu8]).unwrap()
        first.close(handle).unwrap()
        step("The same path in a separate namespace must stay absent")
        var second = NvfsPosixDriver.new("name-hosted-second")
        expect(second.stat(path).unwrap_err()).to_equal(FsError.NotFound)
        expect(second.open(path, OpenFlags.read_only()).unwrap_err()).to_equal(FsError.NotFound)
```

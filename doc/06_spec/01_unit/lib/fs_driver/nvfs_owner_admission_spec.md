# NVFS owner admission specification

Status: **4/4 PASS — non-admitting host-memory diagnostic, cycle one**. Retained historical seed only; no current Phase1, self-hosted, native, VM, hardware, or release qualification.

Source: `test/01_unit/lib/fs_driver/nvfs_owner_admission_spec.spl`

Source SHA-256: `48d9cf1061aec499bdd46f72b1f5644362f4a85854d7328aeceb88995a5ff596`

Requirements: `REQ-NVFS-MOUNT-ISOLATION`, `REQ-NVFS-BOUNDED-ADMISSION`. NVFS passes 65,536 limits to the same DBFS owner method exercised here with small limits. All counts and open mutations share the existing namespace transaction; there is no second registry.

## Acceptance scenarios

- rejects a new file at capacity while preserving existing-open semantics.
- rejects before truncation or creation and admits again after close.
- counts only this owner's visible files and live file descriptors.
- rejects invalid or zero admission without creating a namespace entry.

## Evidence boundaries

Assertions use real hosted DBFS inodes, descriptors, bytes, and errors. The four cases passed this host-only diagnostic; the authored UNRUN comment in the exact source remains unchanged. Static source review cannot establish concurrency execution, hardware persistence, or OS boot behavior. No QEMU, guest, or hardware-NVMe check may be inferred from these fixtures.

## Diagnostic evidence

- Inputs: `build/phase-one-storage-gui-diagnostic/nvfs-isolation-host-cycle-one-inputs.sdn` (345 input hashes matched before/after).
- Log: `build/phase-one-storage-gui-diagnostic/nvfs_owner_admission_spec/cycle-one.log`; 253 ms; peak observed process-tree RSS 256300 KiB; exit 0; quiescent 1.
- Producer SHA-256: `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`.
- Actual status: `build/phase-one-storage-gui-diagnostic/nvfs-isolation-host-cycle-one-status.sdn`. No rerun or hardware action.

## Executable source

```simple
"""NVFS admission policy enforced by the actual DBFS namespace owner; UNRUN.

Small explicit limits exercise the same owner method used with 65,536 limits
by NvfsPosixDriver.open_path. No shadow registry or large allocation loop.
"""
# @req REQ-NVFS-MOUNT-ISOLATION
# @req REQ-NVFS-BOUNDED-ADMISSION
# @manual: primary
use std.spec.*
use std.spec.step
use std.db.dbfs_driver.{DbFsDriver}
use std.fs_driver.types.{Path, OpenFlags}
use std.fs_driver.error.{FsError}

describe "NVFS admission uses the locked inner namespace":
    it "rejects a new file at capacity while preserving existing-open semantics":
        step("Create one file under a one-file namespace policy")
        var driver = DbFsDriver.new_hosted()
        var create = OpenFlags.read_write().with_create()
        val first = driver.open_path_bounded_v1(Path(raw: "/one"), create, 1, 2).unwrap()
        driver.pwrite_bytes_handle(first, 0, [1u8, 0u8, 255u8]).unwrap()
        driver.close_handle(first).unwrap()
        step("Admission failure must not create an inode or alter existing bytes")
        expect(driver.open_path_bounded_v1(Path(raw: "/two"), create, 1, 2).unwrap_err()).to_equal(FsError.TooLarge)
        expect(driver.stat_path(Path(raw: "/two")).unwrap_err()).to_equal(FsError.NotFound)
        val existing = driver.open_path_bounded_v1(Path(raw: "/one"), create, 1, 2).unwrap()
        expect(driver.pread_bytes_handle(existing, 0, 8).unwrap()).to_equal([1u8, 0u8, 255u8])
        expect(driver.open_path_bounded_v1(Path(raw: "/one"), create.with_excl(), 1, 2).unwrap_err()).to_equal(FsError.AlreadyExists)
        expect(driver.open_path_bounded_v1(Path(raw: "/absent"), OpenFlags.read_only(), 1, 2).unwrap_err()).to_equal(FsError.NotFound)
        driver.close_handle(existing).unwrap()

    it "rejects before truncation or creation and admits again after close":
        step("Retain the only admitted file descriptor")
        var driver = DbFsDriver.new_hosted()
        var create = OpenFlags.read_write().with_create()
        val first = driver.open_path_bounded_v1(Path(raw: "/one"), create, 2, 1).unwrap()
        driver.pwrite_bytes_handle(first, 0, [4u8, 5u8]).unwrap()
        expect(driver.open_path_bounded_v1(Path(raw: "/one"), create.with_trunc(), 2, 1).unwrap_err()).to_equal(FsError.TooLarge)
        expect(driver.pread_bytes_handle(first, 0, 8).unwrap()).to_equal([4u8, 5u8])
        expect(driver.open_path_bounded_v1(Path(raw: "/two"), create, 2, 1).unwrap_err()).to_equal(FsError.TooLarge)
        expect(driver.stat_path(Path(raw: "/two")).unwrap_err()).to_equal(FsError.NotFound)
        driver.close_handle(first).unwrap()
        step("A closed descriptor releases admission for a real truncate")
        val truncated = driver.open_path_bounded_v1(Path(raw: "/one"), create.with_trunc(), 2, 1).unwrap()
        expect(driver.fstat(truncated).unwrap().size).to_equal(0)
        driver.close_handle(truncated).unwrap()

    it "counts only this owner's visible files and live file descriptors":
        step("Independent owners and directory handles do not consume this file policy")
        var first = DbFsDriver.new_hosted()
        var second = DbFsDriver.new_hosted()
        val create = OpenFlags.read_write().with_create()
        val a = first.open_path_bounded_v1(Path(raw: "/same"), create, 1, 1).unwrap()
        val directory = second.opendir_path(Path(raw: "/")).unwrap()
        val b = second.open_path_bounded_v1(Path(raw: "/same"), create, 1, 1).unwrap()
        first.pwrite_bytes_handle(a, 0, [6u8]).unwrap()
        second.pwrite_bytes_handle(b, 0, [7u8]).unwrap()
        step("Unlink releases a name but its retained handle still consumes admission")
        first.unlink_path("/same").unwrap()
        expect(first.open_path_bounded_v1(Path(raw: "/replacement"), create, 1, 1).unwrap_err()).to_equal(FsError.TooLarge)
        first.close_handle(a).unwrap()
        val replacement = first.open_path_bounded_v1(Path(raw: "/replacement"), create, 1, 1).unwrap()
        expect(second.pread_bytes_handle(b, 0, 1).unwrap()).to_equal([7u8])
        first.close_handle(replacement).unwrap()
        second.close_handle(b).unwrap()
        second.close_dir_handle(directory).unwrap()

    it "rejects invalid or zero admission without creating a namespace entry":
        step("Invalid limits and zero capacity fail before any mutation")
        var driver = DbFsDriver.new_hosted()
        val path = Path(raw: "/no-entry")
        val create = OpenFlags.read_write().with_create()
        expect(driver.open_path_bounded_v1(path, create, -1, 1).unwrap_err()).to_equal(FsError.InvalidArg)
        expect(driver.open_path_bounded_v1(path, create, 1, -1).unwrap_err()).to_equal(FsError.InvalidArg)
        expect(driver.open_path_bounded_v1(path, create, 0, 1).unwrap_err()).to_equal(FsError.TooLarge)
        expect(driver.open_path_bounded_v1(path, create, 1, 0).unwrap_err()).to_equal(FsError.TooLarge)
        expect(driver.stat_path(path).unwrap_err()).to_equal(FsError.NotFound)
        val admitted = driver.open_path_bounded_v1(path, create, 1, 1).unwrap()
        driver.close_handle(admitted).unwrap()
```

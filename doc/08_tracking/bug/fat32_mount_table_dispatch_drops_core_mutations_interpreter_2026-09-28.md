# FAT32 through MountTable loses Fat32Core mutations on the interpreter

**Status:** open. **Found:** 2026-09-28 while restoring the execute-path /
stable-snapshot code lost in stale snapshot `4edef8fab8e`.

## Symptom

On the interpreter, a FAT32 file opened through `MountTable` cannot be used:
`MountTable.open("/TOOL", ...)` returns Ok, then `positioned_write_bytes`,
`positioned_read_bytes`, `close` and `open_for_execute` on it all fail with
`FsError.InvalidArg`. Reproduces with
`FsFat32Driver.new_ram_backed_with_file("TOOL", "abcd")` mounted at `/`.

## Cause

`Fat32Core` keeps its open-file table (`open_files`) and `file_generations`
as struct fields. `mount_driver_dispatch.spl` calls every backend through
`match driver: case DriverInstance.Fat32(d): d.open_path(...)`, where `d` is a
value copy of the payload. The `me fn` mutation lands on that copy and is
discarded, so the `MountEntry.driver` stored in the table never records the
open file; the next operation looks up a handle the core has never seen.
`_driver_mount` already works around the same class for `mount()` by
returning the mutated instance; no other FAT32 dispatch path does.

DBFS and NVFS are unaffected because their state lives in module-level stores
keyed by instance id. `fat32_file_ops.spl:80,148,157` additionally assign
`self.file_generations[slot].field = ...`, which the interpreter rejects with
"complex indexed field receiver is not supported".

## Affected examples

- `mount_table_execute_path_open_spec`: "reads retained executable bindings
  as exact binary bytes", "rejects invalid limits, size substitution, and stale
  execute bindings", "searches FAT32, DBFS, and NVFS".
- `stable_file_snapshot_spec`: "uses true FAT32 offsets and short EOF".

## Fix direction

Either give `Fat32Core` an instance-keyed module store for open files and
generations (the DBFS/NVFS shape), or have every mutating FAT32 dispatch
return the mutated `DriverInstance` and write it back into both
`MountTable.mounts[i]` and `mount_slots`. Rewrite the three
indexed-field assignments in `fat32_file_ops.spl` as row read-modify-write.

# DBFS `open_on_device` refuses a valid staged volume in-guest (x86_64 freestanding)

Date: 2026-09-01
Gate: `scripts/check/check-simpleos-dbfs-server-roundtrip-ovmf.shs` (honestly RED)
Status: OPEN — blocks L5..L10 of the dbfs in-guest round-trip lane

## Summary

The DBFS filesystem server cannot be brought up in-guest. Under real OVMF
firmware the guest gets as far as reading a valid DBFS superblock off a real
NVMe device and then `DbFsDriver.open_on_device` refuses the volume, with no
usable error detail.

Three blockers on the path to this point were found and FIXED (see below); this
record covers the one that remains.

## Evidence — serial transcript, OVMF pflash -> GRUB-EFI -> multiboot1

```
[grub-uefi] multiboot loading /boot/kernel.elf ...
[dbfsrt] probe begin nonce=202609010121051769915
[dbfsrt] acquiring pure-Simple NVMe adapter
[dbfsrt] nvme adapter ok=true
[dbfsrt] dbfs superblock found=true gen=1
[dbfsrt] dbfs superblock block_count=65532
[dbfsrt] dbfs driver open ok=false err=
[dbfsrt] dbfs driver open raw=<object>
[dbfsrt] PROBE FAILED: DbFsDriver.open_on_device refused the volume
```

Verdict line:

```
FAIL — 10 check(s) checked, missing: L5 L6 L7 L8 L9 L10 (nonce=..., token=..., ...)
```

L1..L4 are GREEN: firmware boot, guest entry at this run's nonce, the
pure-Simple NVMe BlockDevice, and superblock recognition of the volume this run
staged.

## Localisation

`DbFsDriver.open_on_device` (`src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:396`)
fails somewhere AFTER its argument guard and BEFORE returning Ok. The guard is
proven passed: it rejects `block_count < 4`, and the guest reads back
`block_count=65532` with `base_block=4`. That leaves, in order:

1. `dbfs_owner_transaction_begin()` -> `Err(FsError.Unsupported)`
2. `_alloc_inst_id_locked()` -> `Err(FsError.TooLarge)`
3. `dbfs_device_register_locked(iid, dev)` -> registration refusal
4. `_dbfs_replay_namespace_locked(iid, base_block, block_count)` -> replay refusal

(3) and (4) are the prime suspects: both touch the device, and this is the first
context in which DBFS has ever seen a REAL NVMe BlockDevice rather than the
host `MemBlockDevice`.

## Why the error could not be narrowed further — a second defect

The refusal carries no identity in freestanding:

- `_dbfsrt_fs_err_text(driver_r.unwrap_err())`, a total `match` over every
  `FsError` variant, rendered as the EMPTY STRING.
- `"{driver_r}"` on the raw `Result` rendered as `<object>`.

A total match cannot legitimately produce "". This matches the documented
x86_64-freestanding `.unwrap()` defect class (`rt_unwrap_or_trap` returning the
wrapper rather than the payload), and it is what blocks further diagnosis from
inside the guest. Fixing error rendering in freestanding is a prerequisite for
finishing this investigation cheaply.

## Fixed on the way here (all landed, all measured)

1. **`content_generation` never threaded through `DbFsInode` rebuilds**
   (`namespace_io.spl`). All 8 mutation sites omitted the field, so it
   defaulted to 0, and `_valid_entry_shape` rejects any live namespace entry
   with generation 0. Net effect: **DBFS could not create or write ANY file on
   a device-backed volume.** Before: `dbfs image seed open failed: /DBFSRT.TOK
   err=invalid-arg`. After: a 32MiB volume builds with its seeded contents
   byte-greppable in the raw image.

2. **`dbfs_image.spl` formatted with `dbfs_superblock_format_disk`**, which
   serializes `block_count = 0` ("unknown"); its own docstring says production
   boot media must use `dbfs_superblock_format_disk_with_block_count`. Every
   image the builder produced was unmountable by the production probe, which
   passes `sb.block_count` straight into `open_on_device`'s `< 4` guard. The
   VOLUME was fixed to satisfy the production contract; no production check was
   weakened.

3. **Errors were being discarded.** `dbfs_image.spl` reported only
   `"dbfs image seed open failed: <path>"`, hiding the `FsError` that named the
   cause. Now rendered. This alone turned an opaque failure into a one-run fix.

## Adjacent, lower-confidence finding

`main(args: [text])` never receives argv via `simple run <file> -- <args>` for
`src/os/port/mkfs_dbfs.spl` and `mkfs_dbfsrt.spl` — the run dies with
`error: semantic: function expects argument for parameter 'args', but none was
provided`. Since `scripts/os/mkfs-dbfs.shs:11` uses exactly that invocation, the
repo's DBFS image builder cannot be run by its documented path. A minimal
control script was NOT conclusive: it was killed by the host CPU watchdog at
985s before reaching main, so this is proven only for these two modules and must
not be cited as a general seed-wide argv break. Re-run the control with
`SIMPLE_TIMEOUT_SECONDS=0`.

## Next step

Add serial-visible instrumentation to the four candidate steps above (or fix
freestanding `FsError` rendering first, which is cheaper and unblocks any future
in-guest DBFS work), then re-run the gate. The gate is fail-closed and needs no
change to go green once the driver opens.

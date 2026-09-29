# DBFS `open_on_device` refuses a valid staged volume in-guest (x86_64 freestanding)

Date: 2026-09-01
Gate: `scripts/check/check-simpleos-dbfs-server-roundtrip-ovmf.shs` (honestly RED)
Status: OPEN — blocks L5..L10 of the dbfs in-guest round-trip lane

## Summary

The DBFS filesystem server cannot be brought up in-guest. Under real OVMF
firmware the guest gets as far as reading a valid DBFS superblock off a real
NVMe device and then `DbFsDriver.open_on_device` refuses the volume.

The refusal is **by design**: DBFS's device commit owner fail-closes on any
platform without an audited runtime mutex provider, and SimpleOS has none. See
ROOT CAUSE. Three separate blockers on the path to this point were genuine bugs
and were FIXED (see "Fixed on the way here"); this record covers the one that
remains, which is a missing feature rather than a defect.

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

## ROOT CAUSE (established by measurement, not inference)

`dbfs_owner_transaction_begin()` returns **false**, so `open_on_device` returns
`Err(FsError.Unsupported)` at its very first gate.

Method: i64 stage/diag markers temporarily compiled into the stdlib (the kernel
compiles stdlib from source every gate run, so no rebuild is needed). Plain
integers were used deliberately — they are immune to the freestanding
Result/enum rendering defect described below. Two runs:

- `open stage=2` — reached the marker immediately before
  `dbfs_owner_transaction_begin()`, never reached 3.
- `lockdiag=0` — every bit of `_owner_lock()`'s precondition mask clear, and
  `_DBFS_DEVICE_OWNER_MUTEX == 0`.

The chain, all in `device_commit_owner.spl`:

```
dbfs_device_mutex_provider_blocker(platform)   # :20
    -> "ready" ONLY for linux|macos|windows|freebsd|illumos|solaris
    -> otherwise DBFS_DEVICE_SERIALIZATION_MISSING
val _DBFS_DEVICE_OWNER_MUTEX = if blocker == "ready": mutex_raw_create() else: 0   # :57
fn _owner_lock() = not quarantined and blocker == "ready"
                   and _DBFS_DEVICE_OWNER_MUTEX > 0 and mutex_raw_lock(...)        # :79
```

SimpleOS/freestanding is not on the allowed list, so the blocker is
`SERIALIZATION_MISSING`, the mutex is never created, and the lock can never be
taken.

## This is DELIBERATE, and must NOT be relaxed

The source says so directly (`device_commit_owner.spl:21-22`):

> These are the audited runtime_thread.c pthread/critical-section targets.
> **Freestanding, SimpleOS, empty, and unknown providers remain fail-closed.**

DBFS's device commit owner serializes every device binding and every namespace
commit through one runtime-backed mutex. Without an audited provider it fails
closed rather than silently corrupting a filesystem under concurrent commits.
Adding `"simpleos"` to that allow-list would turn this gate green while
removing a real serialization guarantee — exactly the fabricated evidence this
lane exists to rule out. **Do not do it.**

## What DBFS-in-guest actually needs

A real SimpleOS/freestanding critical-section provider behind `mutex_raw_create`
/ `mutex_raw_lock` / `mutex_raw_unlock`, audited the same way the
`runtime_thread.c` targets were, and then SimpleOS added to the allow-list. That
is a feature, not a one-line fix, and it is the single remaining blocker: with
it in place the lane's L5..L10 should follow, since L1..L4 already prove the
volume, the device, and the superblock are all good.

## Secondary defect — freestanding error rendering

The refusal carries no identity in freestanding:

- `_dbfsrt_fs_err_text(driver_r.unwrap_err())`, a TOTAL `match` over every
  `FsError` variant, renders as the EMPTY STRING.
- `"{driver_r}"` on the raw `Result` renders as `<object>`.

A total match cannot legitimately produce "". This matches the documented
x86_64-freestanding `.unwrap()` defect class (`rt_unwrap_or_trap` returning the
wrapper rather than the payload). It is why the i64-marker technique above was
necessary, and it is worth fixing on its own: it will silently mislead any
future in-guest driver work.

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

Implement and audit a SimpleOS/freestanding mutex provider (see "What
DBFS-in-guest actually needs"), then add SimpleOS to the allow-list in the same
change. The gate is fail-closed and needs no modification to go green once
`open_on_device` succeeds. Fixing freestanding `FsError` rendering is a cheaper,
independent win that should probably land first.

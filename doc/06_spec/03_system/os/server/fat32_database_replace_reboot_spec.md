# FAT32 database replace across a fresh SimpleOS boot

Status: **required, intentionally failing until the live runner exists**.
This manual never promotes unit, source, serial-marker, or host-edited-image
evidence to a reboot durability result.

## Primary recovery flow

1. **Given a writable provisioned FAT32 server image.** Verify the SimpleOS
   extension reserves exactly 16 contiguous, non-allocatable sectors and save
   the image hash.
2. **When the DB commit is power-cut at crash point N.** Start a new ARM QEMU
   process, commit through the public DB protocol, and terminate at each
   journal payload write/flush, header write/flush, after-image write/flush,
   reclaim-record write/flush, FAT-copy write/flush, and DONE write/flush.
3. **When the same image boots again.** Reuse the exact disk image in a new
   QEMU process; retain PID/process-start, serial, disk hash, and recovery
   receipt so an in-process remount cannot pass.
4. **Then the public DB protocol returns exactly the acknowledged generation.**
   Query through the public protocol. Before COMMITTED the old generation is
   required; after COMMITTED the complete new generation is required.

## Negative flow

Boot an otherwise valid image without the extension descriptor. The mount may
remain read-only/unavailable, but `RecoverableReplaceV1` must be Unsupported
and neither ordinary `rename_at` nor delete-plus-rename may be invoked.

Required artifacts per crash point: QEMU command/identity, pre/post disk
SHA-256, serial log, journal-bank decode, recovery receipt, and public protocol
request/response. Physical UNO Q evidence is a separate acceptance cell.

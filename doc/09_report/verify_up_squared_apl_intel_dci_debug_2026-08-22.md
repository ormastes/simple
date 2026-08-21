# Verification report: UP Squared Apollo Lake debug and storage

## Evidence

- PASS: admitted Stage-3 freestanding build, 58 compiled / 0 failed.
- PASS: self-contained 256 MiB UEFI USB image structural gate; SHA-256
  `311087e4f7f58b3a545a1b5acb4f28f85643b7567ba7c631f21762eb03b5c644`.
- PASS: fresh OVMF boot, VFS entries `bin,etc,README.txt`, exact QEMU NVMe
  identity, and `media_writes=0` before admission.
- PASS: four consecutive nonzero 1024-byte RSP `M` packets return `+$OK#9a`;
  independent `m` readback returns `000102...0f`.
- PASS: numbered-artifact guards, direct-env guards, no scoped placeholder
  patterns, and zero executable `.spl` files under `doc/06_spec`.

## Failures and blockers

- FAIL: freestanding streaming SHA-256 rejects independently verified staging
  bytes. The raw-image session aborts before `BlockDevice.write_sector`; flush
  and fresh-adapter whole-range readback are therefore unproven. The mandatory
  three-cycle retry cap was reached. See
  `doc/08_tracking/bug/up2_sha256_stream_freestanding_mismatch_2026-08-22.md`.
- FAIL: no admitted current-source Stage-4 CLI exists in this workspace, so
  executable SPipe/docgen/maintenance evidence cannot be produced.
- BLOCKED: physical UP2 CN16, Intel DCI, NVMe persistence, and cold NVMe boot
  receipts require the board and qualified transport to be reachable.
- BLOCKED: the resident UEFI mailbox loader/consumer is not implemented.

STATUS: FAIL

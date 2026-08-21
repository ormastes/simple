# Verification report: UP Squared Apollo Lake debug and storage

## Evidence

- PASS: admitted Stage-3 freestanding build, 58 compiled / 0 failed.
- PASS: self-contained 256 MiB UEFI USB image structural gate; SHA-256
  `6d947ef3f2ec65d417f5e3a6740e4dddbf3dbab23d19ed99adaee54fadc2e6b5`.
- PASS: fresh OVMF boot, VFS entries `bin,etc,README.txt`, exact QEMU NVMe
  identity, and `media_writes=0` before admission.
- PASS: four consecutive nonzero 1024-byte RSP `M` packets return `+$OK#9a`;
  independent `m` readback returns `000102...0f`.
- PASS: constant-memory target SHA, dedicated scratch-NVMe write, Flush,
  fresh-adapter exact readback, independent host SHA, and unchanged adjacent
  ranges through `--ovmf-image-provision`.
- PASS: the current 256 MiB image boots as the sole NVMe device with USB absent
  and completes command-correlated VFS `ls /` through `--ovmf-nvme-boot`.
- PASS: `--ovmf-dci-admission` uses GNU GDB to write the exact current
  298,648-byte SimpleOS ELF and commit-last descriptor into the resident UEFI
  windows; the PE32+ loader preserves the nonce, verifies SHA-256 and ELF
  bounds, constructs the final EFI map, exits boot services, enters the
  embedded ELF32 shim, and reaches the SimpleOS shell without GRUB fallback.
  That runtime receipt binds image `652d5d53…cdf08d`; the latest rebuild differs
  in container metadata but has the identical loader PE `2b116981…a936e` and
  kernel `0a8afd63…293c08`.
- PASS: `--ovmf-dci-rejection` uses the same complete payload with an all-zero
  descriptor digest and proves rejection before admission, transition, or GRUB.
- PASS: the no-commit PE32+ timeout still chainloads `GRUBX64.EFI`, which boots
  the same kernel and completes VFS-backed `ls /`.
- PASS: numbered-artifact guards, direct-env guards, no scoped placeholder
  patterns, and zero executable `.spl` files under `doc/06_spec`.

## Failures and blockers

- FAIL: no admitted current-source Stage-4 CLI exists in this workspace, so
  executable SPipe/docgen/maintenance evidence cannot be produced.
- BLOCKED: physical UP2 CN16, Intel DCI, NVMe persistence, and physical cold NVMe boot
  receipts require the board and qualified transport to be reachable.
- BLOCKED: physical multi-core UP2 boot still needs firmware MP-topology and
  post-transition kernel AP-state receipts; the OVMF DCI admission oracle uses
  one CPU and cannot prove the PI ExitBootServices idle state on this board.

STATUS: FAIL

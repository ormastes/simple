# NFR requirements: SimpleOS on UP Squared Apollo Lake

Selected: fail-closed physical evidence (NFR set A), 2026-08-17.

- NFR-001: resolve media and console adapters by stable USB identity and
  interface metadata, never transient device numbering.
- NFR-002: reject missing, ambiguous, mounted, held, non-removable, system,
  root, swap, internal-eMMC, and identity-changing media targets.
- NFR-003: boot and Identify perform no internal-storage writes. Persistent
  writes are restricted to the selected removable USB, or to the exact NVMe
  identity named by a separately entered format challenge; never write eMMC,
  BIOS/SPI, UEFI variables, or CN22.
- NFR-004: media admission requires exact serial confirmation and full image
  readback equality before boot.
- NFR-005: all subprocesses and UART waits are bounded and retain artifacts.
- NFR-006: missing hardware or required privilege is BLOCKED; unsafe media,
  malformed evidence, boot failure, timeout after connection, or static/fake
  `ls` evidence is FAIL.
- NFR-007: one stateful live session is the sole physical acceptance oracle.
- NFR-008: CN16 uses 3.3 V TTL only; CN22 is never treated as CPU JTAG.
- NFR-009: namespace and partition LBAs are lease-bounded; controller/DMA
  mutable state remains owned by `NvmeDriver` and is not copied across domains.
- NFR-010: storage PASS requires GPT/FAT32 interoperability plus flushed
  write/read equality after a fresh adapter, not an in-memory echo.

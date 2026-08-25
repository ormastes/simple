# Simple toolchain signed-catalog media gap

## Status

Open — loader-private preparation and cleanup foundations exist, but no boot
launch connection exists. Production media, signer initialization, and a
privileged caller remain required.

## Static audit

- x86_64, ARM64, and RV64 have signed Simplebox SCR1 ingestion, but that record
  covers `/bin/simplebox` and its coreutils aliases only.
- Existing filesystem-exec smoke entries directly read or launch
  `simple_compiler`, `simple_interpreter`, and `simple_loader` payloads without
  proving that those three paths are sealed catalog rows.
- ARM32 mounts the canonical FAT32/VFS owner but has no generated ARM32 trust
  configuration or SCR1 boot-ingestion adapter.
- No current image producer emits three SCR1 records for
  `/sys/apps/simple_interpreter.smf`, `/sys/apps/simple_compiler.smf`, and
  `/sys/apps/simple_loader.smf`.

## Implemented resume boundary

`simple_toolchain_signed_catalog_boot_v1.spl` is a dormant loader-package
foundation. It requires all three target-bound catalog rows to share one signer
and trust root, and its error paths retire prepared handles/tokens before
restoring the VFS lease. It is not invoked by boot and cannot currently prepare
an admission because the online signer has no production initializer. The
optional availability probe does not affect ordinary boot when records are
missing; no path falls back to resident or cached bytes.

## Remaining unblock conditions

1. Extend the installer signed bundle to emit and stage the three distinct
   toolchain artifact/SCR1 pairs with the architecture trust root.
2. Generate and embed x86/ARM32/RV32 trust configurations and catalog-ingestion
   adapters, or explicitly leave those 32-bit targets unavailable in the
   signed-media matrix.
3. Install the loader authority registry and online re-attestation owner from
   boot-owned configuration/secret handoffs,
   with verified seed wiping and the same signer/trust identity as the triplet.
4. Select a real mounted FAT32/DBFS/NVFS source and output path, then invoke
   `simple_toolchain_signed_catalog_boot_launch_v1` with the actual nonzero
   parent task ID before user services begin.

Owner: SimpleOS installer/loader integration. Final reviewer: loader security.

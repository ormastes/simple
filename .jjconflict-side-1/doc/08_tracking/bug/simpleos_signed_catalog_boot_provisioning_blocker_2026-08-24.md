# SimpleOS signed catalog boot provisioning blocker

The fail-closed catalog population transaction now has an explicit pure-Simple
owner. A loader-package adapter can consume the committed hosted safe-root
provisioner result, revalidate its bounded receipt and exact Simplebox bundle,
and enter the verify-before-mutate transaction without exposing a public
mutation API. No production image currently supplies that adapter's
authenticated boot-owned input.

Missing production evidence:

- signed canonical manifest records for `/SERVERS.ELF`, the database server,
  `/usr/bin/simple` roles, `/usr/bin/clang` and LLVM roles, and primary tools;
- complete records for x86_64, x86, aarch64, arm, riscv64, and riscv32 images;
- authenticated boot-policy transfer of trusted Ed25519 roots, the exact image
  target, and the complete required canonical-path set; and
- a freestanding on-image reader plus typed SAM1 manifest decoder (SCR1 is
  bounded and canonical but currently requires a separately supplied typed
  manifest projection); and
- a boot-owned platform policy that supplies the pinned Ed25519 roots, target,
  required complete bundle, and calls the package-private ingestion adapter
  before any launcher.

The unsigned Simplebox build receipt remains deliberately inadmissible. The
owner verifies all records before opening the one-way bootstrap session and
therefore cannot fabricate a sealed catalog from present installer metadata.
The mutation-bearing adapter is deliberately package-private: making it public
would let a copied provision result select the one-time trust roots. Wiring it
into a boot sequence before the missing platform policy exists would recreate
that authority bug.
No runtime verification was run, by user request.

## 2026-08-25 combined-release update (unverified)

The active implementation now prepares the signed Clang/sysroot and primary
tool releases together, requires an identical nonempty release ID, assigns the
only Simplebox record to the primary plan, and calls the installed-artifact
composition owner once for fourteen records. The host producer likewise has a
two-descriptor extension to one retained-root bounded bundle transaction.
These are source changes under review, not verified completion; no manual test,
build, SPipe, image, QEMU, benchmark, or optimizer command was run.

The original "no production input" blocker is narrowed, not closed:

- `src/os/installer/image_builder.spl` stages signed media into a rootfs tree,
  but `_materialize_primary_artifact` produces a real disk only for the
  non-installer x86_64 FAT32 path. Other architectures fall back to a
  descriptor, while DBFS/NVFS backend markers do not materialize the signed
  files into a boot-mounted filesystem. Unblock by adding target-aware FAT32,
  DBFS, and NVFS materializers that atomically preserve exact payload, SCR1,
  trust, and both descriptor bytes, followed by live guest launch receipts.
- `src/os/port/llvm/sysroot.shs` owns runtime construction only for x86_64 and
  aarch64. The build driver recognizes armv7/riscv32, but the sysroot owner
  rejects those runtime triples; i686 has no driver/catalog row. Unblock each
  32-bit row with a per-target sysroot, CRT, syscall ABI, libc, Simple runtime,
  linker layout, signed target-native artifacts, image adapter, and live
  filesystem compile/link/run evidence.
- Fresh x86_64, aarch64, and riscv64 FAT32/DBFS/NVFS guest evidence remains
  open. Static adapters and focused specs cannot establish a boot or launch.

Authoritative narrow handoff:
`doc/03_plan/agent_tasks/simpleos_combined_signed_catalog_boot.md` and
`.spipe/simpleos_combined_signed_catalog_boot/state.md`.

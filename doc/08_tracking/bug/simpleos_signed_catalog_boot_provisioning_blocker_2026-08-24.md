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

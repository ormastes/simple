# SimpleOS signed catalog boot provisioning blocker

The fail-closed catalog population transaction now has an explicit pure-Simple
owner, but no production image currently supplies its authenticated input.

Missing production evidence:

- signed canonical manifest records for `/SERVERS.ELF`, the database server,
  `/usr/bin/simple` roles, `/usr/bin/clang` and LLVM roles, and primary tools;
- complete records for x86_64, x86, aarch64, arm, riscv64, and riscv32 images;
- authenticated boot-policy transfer of trusted Ed25519 roots, the exact image
  target, and the complete required canonical-path set; and
- a canonical bounded on-image record codec and boot reader that invokes
  `installed_artifact_catalog_populate_from_boot_policy_v1` before launchers.

The unsigned Simplebox build receipt remains deliberately inadmissible. The
new owner verifies all records before opening the one-way bootstrap session and
therefore cannot fabricate a sealed catalog from present installer metadata.
No runtime verification was run, by user request.


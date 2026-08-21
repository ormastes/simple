# SimpleOS ARM64 native linker contract

Mirror of `test/03_system/os/simpleos_arm64_native_link_contract_spec.spl`.

The executable SSpec checks host GPU daemons stay out of compiler closure, freestanding ARM64 dispatch reaches real boot owners, generic discovery excludes host probes, RV64 probes link the real runtime, minimal boot mode is enabled, one ABI-correct TLB invalidation owner remains, RV64 exits through OpenSBI, ivshmem ownership stays separated, and early polling is bounded.

This is static native-link and ownership evidence, not an ARM64 boot run.

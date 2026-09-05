# RV64 native linker runtime ownership

Mirror of `test/01_unit/compiler/backend/rv64_real_runtime_link_contract_spec.spl`.

The executable SSpec verifies that RV64 native links use architecture-owned probe behavior rather than generated success bodies and retain real storage and SMF checks in the selected runtime.

This is static linker/source-contract evidence; it does not execute a produced image on RV64 hardware or an emulator.

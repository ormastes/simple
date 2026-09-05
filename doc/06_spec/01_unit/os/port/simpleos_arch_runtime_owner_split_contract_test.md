# SimpleOS Architecture Runtime Owner Split

Source: `test/01_unit/os/port/simpleos_arch_runtime_owner_split_contract_test.shs`

Evidence class: `host-build-fixture`.

The test compiles and relocatably links x86_64 and ARM64 runtime-owner objects,
requires one definition for selected ABI symbols, checks backend linker wiring,
and enforces the 800-line owner limit. It proves host cross-object symbol
ownership, not a booted architecture runtime.


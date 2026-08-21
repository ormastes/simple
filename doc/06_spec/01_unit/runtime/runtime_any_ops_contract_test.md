# Runtime Any-Operations Cross-Runtime Contract

Sources:

- `test/01_unit/runtime/runtime_any_ops_contract_test.shs`
- `test/01_unit/runtime/runtime_any_ops_contract_test.c`

Evidence class: `host-build-fixture` plus `source-contract`.

The shell owner compiles and executes the C fixture against the bounded any-op
and string-FFI runtime modules. The fixture checks integer and floating-point
arithmetic and comparisons, divide-by-zero behavior, and copied/null C-string
conversion. Static checks require matching pure-Simple owners, guarded signed
division overflow, bounded headers, and no leakage into the monolithic runtime
header.

This proves the host runtime contract and symbol surface; it is not a SimpleOS
guest or architecture-native execution result.


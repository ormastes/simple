# Parallel Ownership and Storage Layout System-Test Plan

Current scope is the Wave 0 transfer vocabulary. The focused unit contract is
`test/01_unit/common/structural/transfer_contract_spec.spl`.

Future SPipe/system scenarios remain blocked on the corresponding executable
waves and must use real transport, not mocks:

| AC | Scenario | Dependency | Required evidence |
|---|---|---|---|
| AC-4 | child-created output through bounded typed thread transport | WP-13..18 | send/receive/cancel receipt |
| AC-4 | process pointer rejection and encoded/object-ref transfer | WP-13, WP-17 | distinct-process identity proof |
| AC-5 | unknown dynamic index overlap and proven disjoint slice | WP-10..12 | compile diagnostics/MIR facts |
| AC-6 | AoS/SoA transformed view parity and ABI rejection | WP-20..25 | `storage_layout_custom_native_execution_spec.spl` exact-byte/canary evidence; currently blocked before execution by `smf_mmap_native.ptr_read_u8` native codegen |
| AC-7 | MDSOC port route with bypass sabotage | WP-30 | route receipt and deliberate bypass failure |
| AC-8 | randomized child completion with canonical parent commit | WP-15 and pilot | deterministic receipt hash |
| AC-8 | armored child stdout result reaches a generation-bound, replay-rejecting parent ingress and owner commit | WP-15, WP-17 | `parent_commit_piped_result_spec.spl`: real pipe, accepted frame, retained-line high-water, idempotent child close receipt, and owner receipt; blocked until the self-hosted `test --help` crash is repaired |

When these scenarios become executable, create mirrored `test/03_system/...`
SSpec and `doc/06_spec/...` manual artifacts; do not add a passing placeholder
before a real runtime boundary exists.

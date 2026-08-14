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
| AC-8 | armored child stdout result reaches a generation-bound, replay-rejecting parent ingress and owner commit | WP-15, WP-17 | `parent_commit_piped_result_spec.spl`: authored real-pipe five-step flow, copied isolation, typed mutation receipt, rollback, retained-line high-water, and close-once receipt; native verdict remains blocked until the self-hosted `test --help` crash is repaired. See `doc/03_plan/sys_test/parent_authoritative_actor_process.md`. |

The parent-result SSpec and authored `doc/06_spec/...` manual mirror now exist;
they deliberately retain a blocked-generation status. Other future scenarios
still require both artifacts. Do not add a passing placeholder or hand-enter a
generated/maintenance PASS before a real runtime boundary exists.

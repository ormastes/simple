# Test-runner MIR rejects multiple wildcard arms

Status: FAIL; root cause not established.

Producer c27cb117978d2212cae16a6d956690e13003435f73f2047f1fa237f2fa8a8466; source 6ec114562; Cranelift; normal/slim non-delegated compiler matrix, three build threads and one test worker. The test_runner_build task reached MIR lowering for 252 modules and failed at elapsed_ms=334400, before native-cache planning, with: `MIR lowering error: B5b: match has multiple wildcard arms`. The emitted diagnostic does not identify the responsible source/function. Do not infer which match is faulty from this message alone.

Log: /mnt/wsl/simple-dbc-native-bootstrap-20261012/stage2-compiler-tests/x86_64-unknown-linux-gnu/verification/logs/test_runner_build.log. The matrix remains live at initial observation; inspect its terminal producer-bound summary before reporting final status/RSS.

This failure occurs earlier than producer4c's native-cache RSS cap. It neither proves nor disproves the MIR-identity scratch reclamation repair. No cap was raised, no wildcard guard removed, and no new full rebuild or callback retry was launched. The CLI build is independent and remains in progress. General test/SPipe qualification remains unavailable.

A source-only diagnostic improvement now includes the duplicate wildcard arm index, owning function and module in this same rejection branch, matching the adjacent binding-default diagnostic's owner information. The duplicate-default guard, error severity, source span and return behavior are unchanged. This does not repair the failure and has not been rebuilt or executed. No speculative source match was rewritten.

Terminal matrix confirms test_runner_build FAIL status1 after373 seconds, peak2946784 KiB; the CLI independently failed status88/RSS after793 seconds. Overall bootstrap exited1 at stage2-compiler-tests. There is no remaining live session30186 to wait on.

## Item-2 source probe reproduction — 2026-10-20

The admitted pure-Simple producer645e62a8 additionally fails
`lib.scv.db_pages.db_page_decode` with
`B5b: match has multiple wildcard arms (arm 1)` while compiling the197-module
budgeted-store probe closure. This is production DB code, not a test-runner
placeholder. Retained grouped diagnostics and source/snapshot identities:
`doc/03_plan/evidence/seven_plans/items247_store_compile_diagnostics_2026-10-20.md`.
No native executable or Phase3 PASS resulted.

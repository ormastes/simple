# Phase 2 subsystem test helpers fail MIR lowering

Status: OPEN (P1). No subsystem test binary or test execution is proved by this run.

## Reproduction and evidence

Diagnostic packet: `six-products-current-proven-transport1` under the Windows
restart evidence directory. Producer source: `916be6c20617637e2cccf3d18c23669470ab8ffe`.
Producer SHA-256: `2b83155910336e56ec8b663c3d3e7d3ceb9c61b60fa98182163f9670ff044c33`.
The six compiler/interpreter/loader lanes across LLVM and Cranelift each completed
source inventory with exit zero, then generator and main-verdict helper builds
each returned exit one. Product matrices report required helper compilation
failure and unknown registered/executed/pass/fail test counts. These are twelve
helper build failures, not twelve failed test cases.

`helper-build-failures.json` preserves extracted diagnostics for all six lanes.
The LLVM compiler lane contains 27 distinct generator error lines and 11 verdict
error lines; these are diagnostic counts, not independent root-cause counts.
Completed step receipts retain command, output hashes, actual exit and process
closure. Preserve this packet and its caches for comparison with the successor.

## Parallel diagnosis

- Generator/frontend: `FlatPoolReader` constructor and method resolution in
  `flat_pool_codec.spl`, and `ord` resolution in `placeholder_lambda.spl`.
- Shared I/O/type propagation: `Result` methods and process handle methods in
  `nogc_sync_mut/io/process_ops.spl`, `ProcessObservationPacketKindV4` operator
  lowering, enum arm lowering, an I64 collection iteration, and string methods
  in `nogc_sync_mut/io/env_ops.spl`.

These groupings assign investigation; a diagnostic mentioning a struct does not
prove an enum identity defect. Existing dictionary typed-local workarounds are
applicable only after tracing the actual value's owner and type.

## Repair and acceptance

Use minimal reviewed source repairs or bug-linked semantic-preserving workarounds
with the current producer first. Keep frozen inputs immutable and carry forward
only valid caches. Do not remove tests, stub helper behavior, substitute a seed,
or count generator builds as subsystem test execution.

Compile and execute the real generator and verdict helpers, produce all six
native subsystem products, enumerate each binary's registered tests, then run
each binary through completion with truthful counts and closure evidence.
Qualify root fixes with reproductions and neighboring cases before retiring
workarounds on an isolated later rebuild. Check memory and behavior for every
performance-related repair, and performance and behavior for memory repairs.

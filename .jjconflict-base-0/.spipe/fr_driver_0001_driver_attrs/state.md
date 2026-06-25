# Feature: fr-driver-0001-driver-attrs

## Raw Request
resolve driver framework request `FR-DRIVER-0001` if feasible. Own only driver framework source/tests/docs for this item, the assigned tracker entry, and `.spipe/<slug>/state.md`. Locate the exact request, define acceptance criteria, implement/close with focused tests, and final with status, changed paths, tests run, and blockers.

## Task Type
feature

## Refined Goal
Close FR-DRIVER-0001 by making the driver attribute sugar verifiably covered by existing compiler and driver framework tests, or record the remaining blocker if the Rust seed cannot exercise the self-hosted path.

## Acceptance Criteria
- AC-1: The FR-DRIVER-0001 tracker entry states the current implementation status and whether any live-compiler blocker remains.
- AC-2: Parser coverage verifies `@driver(...)` and `@native_lib(...)` named arguments for the requested fields.
- AC-3: HIR/MIR coverage verifies the parsed manifest is preserved on the owning declaration.
- AC-4: Synthetic registration coverage verifies `ReadyToSynthesize` emits a `register_static_driver(manifest, ops)` call through the self-hosted planner/codegen path.
- AC-5: SFFI lint coverage verifies `extern fn` plus `@driver(...)` requires a matching `impl Driver`.
- AC-6: Driver example coverage verifies `examples/simple_os/src/drivers/null_block.spl` uses `@driver(...)` and still passes the null block driver test.

## Scope Exclusions
No unrelated compiler feature work, no unrelated driver framework requests, no generated documentation refresh, no push.

## Phase
verified-focused

## Status
FR-DRIVER-0001 is salvaged for focused integration review. Attribute manifest parsing, SFFI driver-shim lint coverage, synthetic registration planning, and null-block attribute-sugar registration all pass focused interpreter verification. The broad `src/compiler` and `src/lib` checks also exit successfully with pre-existing warning noise.

The remaining blocker is live end-to-end proof that the Rust seed executes the self-hosted synthetic MIR injection path and emits a concrete `register_static_driver(manifest, ops)` runtime call. Current coverage verifies the self-hosted planner/codegen modules compile and that `ReadyToSynthesize` identifies the ops value; it does not prove native runtime execution of the injected call.

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
- codex: Focused salvage completed. Driver manifest attr parsing, synthetic registration planner, SFFI lint, SFFI driver shim, and null block driver tests pass. `src/compiler` and `src/lib` checks pass with existing warnings. Live self-hosted runtime injection remains the only integration blocker.

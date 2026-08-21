# Stage-3 incremental directory import resolution (2026-08-21)

## Status

Open, deterministic bootstrap blocker. The third bounded verify/fix cycle was
stopped after establishing the first HIR failure; no fourth bootstrap attempt
is permitted by the repository iteration guard.

## Evidence

The receipt-bound Stage-3 compiler completed all 954 streaming surface parses,
proving that whole-owner replacement removed the preceding transient pool
SEGV. HIR lowering then reported four errors in
`src/compiler/80.driver/driver_build/incremental.spl`:

- unresolved name `dir_list` at the named `std.io_runtime` import;
- unresolved name `dir_create_all` at the same import.

The source already has the explicit import
`use std.io_runtime.{dir_create_all, dir_list}`. This is therefore an imported
callable materialization/routing failure, not a missing source import.

## Next bounded action

Audit the `std.io_runtime` export origins for these two callables and compare
them with their canonical `std.nogc_sync_mut.io.dir_ops` declarations. Apply
one explicit, unambiguous route fix, then begin a fresh session and run one new
Stage-2 admission plus receipt-bound Stage-3/4 attempt. Do not use the Rust seed
as a verifier and do not bypass the must-check push gate.

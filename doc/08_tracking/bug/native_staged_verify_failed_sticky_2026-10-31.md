# Staged codegen: `verify_failed` withholds all later batches outside go-to-end

Status: OPEN
Date: 2026-10-31

`native_staged_codegen_flush_v1` (`src/compiler/80.driver/driver_aot_pipeline.spl`) clears
`verify_failed` only under go-to-end. Otherwise one real MIR verify failure withholds every later
batch, which contradicts the function's "later batches keep emitting" comments. Those batches are
also not added to `failed_batches`, and neither are batches withheld for a lowering failure, although
the docstring says every failed batch is named. The build still fails correctly.

PR #5615 made `lowering_failed` per batch; this is the same latch on the verify path.
Found by code review; not reproduced.

Unblock: reset the verify verdict per batch and record withheld batches in `failed_batches`.

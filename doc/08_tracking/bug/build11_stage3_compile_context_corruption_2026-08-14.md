# Build11 Stage 3 CompileContext corruption after clean parse

## Status

Open. This blocks an admitted self-hosted compiler deployment and therefore
blocks the compiler/loader performance rows that reject Rust-seed evidence.

## Reproduction

From a strict, provenance-recorded Build11 bootstrap, Stage 2 reports:

`Build complete: 845 compiled, 0 cached, 0 failed`

The admitted Stage 2 compiler then parses all 603 Stage 3 closure files with
zero failures and exits 139 before the first HIR progress row. The canonical
recovery command reproduces the same terminal result.

## Evidence

GDB resolves the crash to:

`CompileContext.error_count -> CompilerDriver.lower_and_check_impl -> CompilerDriver.compile`

The Stage 3 log is empty and the diagnostic immediately after the first
`self.ctx.error_count()` call never prints. Replacing getter calls in the
driver with direct `error_count_value` reads did not change the terminal
result, proving the getter frame is a symptom rather than the root cause; that
unproven workaround was removed.

An earlier parser blocker in
`compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl` was independently
fixed with required parentheses around a multiline boolean. Both subsequent
cycles parsed all 603 files, so this context corruption is the remaining
blocker.

## Unblock condition

Produce one admitted Stage 3 candidate that passes provenance and frontend
sanity, deploy the full pure-Simple CLI, then run the focused loader SPipe gate,
C provider self-check, optimizer audit, and retained failed-probe/latency/RSS
measurement exactly once.

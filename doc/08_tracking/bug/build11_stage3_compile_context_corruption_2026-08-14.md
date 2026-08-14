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
`self.ctx.error_count()` call never prints. In this fresh lane, replacing getter
calls in the driver with direct `error_count_value` reads did not change the
terminal result, so that unproven workaround was removed. This does not
invalidate the earlier `3c26d1b9c2f` observation that direct scalar reads
advanced a different Stage3 run into HIR; the current failure frontier is
earlier and must be localized independently.

An earlier parser blocker in
`compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl` was independently
fixed with required parentheses around a multiline boolean. Both subsequent
cycles parsed all 603 files, so this context corruption is the remaining
blocker.

## Unblock condition

Resume the preserved admitted lineage with:

`sh scripts/bootstrap/resume-stage3-from-admitted.sh build/restart12-build11-a-r2/output`

Retain the Stage2/Stage3 build logs, command transcripts, sanity/provenance
manifests, candidate hashes, and the focused GDB backtrace. Add primitive-only
canaries at `lower_and_check_impl` entry, after the `source_path_map` loop, and
immediately before/after `module_surfaces_from_modules`; if corruption crosses
that call, capture its MIR/native IR and add an adjacent aggregate-return/copy
regression. Do not retry getter-only edits without new localization evidence.

Produce one admitted Stage 3 candidate that passes provenance and frontend
sanity, deploy the full pure-Simple CLI, then run the focused loader SPipe gate,
C provider self-check, optimizer audit, and retained failed-probe/latency/RSS
measurement exactly once.

## Bounded lane-A localization result

Three recovery cycles were consumed without producing an admitted candidate.
The first reproduced exit 139. The second enabled `SIMPLE_INTERP_TRACE=1`, but
the provenance wrapper intentionally reconstructs the Stage 3 environment and
did not admit that variable. The final cycle used unconditional primitive-only
entry, post-source-map, pre-surface, and post-surface canaries in
`lower_and_check_impl`; Stage 3 again exited 139 and its retained native-build
log remained empty. The diagnostic canaries were removed after the run.

This result does **not** prove that `module_surfaces_from_modules` is the active
frontier: no `lower_and_check_impl` entry canary was observed. Resume work must
first establish whether control reaches that method under a trace-preserving
provenance command or debugger breakpoint, then inspect the aggregate call only
if the entry/source-map canaries execute. The three-cycle cap is exhausted for
this lane; do not repeat the same recovery command without a new instrumented
or debugger-backed localization strategy.

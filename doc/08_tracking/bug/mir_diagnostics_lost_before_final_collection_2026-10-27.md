# MIR causes lost when a build stops before final collection

The retained direct phase-3 attempt at
`/tmp/simple-luna-direct-phase3-20261027/attempt4` reached 640/1589 modules,
with 630 successes and 10 failures, before RSS containment exited with 89.
The loop can retain fatal messages in `MirLowering.errors` until
`_driver_collect_mir_errors` after the entire schedule. The retained log does
not identify those ten causes. Its per-module
trace was disabled without `SIMPLE_COMPILER_PHASE_PROFILE=1`.

The reporting owner now emits one unconditional, explicitly flushed stdout
summary for each newly recorded fatal MIR error range. Severity uses the same
explicit-fatal OR legacy-message classifier as final collection. Module, path
and first message are bounded ASCII previews (192, 256 and 768 bytes, plus
truncation markers); the summary includes the total new fatal count. Existing
opt-in profile tracing retains its complete diagnostic items. Original messages and final
aggregation remain unchanged; no compilation policy or success decision changes.

This covers `MirError` entries at existing per-module trace calls. Context-only
errors added later, failures inside lowering before it returns, and parent
relay buffering are outside this narrow fix. Full messages remain in memory
until ordinary final collection; the summary is not a new durable receipt or a
promise that every diagnostic survives a host crash. Existing ICE receipts
retain their existing configuration and semantics.

The focused spec is `test/01_unit/compiler/driver/mir_immediate_diagnostic_spec.spl`.
The native fixture calls the actual reporting owner, then stays in later work;
`scripts/check/check-mir-immediate-diagnostic.py` must observe redirected stdout
with profiling off before killing the process. Normal exit would mask a
missing flush. No full phase-3 rerun is necessary for this bounded check.

Independent source review found no P0/P1 after preserving the opt-in profile
items. Static checks passed for the unchanged legacy classifier and final
collector, immediate call ordering, Python harness syntax, and the working
environment-facade guard. These are not native execution evidence.

The single native fixture compilation using producer
`8d21317328ccb2b32ba707d2485c3c8ca6c4d02592952537e7754a6d006cb116`
stopped during source loading with exit 88 (`rss-cap-exceeded`): peak
4,317,460 KiB against a 4,194,304 KiB cap. No executable was produced and no
retry was made. The retained directory
`/tmp/simple-mir-diagnostic-retention-evidence-20261027` contains the compiler
argv, source/runtime/producer hashes, log and RSS receipt. The output-retention
test for that full-owner fixture is **UNRUN**, not a native red-to-green result.

A distinct presentation-only fixture (`preview.spl` beside `main.spl`) imports
the shared production formatter leaf and actual `log_error_flushed` owner,
without importing `MirError` and its full lowering graph. The driver calls
this same formatter after selecting the first message and count. This reduced
the selected closure from 521 to 69 modules. Its bounded compile succeeded;
the executable SHA-256 is
`62f16919d0a8051072efd6024929beff15b8205695a3011eebd43cd49ba3831a`.

The harness ran with `--scope presentation-only`, observed exactly one summary
in redirected stdout while the process was still running, then killed it
(exit -9). Profiling was off. It also reached the emission after native
assertions for control-character sanitation, truncation and zero-count
suppression. This **PASS** proves the shared presentation and explicit flush,
not the full owner's range/count/classification behavior. Those executable
checks remain **UNRUN**. Evidence, selected closure and source/runtime/producer
hashes are retained at `/tmp/simple-mir-diagnostic-preview-evidence-20261027`.
The [committed evidence summary](mir_diagnostics_lost_before_final_collection_2026-10-27.evidence.sdn)
includes those identities, actual stdout and both bounded attempt outcomes.

The available bootstrap-only CLI cannot run the unit/core/MCP verification
gates; those remain **UNRUN**. No full compiler rebuild or phase-3 admission
was performed. Resume the remaining owner and unit/core/MCP gates with a
qualified runner; do not repeat the passing presentation test or the unchanged
failed full-owner command.

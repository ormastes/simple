# H1 (streaming source reclaim) experiment — IN FLIGHT (earlier 'died' reading RETRACTED)

**Date:** 2026-09-03  **Status:** running

> **RETRACTION.** An earlier revision of this file said the run 'died silently
> at 18:25, likely OOM'. That was wrong. The worker (pid 19462) was in state `R`
> with 70 minutes of CPU and a saturated core the entire time. The false reading
> came from `bootstrap-progress.log` reporting `tree_processes=0 / cpu_pct=0.0`
> for a healthy run, plus polling a log path the compiler never writes. See
> [bootstrap_progress_monitor_reports_live_run_as_dead_2026-09-03.md]. The OOM
> hypothesis below is withdrawn; no memory pressure was ever demonstrated.

## What was tested

PR #351 added `SIMPLE_KEEP_SOURCE_CONTENTS` (default OFF), gating the
unconditional streaming source reclaim at
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:414-418`. Hypothesis
H1: that reclaim is what leaves `current_module_id` empty at the ZeroKind raise
site, because the non-streaming path gates the same reclaim on
`if source_contents_reclaimable() and not streaming`
(`driver_orchestration.spl:181`) while the streaming path — the one Stage 3 uses
— does not.

Pre-registered reading: *fatals gone => the reclaim is implicated; unchanged =>
it is not.*

## Result: NEITHER. The run never reached the phase under test.

Stage 3 started 18:13:26 and died silently at 18:25:48, at the phase2->phase3
boundary, having just finished the last surface file (`seq=763`,
`src/compiler/driver/pipeline_fn.spl`). No error text, no exit message.

The log shows `zerokind=0` and `hir-fatals=0`. **Both are meaningless here.**
ZeroKind is raised during HIR lowering in phase 3+; a run that stopped at the end
of phase 2 could not have produced one no matter what the flag did. This is the
same trap that produced the retraction in PR #322 — a zero count cited from a run
that died early. The guard established there applies and was applied: *report how
far the run got, alongside any count.*

Confirming the flag never even took effect: the gate's own log line
`phase3:streaming_source_reclaim:SKIPPED` appears **0 times**, because it is
emitted in phase 3.

## The experiment plausibly caused the death

`SIMPLE_KEEP_SOURCE_CONTENTS=1` retains all 763 files' source text instead of
releasing it, so peak RSS is maximal precisely at the phase2->phase3 boundary
where the process vanished. A silent death with no diagnostic is what a SIGKILL
looks like.

This is **not confirmed**: the progress sampler recorded `rss_kb=0`,
`tree_rss_kb=0`, `top_rss_kb=0` for every sample of the run, so there is no
memory evidence in either direction. `log show --predicate 'eventMessage CONTAINS
"memorystatus"'` returned nothing for the window. Treat OOM as the leading
suspect, not a finding.

## Secondary defect found: the progress monitor reports a dead run as alive

`build/bootstrap/bootstrap-progress.log` kept emitting
`status=alive-no-progress ... terminal=running` for **65 minutes** after the
worker was gone, with `stall_streak` climbing to 155 and
`tree_processes=0 / cpu_pct=0.0 / rss_kb=0` on every sample. It tracks the
wrapper shell's pid, so a dead worker under a live wrapper reads as "running".
`tree_processes=0` for a sustained streak should be terminal, not `alive`.

## Log location trap (cost ~1h of blind polling)

The stage-3 compiler writes its stderr to
`build/bootstrap/stage3/<triple>/stage3-tmp/simple_err_<pid>_<ts>.txt`, **not**
`stage3-native-build.log` and not `native-build-stderr-*.log`. Polling for the
latter reported "no log yet" while a 507KB log had existed since 18:20. The
`chain.sh` verdict block now reads the correct path and prints the last phase and
last `hir N/760` reached.

## Next

H1 is untested, not refuted. Re-testing it requires either a lower-memory
variant (retain sources for a subset, or retain only the span/module fields the
raise site needs) or more RAM headroom. Until then the pre-registered alternative
— the ragged parallel arrays at `lowering_helpers.spl:230-320` — is the front
hypothesis, on the independent evidence that `current_module_id` has exactly one
writer (`module_lowering.spl:1151`, inside `lower_module`), so an empty value
proves `lower_module` never ran on that instance.

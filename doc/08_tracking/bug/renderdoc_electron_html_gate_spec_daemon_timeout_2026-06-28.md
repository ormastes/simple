# RenderDoc Electron HTML Gate SSpec Daemon Timeout

Date: 2026-06-28

## Summary

`test/03_system/check/renderdoc_electron_html_gate_spec.spl` times out under the
current SPipe test daemon on this host, even though the direct shell gate
completes quickly. Do not rerun the same SSpec repeatedly in one session; use
direct gate evidence while this daemon issue is open.

## Observed Command

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/renderdoc_electron_html_gate_spec.spl --mode=interpreter --clean --fail-fast
```

Observed result:

```text
ERROR: test daemon timed out: test/03_system/check/renderdoc_electron_html_gate_spec.spl
```

## Current Direct Evidence

The direct aggregate completes and reports:

```text
gui_showcase_4k_200fps_status=pass
gui_showcase_8k_perf_status=pass
electron_renderdoc_gate_launch_metadata_status=missing
electron_renderdoc_gate_launch_metadata_reason=missing-launch-exit-metadata
electron_renderdoc_gate_source_contract_status=stale
electron_renderdoc_gate_source_contract_reason=stale-source-missing-launch-exit-metadata
```

## Required Fix

Split the SSpec or fix the daemon profile so the scenario file can finish
without timing out. Until then, completion claims for the Electron RenderDoc
gate must rely on direct gate evidence plus this bug note, not repeated SSpec
reruns.

## Re-triage 2026-08-17 (m9a_tests lane)

**Verdict: the "daemon timeout" is explained by the specs own structure — it
is a cost problem, not a hang, and not a silent-wrong-result bug.**

`test/03_system/check/renderdoc_electron_html_gate_spec.spl` runs whole check
scripts from inside its examples, via a locally-declared
`extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)`
(line 137):

- line 149: `rt_process_run("/bin/cat", [path])`
- lines 162-163: `rm -rf build/test-renderdoc-electron-html-gate && ... sh scripts/check/check-renderdoc-electron-html-gate.shs || true`
- lines 229-230: a second, larger fixture-synthesising invocation of the same gate

So each example forks a shell that re-runs the full gate script, on top of the
~310s fixed session setup the daemon already pays. "The direct gate completes
quickly" and "the spec times out under the daemon" are therefore consistent
with each other and with no defect: the spec does strictly more work than the
gate does.

Two of the four claims in the original report are also independently suspect
per the session brief: `SIMPLE_TIMEOUT_SECONDS` was parsed and discarded until
`a034851236d` and still misbehaves, and a mis-thresholded
`kill_simple_monitor.shs` was SIGTERMing healthy specs. This doc predates both.

**Not re-measured to a `Results:` line from this lane.** Attempts under a host
load average of 81-133 were SIGTERMed at rc=143 with no `Results:` line, which
per the brief is UNVERIFIED rather than failed. Re-measure on a quiet host with
an explicit `--timeout`, never `SIMPLE_TIMEOUT_SECONDS`, before closing.

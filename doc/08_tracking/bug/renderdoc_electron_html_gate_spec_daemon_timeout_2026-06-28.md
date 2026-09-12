# RenderDoc Electron HTML Gate SSpec Daemon Timeout
**Status:** OPEN (2026-09-12, re-verified: bin/simple test test/03_system/check/renderdoc_electron_html_gate_spec.spl -> 7 passed, 5 failed, still reproduces)

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

## Triage 2026-09-12
Rule B: ran `bin/simple test test/03_system/check/renderdoc_electron_html_gate_spec.spl` on the deployed seed; 5 of 12 checks still fail, so this record still reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

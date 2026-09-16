# RenderDoc Electron HTML Gate SSpec Daemon Timeout

## Triage note 2026-09-13 — could not verify: the spec runner is broken on this host
- **measured** (Windows Rust seed v1.0.0-rc.1): `bin/simple test` is non-functional here — a 3-line 1-assertion spec returns in under a second with `WARNING: test daemon unavailable; running directly`, `error: test-runner: code -1 (process_run_bounded killed the child at its budget)` and a false `reason=outer-bound-timeout budget_ms=930000`. Seven real specs produced byte-identical verdicts.
- **inferred**: every runner-behaviour claim in this entry (example counts, PASS/FAIL bookkeeping, daemon timeouts) is therefore unverifiable here; a green or red from this host would be meaningless either way.
- **inferred**: left OPEN, not stale — the referenced spec files all still exist.

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

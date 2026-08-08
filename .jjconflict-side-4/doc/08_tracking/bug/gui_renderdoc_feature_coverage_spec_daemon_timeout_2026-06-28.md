# GUI RenderDoc Feature Coverage SSpec Daemon Timeout

Date: 2026-06-28
Status: open-long-profile
Owner: rendering verification lane

## Summary

`test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl` timed out
under the SPipe test daemon during a focused verification pass for Electron
RenderDoc launch diagnostics.

## Evidence

Command:

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl \
  --mode=interpreter --clean --fail-fast
```

Observed output:

```text
ERROR: test daemon timed out: test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl
```

The same verification pass showed:

- `test/03_system/check/renderdoc_electron_html_gate_spec.spl`: PASS, 11 examples.
- `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`: completed
  and forwarded the Electron gate launch fields plus GPU process exit fields.
- `sh scripts/audit/direct-env-runtime-guard.shs --working`: PASS.

## Impact

The script-level aggregate evidence is available, but repeated nested gate
setup in the SSpec wrapper made the full spec unreliable on this host.

## Next Step

`scripts/check/check-gui-renderdoc-feature-coverage-status.shs` now enables its
fingerprinted nested-gate cache by default under
`build/gui-renderdoc-feature-coverage-static-cache`. The wrapper itself was
measured at about 1.4 seconds on this host after the cache change, so the
remaining timeout belongs to the historical exhaustive SSpec matrix profile, not
to the aggregate wrapper.

`test/03_system/check/gui_renderdoc_feature_coverage_fast_gate_spec.spl` is the
intended bounded normal-lane check for the wrapper contract, but it is still not
fully reliable under the current test daemon. It passed once with 1 example in
`45026ms`, then timed out in a later focused run after Electron launch metadata
forwarding was added.

The direct wrapper remains usable verification evidence. On 2026-06-28 it
completed in about `25.60s` and emitted:

- `electron_renderdoc_gate_launch_metadata_status=missing`
- `electron_renderdoc_gate_launch_metadata_reason=missing-launch-exit-metadata`
- `gui_widget_renderdoc_goal_electron_gate_launch_metadata_status=missing`
- `gui_widget_renderdoc_goal_electron_gate_launch_metadata_reason=missing-launch-exit-metadata`

The exhaustive matrix spec still requires either a long timeout profile, as
documented in
`doc/09_report/gui_renderdoc_aggregate_sspec_perf_2026-06-25.md`, or future
sharding into smaller scenario files. The fast gate also needs sharding or a
daemon timeout classification fix before it can be treated as always-green
release evidence.

Follow-up evidence: removing the fast gate's explicit deletion of
`build/gui-renderdoc-feature-coverage-static-cache` was not sufficient to make
the SSpec reliable under the current daemon; the focused fast-gate SSpec still
timed out. Keep the cache-preserving behavior because it avoids deliberate cold
nested-gate refreshes, but do not claim the SSpec timeout is fixed until the
gate is split further or the daemon profile is corrected.

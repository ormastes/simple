# Linux Vulkan RenderDoc Reason Forwarding SSpec Daemon Timeout

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Date: 2026-06-28

## Summary

`test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl` times
out under the current SPipe test daemon on this host, even though the direct
aggregate evidence check completes quickly. Do not rerun this SSpec repeatedly
in one session.

## Observed Command

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl --mode=interpreter --clean --fail-fast
```

Observed result:

```text
ERROR: test daemon timed out: test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl
```

## Direct Evidence

The direct aggregate now forwards:

```text
linux_vulkan_render_log_compare_blocked_gate_count=2
linux_vulkan_render_log_compare_blocked_gates=renderdoc-chrome-rdc,renderdoc-electron-rdc
linux_vulkan_render_log_compare_renderdoc_chrome_reason=chromium-gpu-process-crashed-under-renderdoc
linux_vulkan_render_log_compare_renderdoc_electron_reason=missing-rdc
gui_showcase_4k_200fps_status=pass
gui_showcase_8k_perf_status=pass
```

## Required Fix

Fix the SPipe daemon profile or split this focused static-forwarding scenario so
it can complete reliably. Until then, use the direct aggregate evidence for this
specific forwarding contract and keep the broader Linux RenderDoc gate
incomplete until Chrome and Electron `.rdc` artifacts have `RDOC` magic.

## Re-triage 2026-08-17 (m9a_tests lane)

**Verdict: timeout evidence is stale and structurally suspect; not re-measured.**

`test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl` reads
check scripts as data rather than forking them (line 126
`file_read("scripts/check/check-linux-vulkan-render-log-compare.shs")`, line 134
`file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")`),
so unlike its sibling `renderdoc_electron_html_gate_spec.spl` it does **not**
re-run whole gates from inside its examples. That removes the obvious cost
explanation and makes a genuine 2026-06-28 timeout less likely to still hold.

The original evidence predates both known false-timeout sources named in the
session brief: `SIMPLE_TIMEOUT_SECONDS` being parsed and discarded until
`a034851236d`, and the mis-thresholded `kill_simple_monitor.shs` that SIGTERMed
specs at `MIN_AGE_SECS=60` — below a normal specs ~115s runtime.

**Not re-measured to a `Results:` line from this lane** (host load average
81-133; runs were SIGTERMed at rc=143 with no `Results:` line = UNVERIFIED, not
failed). Re-run on a quiet host with an explicit `--timeout` before closing.

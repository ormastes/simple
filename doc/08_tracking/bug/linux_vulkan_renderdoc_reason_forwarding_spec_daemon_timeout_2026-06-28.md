# Linux Vulkan RenderDoc Reason Forwarding SSpec Daemon Timeout

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12
The record itself warns not to rerun this SSpec repeatedly in one session, so it was not re-run; older than 45 days. Closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

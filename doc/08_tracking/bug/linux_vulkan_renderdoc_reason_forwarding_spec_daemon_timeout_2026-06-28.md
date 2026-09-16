# Linux Vulkan RenderDoc Reason Forwarding SSpec Daemon Timeout

## Triage note 2026-09-13 — could not verify: the spec runner is broken on this host
- **measured** (Windows Rust seed v1.0.0-rc.1): `bin/simple test` is non-functional here — a 3-line 1-assertion spec returns in under a second with `WARNING: test daemon unavailable; running directly`, `error: test-runner: code -1 (process_run_bounded killed the child at its budget)` and a false `reason=outer-bound-timeout budget_ms=930000`. Seven real specs produced byte-identical verdicts.
- **inferred**: every runner-behaviour claim in this entry (example counts, PASS/FAIL bookkeeping, daemon timeouts) is therefore unverifiable here; a green or red from this host would be meaningless either way.
- **inferred**: left OPEN, not stale — the referenced spec files all still exist.

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

# Linux Vulkan RenderDoc Reason Forwarding SSpec Daemon Timeout

Date: 2026-06-28

## Status

STALE ASSERTION FIXED / DAEMON VERIFICATION PENDING.

The stale forwarding assertion now checks the current lookup components: raw
external-host reason, capture reason, and the generic gate fallback. This
repairs the stale source assertion only. It does not prove the lookup's runtime
precedence and it does not resolve or explain the historical daemon timeout.

The timeout report predates the `SIMPLE_TIMEOUT_SECONDS` handling fix, but that
chronology is not evidence that the ignored environment budget caused this
specific timeout.

## Observed Command

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl --mode=interpreter --clean --fail-fast
```

Non-authoritative seed result (2026-09-21):

```text
PASS test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl
Duration: 257ms
```

The available `bin/simple` identifies itself as a Rust bootstrap seed. This
result preserves the red-to-green evidence but cannot close the bug under the
pure-Simple runtime policy.

Original daemon observation (2026-06-28):

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

## Scope

Run the focused command with an admitted pure-Simple self-hosted binary and
record a passing daemon result before closing this bug. The broader Linux
RenderDoc gate remains incomplete until Chrome and Electron `.rdc` artifacts
have `RDOC` magic.

## TODO: Deferred Verification

- On Linux/aarch64, after an admitted pure-Simple Stage 2 or Stage 3 CLI is
  available, run the focused command above through the session daemon with an
  explicit `--timeout` and with `SIMPLE_TIMEOUT_SECONDS` set to a distinct
  larger value. Record binary path, SHA-256, stage/provenance, elapsed time, and
  daemon verdict. This is the required test for this timeout bug.
- The GPU-free behavioral fixture is now
  `test/01_unit/scripts/linux_vulkan_renderdoc_reason_precedence_contract_test.shs`.
  It supplies distinct raw-capture, capture, and generic-gate reasons and proves
  raw wins, capture is the second fallback, and generic is last.
- On a prepared Linux Vulkan GUI host, run Chrome and Electron under the
  canonical RenderDoc wrapper and require both resulting capture files to have
  `RDOC` magic. This is broader platform completion evidence, not a prerequisite
  for closing the focused daemon-timeout verdict.

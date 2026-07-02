# Linux Vulkan Render Log Compare Current Status - 2026-07-02

## Result

Current default Linux Vulkan render-log comparison fails only on the browser
RenderDoc `.rdc` gates. The direct GUI/Web/2D Vulkan aggregate now exists and
passes Simple Vulkan, browser backing, ARGB source, and pairwise pixel
comparison gates. Chrome and Electron RenderDoc evidence files now exist, but
both browser GPU processes exit with code `139` under RenderDoc and emit no
`.rdc` artifact. Chrome's current crash stack includes `librenderdoc.so`.

## Command

```text
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

## Current Evidence

```text
linux_vulkan_render_log_compare_status=fail
linux_vulkan_render_log_compare_reason=renderdoc-chrome-fail;renderdoc-electron-fail
linux_vulkan_render_log_compare_blocked_gate_count=2
linux_vulkan_render_log_compare_blocked_gates=renderdoc-chrome-rdc,renderdoc-electron-rdc
linux_vulkan_render_log_compare_simple_vulkan_gate_status=pass
linux_vulkan_render_log_compare_browser_backing_gate_status=pass
linux_vulkan_render_log_compare_pairwise_gate_status=pass
linux_vulkan_render_log_compare_argb_source_gate_status=pass
linux_vulkan_render_log_compare_renderdoc_gate_status=fail
linux_vulkan_render_log_compare_gui_web_2d_vulkan_env=build/gui-web-2d-vulkan-env-run-current/evidence.env
linux_vulkan_render_log_compare_gui_web_2d_vulkan_env_file_status=pass
linux_vulkan_render_log_compare_pairwise_status=pass
linux_vulkan_render_log_compare_pairwise_mode=pairwise-argb-diff
linux_vulkan_render_log_compare_renderdoc_simple_status=pass
linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC
linux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=pass
linux_vulkan_render_log_compare_renderdoc_chrome_status=fail
linux_vulkan_render_log_compare_renderdoc_chrome_reason=chromium-gpu-process-segv-in-renderdoc
linux_vulkan_render_log_compare_renderdoc_chrome_gpu_process_exit_status=fail
linux_vulkan_render_log_compare_renderdoc_chrome_gpu_process_exit_count=6
linux_vulkan_render_log_compare_renderdoc_chrome_gpu_process_exit_codes=139
linux_vulkan_render_log_compare_renderdoc_chrome_gpu_process_exit_reason=gpu-process-segv-in-renderdoc
linux_vulkan_render_log_compare_renderdoc_chrome_gpu_process_exit_renderdoc_stack_status=fail
linux_vulkan_render_log_compare_renderdoc_chrome_gpu_process_exit_renderdoc_stack_count=6
linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=missing
linux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass
linux_vulkan_render_log_compare_renderdoc_electron_status=fail
linux_vulkan_render_log_compare_renderdoc_electron_reason=chromium-gpu-process-crashed-under-renderdoc
linux_vulkan_render_log_compare_renderdoc_electron_gpu_process_exit_status=fail
linux_vulkan_render_log_compare_renderdoc_electron_gpu_process_exit_count=6
linux_vulkan_render_log_compare_renderdoc_electron_gpu_process_exit_codes=139
linux_vulkan_render_log_compare_renderdoc_electron_gpu_process_exit_reason=gpu-process-exited-unexpectedly
linux_vulkan_render_log_compare_renderdoc_electron_gpu_process_exit_renderdoc_stack_status=pass
linux_vulkan_render_log_compare_renderdoc_electron_gpu_process_exit_renderdoc_stack_count=0
linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=missing
```

## Existing Artifacts Checked

- `build/gui-web-2d-vulkan-env-browser-backing/evidence.env`: present
- `build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/evidence.env`: present
- `build/renderdoc/canonical-probe/simple/evidence.env`: present
- `build/gui-web-2d-vulkan-env-run-current/evidence.env`: present
- `build/renderdoc/chrome-implicit-layer-default-autocapture/html/evidence.env`: present, no `.rdc`
- `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/evidence.env`: present, no `.rdc`

## Status

Do not use `doc/09_report/linux_vulkan_render_log_compare_2026-06-29.md` as
current completion proof on this workspace. Re-run the GUI/Web/2D Vulkan
aggregate and the Chrome/Electron RenderDoc capture lanes before claiming Linux
Vulkan RenderDoc parity is passing. As of this run, the direct aggregate passes;
the remaining work is the Chromium GPU-process crash under RenderDoc for Chrome
and Electron. Chrome now records the crash as a RenderDoc-library segfault;
Electron records the same exit code without stack frames in the wrapper log.

## No-Child-Hook Diagnostic

`RDOC_RENDERDOC_HOOK_CHILDREN=0` was tested as a diagnostic only:

```text
build/renderdoc/chrome-implicit-layer-no-child-hook-diagnostic/html/evidence.env
rdoc_chromium_gpu_process_exit_status=pass
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
rdoc_capture_magic=

build/renderdoc/electron-implicit-layer-no-child-hook-diagnostic/electron-html/evidence.env
rdoc_electron_launch_exit_code=124
rdoc_electron_launch_timed_out=true
rdoc_chromium_gpu_process_exit_status=pass
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
rdoc_capture_magic=
```

This isolates the default crash to RenderDoc child-process hooking, but it is
not passing evidence because neither browser emits a valid `RDOC` artifact.

Use the canonical paths consumed by
`scripts/check/check-linux-vulkan-render-log-compare.shs`:

```sh
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-browser-backing \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-renderdoc-simple \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple
RDOC_OUTPUT_DIR=build/renderdoc/chrome-implicit-layer-default-autocapture \
  scripts/tool/renderdoc-evidence.shs capture-html
RDOC_OUTPUT_DIR=build/renderdoc/electron-implicit-layer-default-autocapture \
  scripts/tool/renderdoc-evidence.shs capture-electron-html
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

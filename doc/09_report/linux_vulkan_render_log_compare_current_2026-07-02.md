# Linux Vulkan Render Log Compare Current Status - 2026-07-02

## Result

Current default Linux Vulkan render-log comparison is unavailable on this
workspace. The checker is reporting missing live aggregate and browser
RenderDoc evidence rather than reusing older report artifacts or synthetic test
fixtures.

## Command

```text
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

## Current Evidence

```text
linux_vulkan_render_log_compare_status=unavailable
linux_vulkan_render_log_compare_reason=missing-gui-web-2d-vulkan-env;renderdoc-chrome-unavailable;renderdoc-electron-unavailable
linux_vulkan_render_log_compare_blocked_gate_count=7
linux_vulkan_render_log_compare_blocked_gates=gui-web-2d-vulkan-env,simple-vulkan-backend,browser-vulkan-backing,pairwise-argb-diff,argb-source-evidence,renderdoc-chrome-rdc,renderdoc-electron-rdc
linux_vulkan_render_log_compare_simple_vulkan_gate_status=fail
linux_vulkan_render_log_compare_browser_backing_gate_status=fail
linux_vulkan_render_log_compare_pairwise_gate_status=fail
linux_vulkan_render_log_compare_argb_source_gate_status=fail
linux_vulkan_render_log_compare_renderdoc_gate_status=fail
linux_vulkan_render_log_compare_gui_web_2d_vulkan_env=build/gui-web-2d-vulkan-env-run-current/evidence.env
linux_vulkan_render_log_compare_gui_web_2d_vulkan_env_file_status=missing
linux_vulkan_render_log_compare_renderdoc_simple_status=pass
linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC
linux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=missing
linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=missing
linux_vulkan_render_log_compare_renderdoc_electron_env_file_status=missing
linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=missing
```

## Existing Artifacts Checked

- `build/gui-web-2d-vulkan-env-browser-backing/evidence.env`: present
- `build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/evidence.env`: present
- `build/renderdoc/canonical-probe/simple/evidence.env`: present
- `build/gui-web-2d-vulkan-env-run-current/evidence.env`: missing
- `build/renderdoc/chrome-implicit-layer-default-autocapture/html/evidence.env`: missing
- `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/evidence.env`: missing

## Status

Do not use `doc/09_report/linux_vulkan_render_log_compare_2026-06-29.md` as
current completion proof on this workspace. Re-run the GUI/Web/2D Vulkan
aggregate and the Chrome/Electron RenderDoc capture lanes before claiming Linux
Vulkan RenderDoc parity is passing.

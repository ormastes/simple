# Linux Vulkan Render Log Compare

Historical snapshot from 2026-06-25. This report is retained as failure
evidence for the old browser-backing state and must not be used as current
completion evidence. Use the active aggregate completion checklist and a fresh
`scripts/check/check-linux-vulkan-render-log-compare.shs` run on a prepared
Linux GUI/Vulkan/RenderDoc host for current proof.

- status: fail
- reason: electron-browser-backing-fail;browser-backing-fail
- aggregate evidence: build/gui-web-2d-vulkan-env/evidence.env
- simple log: build/linux-vulkan-render-log-compare-current/simple.srl.env
- chrome log: build/linux-vulkan-render-log-compare-current/chrome.srl.env
- electron log: build/linux-vulkan-render-log-compare-current/electron.srl.env
- compare log: build/linux-vulkan-render-log-compare-current/compare.srl.env

## Evidence
- linux_vulkan_render_log_compare_status=fail
- linux_vulkan_render_log_compare_reason=electron-browser-backing-fail;browser-backing-fail
- linux_vulkan_render_log_compare_platform=linux
- linux_vulkan_render_log_compare_required_api=vulkan
- linux_vulkan_render_log_compare_gui_web_2d_vulkan_env=build/gui-web-2d-vulkan-env/evidence.env
- linux_vulkan_render_log_compare_browser_backing_env=build/gui-web-2d-vulkan-env-browser-backing/evidence.env
- linux_vulkan_render_log_compare_simple_log=build/linux-vulkan-render-log-compare-current/simple.srl.env
- linux_vulkan_render_log_compare_chrome_log=build/linux-vulkan-render-log-compare-current/chrome.srl.env
- linux_vulkan_render_log_compare_electron_log=build/linux-vulkan-render-log-compare-current/electron.srl.env
- linux_vulkan_render_log_compare_compare_log=build/linux-vulkan-render-log-compare-current/compare.srl.env
- linux_vulkan_render_log_compare_pairwise_status=pass
- linux_vulkan_render_log_compare_pairwise_mode=pairwise-argb-diff
- linux_vulkan_render_log_compare_renderdoc_simple_status=pass
- linux_vulkan_render_log_compare_renderdoc_chrome_status=fail
- linux_vulkan_render_log_compare_renderdoc_electron_status=fail
- linux_vulkan_render_log_compare_require_renderdoc=0

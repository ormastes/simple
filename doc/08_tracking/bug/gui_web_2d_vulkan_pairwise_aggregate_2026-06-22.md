# GUI/Web/2D Vulkan Pairwise Aggregate Evidence

- Date: 2026-06-22
- Status: pass — strict pairwise pixel comparison passes
- Gate: `scripts/setup/setup-gui-web-2d-vulkan-env.shs --run`
- Evidence: `build/gui-web-2d-vulkan-env/evidence.env`

## Current Evidence

```text
gui_web_2d_vulkan_loader_status=present
gui_web_2d_vulkan_device=llvmpipe (LLVM 20.1.2, 256 bits)
gui_web_2d_vulkan_electron_argb_status=pass
gui_web_2d_vulkan_electron_argb_path=build/gui-web-2d-vulkan-env/electron_argb.json
gui_web_2d_vulkan_chrome_argb_status=pass
gui_web_2d_vulkan_chrome_argb_proof=build/gui-web-2d-vulkan-env/chrome_argb_proof.json
gui_web_2d_vulkan_simple_status=pass
gui_web_2d_vulkan_simple_backend_name=vulkan
gui_web_2d_vulkan_browser_backing_mode=gpu-feature-status
gui_web_2d_vulkan_electron_browser_backing_status=fail
gui_web_2d_vulkan_electron_browser_backing_reason=electron-vulkan-disabled_off
gui_web_2d_vulkan_electron_browser_backing_vulkan=disabled_off
gui_web_2d_vulkan_electron_browser_backing_hardware_supports_vulkan=false
gui_web_2d_vulkan_chrome_browser_backing_status=pass
gui_web_2d_vulkan_chrome_browser_backing_reason=chrome-vulkan-backed
gui_web_2d_vulkan_browser_backing_status=fail
gui_web_2d_vulkan_browser_backing_reason=electron-vulkan-disabled_off;chrome-vulkan-backed
gui_web_2d_vulkan_simple_argb_status=pass
gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=403594
gui_web_2d_vulkan_electron_chrome_diff_status=pass
gui_web_2d_vulkan_electron_chrome_mismatch_count=0
gui_web_2d_vulkan_electron_chrome_max_channel_delta=0
gui_web_2d_vulkan_electron_chrome_total_delta=0
gui_web_2d_vulkan_electron_chrome_bg_diff_count=0
gui_web_2d_vulkan_electron_chrome_text_diff_count=0
gui_web_2d_vulkan_electron_chrome_diff_bbox=none
gui_web_2d_vulkan_electron_chrome_diff_component_count=0
gui_web_2d_vulkan_electron_chrome_diff_top_components=
gui_web_2d_vulkan_electron_simple_diff_status=pass
gui_web_2d_vulkan_electron_simple_mismatch_count=0
gui_web_2d_vulkan_electron_simple_max_channel_delta=0
gui_web_2d_vulkan_electron_simple_total_delta=0
gui_web_2d_vulkan_electron_simple_bg_diff_count=0
gui_web_2d_vulkan_electron_simple_text_diff_count=0
gui_web_2d_vulkan_electron_simple_diff_bbox=none
gui_web_2d_vulkan_electron_simple_diff_component_count=0
gui_web_2d_vulkan_electron_simple_diff_top_components=
gui_web_2d_vulkan_chrome_simple_diff_status=pass
gui_web_2d_vulkan_chrome_simple_mismatch_count=0
gui_web_2d_vulkan_chrome_simple_max_channel_delta=0
gui_web_2d_vulkan_chrome_simple_total_delta=0
gui_web_2d_vulkan_chrome_simple_bg_diff_count=0
gui_web_2d_vulkan_chrome_simple_text_diff_count=0
gui_web_2d_vulkan_chrome_simple_diff_bbox=none
gui_web_2d_vulkan_chrome_simple_diff_component_count=0
gui_web_2d_vulkan_chrome_simple_diff_top_components=
gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=pass
gui_web_2d_vulkan_electron_simple_pairwise_diff_status=pass
gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=pass
gui_web_2d_vulkan_electron_simple_excess_over_browser_floor=0
gui_web_2d_vulkan_chrome_simple_excess_over_browser_floor=0
gui_web_2d_vulkan_simple_browser_floor_status=pass
gui_web_2d_vulkan_simple_browser_floor_reason=simple-has-no-excess-over-electron-chrome-drift
gui_web_2d_vulkan_pixel_comparison_status=pass
gui_web_2d_vulkan_pixel_comparison_reason=all-pairwise-diffs-pass
gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff
```

## Notes

Simple Vulkan Engine2D readback itself passes with exact clear/rect readback,
and the Simple HTML ARGB renderer now produces a full capture through Simple
facades instead of direct `rt_*` calls. The fixture is now boxes-only CSS
(`color: transparent`, native control appearance disabled), reducing
Electron/Chrome mismatch from `10656` to `232` and Simple/browser mismatch from
about `111918` to `232`/`226` after the measured fieldset/native-widget
geometry fills, transparent image witnesses, and browser-stable media/control
geometry patches, and squared header button corners. The strict aggregate now
passes with zero Electron/Chrome, Electron/Simple, and Chrome/Simple ARGB
mismatches. Browser backing remains a separate blocker: Chrome now proves Vulkan
backing through DevTools GPU info, but Electron reports `vulkan=disabled_off`
and `hardwareSupportsVulkan=false`. The aggregate remains fail-closed until
Electron also proves Vulkan/Metal backing.

## 2026-06-22 Native Probe Crash Cause

The native Simple ARGB probe crashed or logged
`function not found: Engine2D.is_err` when the browser presenter routed
`cpu_simd` through `Engine2D.create_requested_backend()` and then called
`Result.is_err()`. In the native compiled path that Result can dispatch as the
wrapped `Engine2D`, so the method lookup is invalid. The session plan is to keep
software, `cpu`, and `cpu_simd` aliases on the direct `cpu_mirror` path, leaving
real GPU backend requests on the existing Engine2D path. Verification evidence:
native probe exit `0`, `Engine2D.is_err` stderr count `0`, JSON pixels `768`,
and GUI/Web/2D Vulkan pairwise mismatches all `0`.

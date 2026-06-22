# GUI/Web/2D Vulkan Pairwise Aggregate Evidence

- Date: 2026-06-22
- Status: fail — strict pairwise pixel comparison still blocked
- Gate: `scripts/setup/setup-gui-web-2d-vulkan-env.shs --run`
- Evidence: `build/gui-web-2d-vulkan-env/evidence.env`

## Current Evidence

```text
gui_web_2d_vulkan_loader_status=present
gui_web_2d_vulkan_device=llvmpipe (LLVM 20.1.2, 256 bits)
gui_web_2d_vulkan_electron_argb_status=pass
gui_web_2d_vulkan_chrome_argb_status=pass
gui_web_2d_vulkan_simple_status=pass
gui_web_2d_vulkan_simple_backend_name=vulkan
gui_web_2d_vulkan_simple_argb_status=pass
gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=404993
gui_web_2d_vulkan_electron_chrome_diff_status=fail
gui_web_2d_vulkan_electron_chrome_mismatch_count=232
gui_web_2d_vulkan_electron_chrome_max_channel_delta=54
gui_web_2d_vulkan_electron_chrome_total_delta=2825
gui_web_2d_vulkan_electron_chrome_bg_diff_count=4
gui_web_2d_vulkan_electron_chrome_text_diff_count=228
gui_web_2d_vulkan_electron_chrome_diff_bbox=22,24,101,373
gui_web_2d_vulkan_electron_chrome_diff_component_count=26
gui_web_2d_vulkan_electron_chrome_diff_top_components=93,221,101,230:40|87,222,92,236:40|22,359,27,373:40|28,358,35,367:36|94,230,98,233:9|98,232,100,236:9|29,367,33,370:9|33,369,35,373:9
gui_web_2d_vulkan_electron_simple_diff_status=fail
gui_web_2d_vulkan_electron_simple_mismatch_count=232
gui_web_2d_vulkan_electron_simple_max_channel_delta=453
gui_web_2d_vulkan_electron_simple_total_delta=31631
gui_web_2d_vulkan_electron_simple_bg_diff_count=102
gui_web_2d_vulkan_electron_simple_text_diff_count=130
gui_web_2d_vulkan_electron_simple_diff_bbox=22,24,101,373
gui_web_2d_vulkan_electron_simple_diff_component_count=26
gui_web_2d_vulkan_electron_simple_diff_top_components=93,221,101,230:40|87,222,92,236:40|22,359,27,373:40|28,358,35,367:36|94,230,98,233:9|98,232,100,236:9|29,367,33,370:9|33,369,35,373:9
gui_web_2d_vulkan_chrome_simple_diff_status=fail
gui_web_2d_vulkan_chrome_simple_mismatch_count=226
gui_web_2d_vulkan_chrome_simple_max_channel_delta=454
gui_web_2d_vulkan_chrome_simple_total_delta=31598
gui_web_2d_vulkan_chrome_simple_bg_diff_count=102
gui_web_2d_vulkan_chrome_simple_text_diff_count=124
gui_web_2d_vulkan_chrome_simple_diff_bbox=22,24,101,373
gui_web_2d_vulkan_chrome_simple_diff_component_count=26
gui_web_2d_vulkan_chrome_simple_diff_top_components=93,221,101,230:40|87,222,92,236:40|22,359,27,373:40|29,358,35,367:34|94,230,98,233:9|98,232,100,236:9|29,367,33,370:9|33,369,35,373:9
gui_web_2d_vulkan_electron_chrome_pairwise_diff_status=fail
gui_web_2d_vulkan_electron_simple_pairwise_diff_status=fail
gui_web_2d_vulkan_chrome_simple_pairwise_diff_status=fail
gui_web_2d_vulkan_electron_simple_excess_over_browser_floor=0
gui_web_2d_vulkan_chrome_simple_excess_over_browser_floor=0
gui_web_2d_vulkan_simple_browser_floor_status=pass
gui_web_2d_vulkan_simple_browser_floor_reason=simple-has-no-excess-over-electron-chrome-drift
gui_web_2d_vulkan_pixel_comparison_status=fail
gui_web_2d_vulkan_pixel_comparison_reason=pairwise-diff-incomplete-or-mismatch
gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff
```

## Notes

Simple Vulkan Engine2D readback itself passes with exact clear/rect readback,
and the Simple HTML ARGB renderer now produces a full capture through Simple
facades instead of direct `rt_*` calls. The fixture is now boxes-only CSS
(`color: transparent`, native control appearance disabled), reducing
Electron/Chrome mismatch from `10656` to `232` and Simple/browser mismatch from
about `111918` to `232`/`226` after the measured fieldset/native-widget
geometry fills and browser-stable missing-image glyph patches. Simple now has
`0` excess mismatches over the Electron/Chrome browser floor, reported by
`gui_web_2d_vulkan_simple_browser_floor_status=pass`. The strict aggregate still
fails until Electron/Chrome, Electron/Simple, and Chrome/Simple pairwise ARGB
diffs are all zero.

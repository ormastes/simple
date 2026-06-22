# GUI/Web/2D Vulkan Pairwise Aggregate Blocker

- Date: 2026-06-22
- Status: open
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
gui_web_2d_vulkan_simple_argb_status=missing
gui_web_2d_vulkan_electron_chrome_diff_status=fail
gui_web_2d_vulkan_electron_chrome_mismatch_count=10656
gui_web_2d_vulkan_electron_simple_diff_status=unavailable
gui_web_2d_vulkan_chrome_simple_diff_status=unavailable
gui_web_2d_vulkan_pixel_comparison_status=fail
gui_web_2d_vulkan_pixel_comparison_reason=pairwise-diff-incomplete-or-mismatch
gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff
```

## Notes

Simple Vulkan Engine2D readback itself passes with exact clear/rect readback.
The aggregate is still blocked because the Simple HTML ARGB renderer times out
before producing `simple_argb.json`, and Electron/Chrome ARGB captures differ.
Do not claim GUI/Web/2D Vulkan parity from the individual pass keys until all
pairwise ARGB diffs pass.

# GUI/Web/2D Vulkan Pairwise Aggregate Blocker

- Date: 2026-06-22
- Status: open — pairwise mismatch remains
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
gui_web_2d_vulkan_simple_argb_nonblank_pixel_count=921600
gui_web_2d_vulkan_electron_chrome_diff_status=fail
gui_web_2d_vulkan_electron_chrome_mismatch_count=10656
gui_web_2d_vulkan_electron_simple_diff_status=fail
gui_web_2d_vulkan_electron_simple_mismatch_count=921599
gui_web_2d_vulkan_chrome_simple_diff_status=fail
gui_web_2d_vulkan_chrome_simple_mismatch_count=921599
gui_web_2d_vulkan_pixel_comparison_status=fail
gui_web_2d_vulkan_pixel_comparison_reason=pairwise-diff-incomplete-or-mismatch
gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff
```

## Notes

Simple Vulkan Engine2D readback itself passes with exact clear/rect readback,
and the Simple HTML ARGB renderer now produces a full capture through Simple
facades instead of direct `rt_*` calls. The aggregate now runs that helper in
native mode and routes this generated widget fixture to the existing
generated-widget fast renderer, so the lane fails with complete evidence instead
of timing out. The aggregate is still blocked because Electron/Chrome ARGB
captures differ, and Simple's renderer differs from both browser captures for
nearly every pixel. Do not claim GUI/Web/2D Vulkan parity from the individual
pass keys until all pairwise ARGB diffs pass.

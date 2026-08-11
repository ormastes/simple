# macOS Vulkan 2D Live Evidence

- status: fail
- reason: runtime-backend-create-failed
- selected driver: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/macos_vulkan_2d_live_harness_direct_probe_ld_new`
- selected driver kind: pure-simple-native-output
- runtime receipt: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-direct-probe-ld-new/runtime_receipt.env`
- 4K/300-DPI framebuffer: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-direct-probe-ld-new/vulkan_3840x2160_300dpi.png`
- exact window before input: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-direct-probe-ld-new/window_before.png`
- exact window after input: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-direct-probe-ld-new/window_after.png`
- launcher stdout: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-direct-probe-ld-new/launch.out`
- launcher stderr: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-direct-probe-ld-new/launch.err`

## Validated evidence

```text
macos_vulkan_2d_live_status=fail
macos_vulkan_2d_live_reason=runtime-backend-create-failed
macos_vulkan_2d_live_driver_kind=pure-simple-native-output
macos_vulkan_2d_live_driver_path=/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/macos_vulkan_2d_live_harness_direct_probe_ld_new
```

## Runtime receipt

```text
gpu_2d_live_status=fail
gpu_2d_live_reason=backend-create-failed
gpu_2d_live_requested_backend=vulkan
gpu_2d_live_selected_backend=cpu
gpu_2d_live_probe=Vulkan shared session initialization failed: 0
```

# macOS Vulkan 2D Live Evidence

- status: fail
- reason: launched-process-missing
- selected driver: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/macos_vulkan_2d_live_harness_raw_abi_manual2`
- selected driver kind: pure-simple-native-output
- runtime receipt: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-raw-abi-manual2/runtime_receipt.env`
- 4K/300-DPI framebuffer: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-raw-abi-manual2/vulkan_3840x2160_300dpi.png`
- exact window before input: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-raw-abi-manual2/window_before.png`
- exact window after input: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-raw-abi-manual2/window_after.png`
- launcher stdout: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-raw-abi-manual2/launch.out`
- launcher stderr: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-raw-abi-manual2/launch.err`

## Diagnosis

- The process aborted in `spirv_reflect.c:310` while creating a compute
  pipeline; no framebuffer, window, capture, or event receipt was produced.
- The provider exported and the artifact referenced the raw SPIR-V,
  push-constant, upload, and download APIs.
- `spirv-val` accepted the eight Engine2D source modules used by the session
  (`noop`, clear, filled/outline rectangle, circle, triangle, gradient, blit).
- The follow-up implementation replaces the aborting C reflection call with a
  bounds-checked Rust scan of SPIR-V `OpDecorate ... Binding` instructions.
  That change remains unverified until the next bounded session.

## Validated evidence

```text
macos_vulkan_2d_live_status=fail
macos_vulkan_2d_live_reason=launched-process-missing
macos_vulkan_2d_live_driver_kind=pure-simple-native-output
macos_vulkan_2d_live_driver_path=/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/macos_vulkan_2d_live_harness_raw_abi_manual2
```

# macOS Vulkan 2D Live Evidence

- status: fail
- reason: runtime-provider-not-linked
- selected driver: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/macos_vulkan_2d_live_harness_font_concat`
- selected driver kind: pure-simple-native-output
- runtime receipt: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-font-concat/runtime_receipt.env`
- 4K/300-DPI framebuffer: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-font-concat/vulkan_3840x2160_300dpi.png`
- exact window before input: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-font-concat/window_before.png`
- exact window after input: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-font-concat/window_after.png`
- launcher stdout: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-font-concat/launch.out`
- launcher stderr: `/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/live-font-concat/launch.err`

## Validated evidence

```text
macos_vulkan_2d_live_status=fail
macos_vulkan_2d_live_reason=runtime-provider-not-linked
macos_vulkan_2d_live_driver_kind=pure-simple-native-output
macos_vulkan_2d_live_driver_path=/Users/ormastes/simple/build/worktrees/render_lane_origin_main/build/native_probe/macos-vulkan-2d-4k-300/macos_vulkan_2d_live_harness_font_concat
```

## Root-cause evidence

- Vulkan validation layers identified the previously submitted font module as
  malformed at SPIR-V word 1966.
- LLDB captured the eleventh raw compile call (the vector-font module) from
  the retained harness. Its SHA-256 was
  `111e3594678fc9d24c2d9dfb56c79ed8384e17731a909e8047a1700334baaeef`;
  `spirv-val` reproduced the truncated `OpTypeOpaque` failure.
- Native byte iteration returns raw `u8`, while generic `array.push` receives a
  tagged integer ABI. The former head/tail append loop therefore corrupted
  tail bytes divisible by eight.
- Replacing the loop with the core byte-array concat produced an exact
  provider-boundary module of 10,884 bytes with pinned SHA-256
  `ca5a3d644e5d4dd1c3b6d453be4db252f8ed7b9d65b78e2f7ae37c17769dc55d`.
  That exact captured module passes `spirv-val`.

## Remaining blocker

The fresh pure-Simple native closure is not admissible to the strict wrapper
because its default link uses dynamic lookup instead of recording the three
runtime-provider dylibs. Diagnostic injection reaches rendering but traps in
`VulkanBackend.clear` with a nil receiver; LLDB records the stack as
`VulkanBackend.clear -> Engine2D.clear -> run_macos_gpu_2d_live_harness`.
The focused Simple spec runner is independently blocked before executing this
spec by its existing unresolved `rt_process_run_bounded` extern.
The strict 4K/300-DPI capture and event gate therefore remains unproven.

# macOS Metal 2D Live Evidence

- status: fail
- reason: runtime-backend-create-failed
- selected driver: `build/macos_gpu_2d_live_native/metal/macos_metal_2d_live_native`
- selected driver kind: trusted-self-hosted-native-output
- trusted build manifest: `build/macos_gpu_2d_live_native/metal/trusted-build.env`
- runtime receipt: `build/wm-current-live/metal-probe/runtime_receipt.env`
- 4K/300-DPI framebuffer: not produced due to fail-closed result
- exact window before input: not produced due to fail-closed result
- exact window after input: not produced due to fail-closed result
- launcher stdout: `build/wm-current-live/metal-probe/launch.out`
- launcher stderr: `build/wm-current-live/metal-probe/launch.err`

## Validated evidence

```text
macos_metal_2d_live_status=fail
macos_metal_2d_live_reason=runtime-backend-create-failed
macos_metal_2d_live_driver_kind=trusted-self-hosted-native-output
macos_metal_2d_live_driver_path=build/macos_gpu_2d_live_native/metal/macos_metal_2d_live_native
macos_metal_2d_live_trusted_build_manifest=build/macos_gpu_2d_live_native/metal/trusted-build.env
```

## Runtime receipt

```text
gpu_2d_live_status=fail
gpu_2d_live_reason=backend-create-failed
gpu_2d_live_requested_backend=metal
gpu_2d_live_selected_backend=cpu
gpu_2d_live_probe=Metal shader compilation failed
```

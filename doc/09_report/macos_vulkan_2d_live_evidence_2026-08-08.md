# macOS Vulkan 2D Live Evidence

- status: fail
- reason: runtime-processing-ir-receipt-failed
- selected driver: `/Users/ormastes/simple/build/macos_gpu_2d_live_native/vulkan/macos_vulkan_2d_live_native`
- selected driver kind: trusted-self-hosted-native-output
- trusted build manifest: `/Users/ormastes/simple/build/macos_gpu_2d_live_native/vulkan/trusted-build.env`
- MoltenVK ICD: `/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`
- MoltenVK ICD SHA-256: `b514f51690582fb783383154b7a33c7816cc47e98ee1a1f652dccd3e996f0bf1`
- MoltenVK library: `/opt/homebrew/lib/libMoltenVK.dylib`
- MoltenVK library SHA-256: `e1773b594b468796c6aacde6b8ec6f414315d94885c69122b56f45f3acebff93`
- MoltenVK preflight: device-driver-verified
- Vulkan device: Apple M4
- Vulkan driver: MoltenVK
- runtime receipt: `/Users/ormastes/simple/build/tmp/macos_vulkan_2d_live_evidence/runtime_receipt.env`
- 4K/300-DPI framebuffer: `/Users/ormastes/simple/build/tmp/macos_vulkan_2d_live_evidence/vulkan_3840x2160_300dpi.png`
- exact window before input: `/Users/ormastes/simple/build/tmp/macos_vulkan_2d_live_evidence/window_before.png`
- exact window after input: `/Users/ormastes/simple/build/tmp/macos_vulkan_2d_live_evidence/window_after.png`
- launcher stdout: `/Users/ormastes/simple/build/tmp/macos_vulkan_2d_live_evidence/launch.out`
- launcher stderr: `/Users/ormastes/simple/build/tmp/macos_vulkan_2d_live_evidence/launch.err`

## Validated evidence

```text
macos_vulkan_2d_live_status=fail
macos_vulkan_2d_live_reason=runtime-processing-ir-receipt-failed
macos_vulkan_2d_live_driver_kind=trusted-self-hosted-native-output
macos_vulkan_2d_live_driver_path=/Users/ormastes/simple/build/macos_gpu_2d_live_native/vulkan/macos_vulkan_2d_live_native
macos_vulkan_2d_live_trusted_build_manifest=/Users/ormastes/simple/build/macos_gpu_2d_live_native/vulkan/trusted-build.env
macos_vulkan_2d_live_moltenvk_icd_path=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json
macos_vulkan_2d_live_moltenvk_icd_sha256=b514f51690582fb783383154b7a33c7816cc47e98ee1a1f652dccd3e996f0bf1
macos_vulkan_2d_live_moltenvk_library_path=/opt/homebrew/lib/libMoltenVK.dylib
macos_vulkan_2d_live_moltenvk_library_sha256=e1773b594b468796c6aacde6b8ec6f414315d94885c69122b56f45f3acebff93
macos_vulkan_2d_live_moltenvk_preflight_status=device-driver-verified
```

## Runtime receipt

```text
gpu_2d_live_status=fail
gpu_2d_live_reason=processing-ir-receipt-failed
gpu_2d_live_backend=vulkan
gpu_2d_live_stage=4
gpu_2d_live_exit_code=4
gpu_2d_live_processing_ir_status=fail
gpu_2d_live_processing_ir_reason=vulkan-physical-device-required
gpu_2d_live_processing_ir_completed=false
gpu_2d_live_processing_ir_backend=vulkan
gpu_2d_live_processing_ir_count=0
gpu_2d_live_processing_ir_expected_checksum=1082179840
gpu_2d_live_processing_ir_actual_checksum=0
gpu_2d_live_processing_ir_values_exact=false
gpu_2d_live_processing_ir_readback_source=device_readback
gpu_2d_live_processing_ir_handle=0
gpu_2d_live_processing_ir_identity=0
gpu_2d_live_processing_ir_mismatch_count=0
gpu_2d_live_processing_ir_cpu_fallback=false
```

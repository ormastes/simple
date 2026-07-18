# OpenCL Generated 2D Readback Evidence

Date: 2026-05-31

| Field | Value |
| --- | --- |
| opencl_generated_2d_readback_status | pass |
| opencl_generated_2d_readback_reason | readback-pixels-matched |
| opencl_generated_2d_readback_opencl_code | 0 |
| opencl_generated_2d_readback_submit_attempted | true |
| opencl_generated_2d_readback_readback_available | true |
| opencl_generated_2d_readback_expected_checksum | 274983770116 |
| opencl_generated_2d_readback_actual_checksum | 274983770116 |
| opencl_generated_2d_readback_mismatch_count | 0 |
| opencl_generated_2d_readback_fill_expected_checksum | 1082179840 |
| opencl_generated_2d_readback_fill_actual_checksum | 1082179840 |
| opencl_generated_2d_readback_fill_mismatch_count | 0 |
| opencl_generated_2d_readback_copy_expected_checksum | 66016 |
| opencl_generated_2d_readback_copy_actual_checksum | 66016 |
| opencl_generated_2d_readback_copy_mismatch_count | 0 |
| opencl_generated_2d_readback_alpha_expected_checksum | 273901410720 |
| opencl_generated_2d_readback_alpha_actual_checksum | 273901410720 |
| opencl_generated_2d_readback_alpha_mismatch_count | 0 |
| opencl_generated_2d_readback_scroll_expected_checksum | 113540 |
| opencl_generated_2d_readback_scroll_actual_checksum | 113540 |
| opencl_generated_2d_readback_scroll_mismatch_count | 0 |
| opencl_generated_2d_readback_blur_or_tolerance_used | false |
| opencl_generated_2d_readback_ops | fill,copy,alpha,scroll |
| opencl_generated_2d_readback_count | 64 |
| opencl_generated_2d_readback_value | 16909060 |
| opencl_generated_2d_readback_expected_pixels_path | build/opencl_generated_2d_readback/expected-u32.json |
| opencl_generated_2d_readback_actual_pixels_path | build/opencl_generated_2d_readback/actual-u32.json |
| opencl_generated_2d_readback_spirv | build/opencl_generated_2d_readback/toolchains/simple_2d_optimization.spirv |
| opencl_generated_2d_readback_spirv_bytes | 0 |
| opencl_generated_2d_readback_loader_present | true |
| opencl_generated_2d_readback_probe_tool_present | true |
| opencl_generated_2d_readback_module_verified | false |

Generated OpenCL evidence is fail-closed until the OpenCL loader, runtime probe, compiled kernel harness, device/queue/kernel handles, submit, synchronization, and readback checksum are all present. The SPIR-V fields are retained as portable-toolchain diagnostics; this gate passes only from direct OpenCL C runtime execution and readback checksum parity.

# ROCm Generated 2D Readback Evidence

Date: 2026-06-16

| Field | Value |
| --- | --- |
| rocm_generated_2d_readback_status | unavailable |
| rocm_generated_2d_readback_reason | missing-primary-tool |
| rocm_generated_2d_readback_hsaco | build/rocm_generated_2d_readback/toolchains/simple_2d_optimization.hsaco |
| rocm_generated_2d_readback_hsaco_bytes | 0 |
| rocm_generated_2d_readback_loader_present | true |
| rocm_generated_2d_readback_probe_tool_present | false |
| rocm_generated_2d_readback_module_verified | false |
| rocm_generated_2d_readback_submit_attempted | false |
| rocm_generated_2d_readback_readback_available | false |
| rocm_generated_2d_readback_expected_checksum | 0 |
| rocm_generated_2d_readback_actual_checksum | 0 |
| rocm_generated_2d_readback_ops | fill,copy,alpha,scroll |
| rocm_generated_2d_readback_required_path | 'HIP source -> HSACO -> ROCm loader -> device/module/kernel handles -> launch -> synchronize -> host readback -> per-op checksums' |

Generated ROCm/HIP evidence is intentionally fail-closed until a verified HSACO module, runtime device/module/kernel handles, submit, synchronization, and readback checksum are all present.

## Host Validation Checklist (AMD ROCm)
- Ensure ROCm/HIP toolchain is present: hipcc.
- Verify runtime tooling before running: rocminfo, libamdhip64, libhsa-runtime64.
- Verify visible AMD GPU runtime before running: rocminfo.
- Refresh and rebuild generated toolchains for HSACO:
<<<<<<< Conflict 1 of 3
+++++++ Contents of side #1
  SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple SIMPLE_LIB=src HIPCC_TOOL=hipcc HIP_ARCH=gfx1100 sh scripts/check/check-portable-compute-toolchains.shs
%%%%%%% Changes from base to side #2
-  - SIMPLE_BIN=bin/simple SIMPLE_LIB=src HIPCC_TOOL=hipcc HIP_ARCH=gfx1100 sh scripts/check/check-portable-compute-toolchains.shs
+  SIMPLE_BIN=bin/simple SIMPLE_LIB=src HIPCC_TOOL=hipcc HIP_ARCH=gfx1100 sh scripts/check/check-portable-compute-toolchains.shs
>>>>>>> Conflict 1 of 3 ends
- Run proof lane directly:
<<<<<<< Conflict 2 of 3
+++++++ Contents of side #1
  SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple SIMPLE_LIB=src HIP_ARCH=gfx1100 sh scripts/check/check-rocm-generated-2d-readback.shs
%%%%%%% Changes from base to side #2
-  - SIMPLE_BIN=bin/simple SIMPLE_LIB=src HIP_ARCH=gfx1100 sh scripts/check/check-rocm-generated-2d-readback.shs
+  SIMPLE_BIN=bin/simple SIMPLE_LIB=src HIP_ARCH=gfx1100 sh scripts/check/check-rocm-generated-2d-readback.shs
>>>>>>> Conflict 2 of 3 ends
- Promote through platform aggregate:
<<<<<<< Conflict 3 of 3
+++++++ Contents of side #1
  SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
%%%%%%% Changes from base to side #2
-  - SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
+  SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
>>>>>>> Conflict 3 of 3 ends

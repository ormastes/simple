# Generated 2D Backend Readback Matrix Evidence

Date: 2026-06-05

- status: pass
- reason: all-required-readbacks-passed
- required backends: cuda opencl vulkan

| Backend | Required | Status | Reason | Expected checksum | Actual checksum | Mismatches |
| --- | --- | --- | --- | --- | --- | --- |
| cuda | true | pass | readback-pixels-matched | 274983770116 | 274983770116 | 0 |
| opencl | true | pass | readback-pixels-matched | 274983770116 | 274983770116 | 0 |
| vulkan | true | pass | pass | 140781974135910 | 140781974135910 | 0 |
| metal | false | unavailable | missing-primary-tool | 0 | 0 |  |
| rocm | false | unavailable | missing-primary-tool | 0 | 0 |  |

## Raw Evidence
- generated_2d_backend_matrix_status=pass
- generated_2d_backend_matrix_reason=all-required-readbacks-passed
- generated_2d_backend_matrix_required_backends=cuda opencl vulkan
- generated_2d_backend_matrix_cuda_status=pass
- generated_2d_backend_matrix_cuda_reason=readback-pixels-matched
- generated_2d_backend_matrix_cuda_required=true
- generated_2d_backend_matrix_cuda_verdict=pass
- generated_2d_backend_matrix_cuda_exit_code=0
- generated_2d_backend_matrix_cuda_evidence_env=build/generated_2d_backend_readback_matrix/cuda/evidence.env
- generated_2d_backend_matrix_cuda_report=build/generated_2d_backend_readback_matrix/cuda/report.md
- generated_2d_backend_matrix_cuda_stdout=build/generated_2d_backend_readback_matrix/cuda/stdout.log
- generated_2d_backend_matrix_cuda_stderr=build/generated_2d_backend_readback_matrix/cuda/stderr.log
- generated_2d_backend_matrix_opencl_status=pass
- generated_2d_backend_matrix_opencl_reason=readback-pixels-matched
- generated_2d_backend_matrix_opencl_required=true
- generated_2d_backend_matrix_opencl_verdict=pass
- generated_2d_backend_matrix_opencl_exit_code=0
- generated_2d_backend_matrix_opencl_evidence_env=build/generated_2d_backend_readback_matrix/opencl/evidence.env
- generated_2d_backend_matrix_opencl_report=build/generated_2d_backend_readback_matrix/opencl/report.md
- generated_2d_backend_matrix_opencl_stdout=build/generated_2d_backend_readback_matrix/opencl/stdout.log
- generated_2d_backend_matrix_opencl_stderr=build/generated_2d_backend_readback_matrix/opencl/stderr.log
- generated_2d_backend_matrix_vulkan_status=pass
- generated_2d_backend_matrix_vulkan_reason=pass
- generated_2d_backend_matrix_vulkan_required=true
- generated_2d_backend_matrix_vulkan_verdict=pass
- generated_2d_backend_matrix_vulkan_exit_code=0
- generated_2d_backend_matrix_vulkan_evidence_env=build/generated_2d_backend_readback_matrix/vulkan/evidence.env
- generated_2d_backend_matrix_vulkan_report=build/generated_2d_backend_readback_matrix/vulkan/report.md
- generated_2d_backend_matrix_vulkan_stdout=build/generated_2d_backend_readback_matrix/vulkan/stdout.log
- generated_2d_backend_matrix_vulkan_stderr=build/generated_2d_backend_readback_matrix/vulkan/stderr.log
- generated_2d_backend_matrix_metal_status=unavailable
- generated_2d_backend_matrix_metal_reason=missing-primary-tool
- generated_2d_backend_matrix_metal_required=false
- generated_2d_backend_matrix_metal_verdict=host-unavailable
- generated_2d_backend_matrix_metal_exit_code=1
- generated_2d_backend_matrix_metal_evidence_env=build/generated_2d_backend_readback_matrix/metal/evidence.env
- generated_2d_backend_matrix_metal_report=build/generated_2d_backend_readback_matrix/metal/report.md
- generated_2d_backend_matrix_metal_stdout=build/generated_2d_backend_readback_matrix/metal/stdout.log
- generated_2d_backend_matrix_metal_stderr=build/generated_2d_backend_readback_matrix/metal/stderr.log
- generated_2d_backend_matrix_rocm_status=unavailable
- generated_2d_backend_matrix_rocm_reason=missing-primary-tool
- generated_2d_backend_matrix_rocm_required=false
- generated_2d_backend_matrix_rocm_verdict=host-unavailable
- generated_2d_backend_matrix_rocm_exit_code=1
- generated_2d_backend_matrix_rocm_evidence_env=build/generated_2d_backend_readback_matrix/rocm/evidence.env
- generated_2d_backend_matrix_rocm_report=build/generated_2d_backend_readback_matrix/rocm/report.md
- generated_2d_backend_matrix_rocm_stdout=build/generated_2d_backend_readback_matrix/rocm/stdout.log
- generated_2d_backend_matrix_rocm_stderr=build/generated_2d_backend_readback_matrix/rocm/stderr.log

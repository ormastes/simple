# Portable Compute Toolchain Evidence

Date: 2026-05-31

| Target | Status | Reason | Bytes | Artifact |
|---|---|---|---:|---|
| cuda | compiled_artifact_verified | pass | 4486 | build/portable_compute_toolchains/simple_2d_optimization.ptx |
| hip | unavailable | missing-primary-tool | 0 | build/portable_compute_toolchains/simple_2d_optimization.hsaco |
| opencl | unavailable | missing-primary-tool | 0 | build/portable_compute_toolchains/simple_2d_optimization.spirv |
| metal | unavailable | missing-primary-tool | 0 | build/portable_compute_toolchains/simple_2d_optimization.metallib |

## Commands

- cuda: `nvcc --ptx -arch`
- hip: `hipcc --genco --offload-arch`
- opencl: `opencl-c-to-spirv -cl-std`
- metal: `metal -c build/portable_compute_toolchains/simple_2d_optimization.metal -o build/portable_compute_toolchains/simple_2d_optimization.air && metallib build/portable_compute_toolchains/simple_2d_optimization.air -o build/portable_compute_toolchains/simple_2d_optimization.metallib`

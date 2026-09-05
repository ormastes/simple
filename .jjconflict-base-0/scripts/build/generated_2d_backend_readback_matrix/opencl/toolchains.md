# Portable Compute Toolchain Evidence

Date: 2026-06-05

| Target | Status | Reason | Bytes | Artifact |
|---|---|---|---:|---|
| cuda | generated_source_failed | generated-source-failed | 0 | build/portable_compute_toolchains/simple_2d_optimization.ptx |
| hip | generated_source_failed | generated-source-failed | 0 | build/portable_compute_toolchains/simple_2d_optimization.hsaco |
| opencl | unavailable | missing-primary-tool | 0 | build/portable_compute_toolchains/simple_2d_optimization.spirv |
| metal | unavailable | missing-primary-tool | 0 | build/portable_compute_toolchains/simple_2d_optimization.metallib |

## Commands

- cuda: `bin/simple run <cuda portable emitter> > build/portable_compute_toolchains/simple_2d_optimization.cu`
- hip: `bin/simple run <hip portable emitter> > build/portable_compute_toolchains/simple_2d_optimization.hip.cpp`
- opencl: `opencl-c-to-spirv -cl-std`
- metal: `metal -c build/portable_compute_toolchains/simple_2d_optimization.metal -o build/portable_compute_toolchains/simple_2d_optimization.air && metallib build/portable_compute_toolchains/simple_2d_optimization.air -o build/portable_compute_toolchains/simple_2d_optimization.metallib`

# Portable Compute Toolchain Evidence

Date: 2026-07-11

| Target | Status | Reason | Bytes | Artifact |
|---|---|---|---:|---|
| cuda | unavailable | missing-primary-tool | 0 | build/portable-compute-metal-fixed/simple_2d_optimization.ptx |
| hip | unavailable | missing-primary-tool | 0 | build/portable-compute-metal-fixed/simple_2d_optimization.hsaco |
| opencl | unavailable | missing-primary-tool | 0 | build/portable-compute-metal-fixed/simple_2d_optimization.spirv |
| metal | compiled_artifact_verified | pass | 19658 | build/portable-compute-metal-fixed/simple_2d_optimization.metallib |

## Commands

- cuda: `nvcc --ptx -arch`
- hip: `hipcc --genco --offload-arch`
- opencl: `opencl-c-to-spirv -cl-std`
- metal: `/var/run/com.apple.security.cryptexd/mnt/com.apple.MobileAsset.MetalToolchain-v17.3.7003.10.RVYeMT/Metal.xctoolchain/usr/bin/metal -c build/portable-compute-metal-fixed/simple_2d_optimization.metal -o build/portable-compute-metal-fixed/simple_2d_optimization.air && /var/run/com.apple.security.cryptexd/mnt/com.apple.MobileAsset.MetalToolchain-v17.3.7003.10.RVYeMT/Metal.xctoolchain/usr/bin/metallib build/portable-compute-metal-fixed/simple_2d_optimization.air -o build/portable-compute-metal-fixed/simple_2d_optimization.metallib`

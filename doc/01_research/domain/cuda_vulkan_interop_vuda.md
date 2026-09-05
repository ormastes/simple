<!-- codex-research -->
# Domain Research: VUDA and Supported CUDA/Vulkan Interop

Date: 2026-08-02

## Verified VUDA facts

VUDA is a real arXiv v1 submitted 2 May 2026 by Bin Xu, Pengfei Hu, Wenxin
Zheng, Jinyu Gu, and Haibo Chen:
https://arxiv.org/abs/2605.01352

The paper redirects CUDA channels into Vulkan's scheduling group and grafts
CUDA page-table subtrees into Vulkan page tables. Its prototype uses a Vulkan
implicit layer, reverse-engineered private driver offsets, and about 1,900 lines
of changes to NVIDIA open RM/UVM kernel modules, including relaxed cross-client
access control. It reports up to 85% improvement over temporal baselines.

The evaluated scope is narrow: Linux, NVIDIA open kernel modules, Vulkan 1.4,
CUDA/driver pairs 12.4/550, 12.6/560, and 12.9/575, on RTX 4090 and RTX 6000
Pro. No Windows, QEMU/Venus, SimpleOS, Adreno, Metal, non-NVIDIA, or emulation
support is evidenced.

No author source repository, patches, build instructions, implementation
license, or reproduction scripts were found. The current host's driver 580 is
outside the paper's published offset table. Direct integration is therefore not
currently implementable or independently verifiable.

The paper's 8,192-buffer setup measurements are workload-specific. The reported
sub-448 KiB failure is an older NVIDIA forum report, not a general VUDA result;
it must not become a universal requirement.

## Supported baseline and alternative

NVIDIA's supported Vulkan interop has Vulkan allocate/export memory and
semaphores, then CUDA import/map/wait/signal them, with devices matched by UUID:
https://docs.nvidia.com/cuda/cuda-programming-guide/04-special-topics/graphics-interop.html

Official sample:
https://github.com/NVIDIA/cuda-samples/tree/master/Samples/5_Domain_Specific/simpleVulkan

This is zero-copy after object setup but object-granular and does not merge
scheduling contexts. `VK_NV_cuda_kernel_launch` can launch uploaded PTX from a
Vulkan command buffer, but is NVIDIA-only/provisional and cannot transparently
redirect arbitrary CUDA libraries:
https://docs.vulkan.org/refpages/latest/refpages/source/VK_NV_cuda_kernel_launch.html

An older project also named VUDA (`jgbit/vuda`) is unrelated: it provides a
CUDA-runtime-like C++ API over Vulkan and is not the 2026 page-table/channel
system: https://github.com/jgbit/vuda

## Risk conclusion

The research VUDA mechanism has severe version, security, fault-isolation,
licensing, and maintenance risks. Simple should model it as an unavailable
experimental capability until upstream code and a supported environment exist.
The implementable host baseline is official external-memory/semaphore interop.

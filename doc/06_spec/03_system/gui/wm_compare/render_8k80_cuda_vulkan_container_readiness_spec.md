# 8K80 CUDA and Vulkan container readiness

This manual mirrors
`test/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.spl`.

## Purpose

Prepare an NVIDIA container to exercise CUDA and Vulkan independently. Vulkan
uses the NVIDIA GPU and driver exposed to the container; it does not execute
through the CUDA programming API.

## Preconditions

- NVIDIA Container Toolkit and Docker GPU support
- an image built by the dedicated preparation wrapper from a digest-pinned
  NVIDIA CUDA devel base, containing `vulkaninfo`, `/usr/bin/time`, and the
  runtime libraries needed by the native producer, but no Mesa Vulkan ICD
- an admitted source-matched Stage4 compiler and provenance receipt

## Operator workflow

1. Run the image contract test without hardware. It proves the digest-only
   base, immutable package snapshot, required tools, Mesa rejection, exact
   NVIDIA capability set, and immutable image-ID receipt behavior.
2. Build/check the image by following
   `doc/07_guide/app/ui/render_8k80_nvidia_container.md`.
3. Run the checker self-test without hardware. The executable SSpec invokes
   this contract matrix through the bounded process facade and requires exit 0.
4. Invoke `--run` with the admitted compiler, provenance receipt, container
   image, and GPU selector.
5. Inspect retained `gpu-inventory/cuda-vulkan.txt`.
6. Accept CUDA only from its generated submit/readback receipt.
7. Accept Vulkan only from the separate strict semantic producer receipt with
   selected backend `vulkan`, known completion, device readback, and no fallback.

## Expected outcomes

- Missing CUDA, Vulkan loader/ICD, GPU capability injection, or Stage4 input:
  status `blocked`.
- Malformed, fallback, mismatched, or non-device evidence: status `failed`.
- Valid non-physical software evidence: aggregate `blocked-physical` until the
  independent physical 8K80 receipt is supplied.

Enumeration from `nvidia-smi` or `vulkaninfo` is inventory only. It cannot
substitute for either API's submit/readback and cannot prove physical scanout.
Likewise, a Mesa software/host ICD must never be used to claim NVIDIA Vulkan.

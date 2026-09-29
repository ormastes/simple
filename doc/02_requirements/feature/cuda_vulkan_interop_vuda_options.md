<!-- codex-research -->
# CUDA/Vulkan Interop — Feature Options

User selection is required before implementation.

## F1 — Supported external memory/semaphore interop (recommended)

**Description:** Add an opt-in composite Simple 2D policy that matches CUDA and
Vulkan device UUIDs, exports Vulkan allocations/semaphores, imports them into
CUDA, and proves CUDA-write to Vulkan-render/readback. SimpleOS exposes the same
typed contract but reports unsupported unless a native matching implementation
exists. VUDA remains an experimental unavailable probe.

**Pros:** Implementable with supported APIs; zero-copy after setup; testable on
the current host; portable across supported NVIDIA driver versions; truthful
SimpleOS behavior.

**Cons:** Does not provide VUDA spatial sharing; per-object setup remains; needs
new runtime/SFFI bindings and lifetime rules.

**Effort:** L, approximately 16-24 files.

## F2 — Vulkan-owned PTX launch with `VK_NV_cuda_kernel_launch`

**Description:** Compile/load selected PTX into Vulkan and launch it from Vulkan
command buffers, retaining official external interop for unsupported kernels.

**Pros:** One Vulkan scheduling context for admitted kernels; avoids kernel
module patching; potentially closer execution integration.

**Cons:** NVIDIA-only provisional extension; cannot redirect opaque CUDA
libraries; substantially changes kernel/module orchestration; support must be
probed per device/driver.

**Effort:** XL, approximately 22-32 files.

## F3 — Wait for and experimentally integrate published VUDA

**Description:** Define only the typed capability/test contract now. Integrate
the 2026 VUDA system later after source, license, supported patches, and a pinned
test environment become available.

**Pros:** Preserves the actual spatial-sharing objective; avoids inventing or
mislabeling an unavailable implementation.

**Cons:** No current implementation outcome; private driver offsets and relaxed
kernel authorization carry severe security/maintenance risk; inapplicable to
SimpleOS/Venus/Adreno/Metal.

**Effort:** S now for contracts, XL+ and presently unestimable for integration.

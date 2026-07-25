# Simple 2D RenderDoc Backend Equivalence — TLDR

Purpose: prove rendering with detailed backend state plus independent exact pixels, without confusing equality, translation, fallback, or artifact presence with correctness.

```sdn
fixtures -> production facades -> backend-owned snapshot -> common record
RenderDoc CLI -> replay evidence ------------------------> equivalence gate
absolute pixel oracle -----------------------------------> equivalence gate
equivalence gate -> focused/intensive/qualification aggregate
```

- Common pure-Simple schema: record, validation, canonical SHA-256, diff, equivalence.
- Exact equality includes provenance; cross-backend semantic equivalence keeps provenance differences visible.
- Linux lanes: NVIDIA Vulkan, Mesa software Vulkan, DirectX-request→Vulkan, Metal-request→Vulkan.
- Native D3D/Metal remain Windows/macOS checkpoints.
- SimpleOS emits a bounded guest receipt; QMP/board capture supplies independent pixels without requiring RenderDoc in the guest.
- QEMU x86/AArch64/RV64 SIMD lanes require target-native instructions, positive operation hits, explicit fallbacks, and exact scalar-oracle pixels.
- Normal frames pay no serialization/replay cost; recording is opt-in.
- Schema changes invalidate stored baselines and comparisons.
- Start at `src/lib/common/renderdoc/`, then Engine2D capture adapter, then the canonical aggregate.

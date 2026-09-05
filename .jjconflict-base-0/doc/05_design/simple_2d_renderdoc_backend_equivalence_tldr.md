# Simple 2D RenderDoc Backend Equivalence Design — TLDR

```sdn
fixture -> production facade -> backend snapshot -> validate/canonicalize
backend -> exact readback -> absolute oracle ------> equivalence result
backend -> RenderDoc capture -> CLI replay-open ---> equivalence result
```

- Exact equality and cross-backend semantic equivalence are distinct.
- Canonical comparison walks fields first; hashes never replace comparison.
- Validation rejects bad provenance, incomplete/blank frames, zero handles, dangling resources, and mislabeled readbacks.
- Linux intensive profile proves NVIDIA Vulkan, Mesa Vulkan, and explicit DirectX/Metal-request→Vulkan compatibility.
- Native D3D and Metal require their native hosts.
- SimpleOS uses a bounded noalloc receipt plus QMP/board framebuffer evidence; guest rendering never depends on host RenderDoc.
- x86 SSE2/AVX2, AArch64 NEON, and RV64 RVV must execute in their QEMU guests with positive hits and exact scalar parity.
- Focused ≤15m; intensive ≤60m; each stress case is 100 frames; max RSS is recorded.
- No raw runtime shortcuts or new Python replay helper.

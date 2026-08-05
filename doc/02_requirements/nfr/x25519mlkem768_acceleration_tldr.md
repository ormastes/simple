# X25519MLKEM768 NFRs — TLDR

```sdn
selection: B
coverage: { overall_branch: 98%, critical_branch: 100% }
promotion: { simd: 1.5x, gpu_end_to_end: 1.25x_at_break_even }
```

- Repair and calibrate coverage before trusting the 98%/100% result.
- Remove secret branches/logging; use explicit entropy and secret lifecycles.
- Scalar p95 regression budget is 5%.
- SIMD needs 1.5x native throughput; GPU needs 1.25x including transfer/sync/readback.
- Persistent caches must invalidate on code/profile/device/config/version changes.
- AVX2/CUDA/Vulkan are current-host rows; native NEON/RVV/Metal remain blockers until proved.


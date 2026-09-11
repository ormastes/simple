# Environment GPU provider/parser qualification

The hosted ABI-v1 lifetime substrate is implemented, but GPU parser execution
must remain unavailable until all of the following are present:

- an authenticated, retained owner for the exact device-program image bytes;
- task-owner consumption of live native provider/resource/completion authority;
- a Vulkan parser kernel whose readback is compared with the CPU oracle;
- missing-feature, wrong-image, capacity+1, cancellation, device-loss,
  uncertain-submit, stale-generation, and replacement negative controls;
- an admitted self-hosted compiler and physical Vulkan device evidence bundle;
- immutable fence/timestamp/readback/retirement receipts and measured startup,
  latency, transfer, synchronization, and RSS budgets.

Do not set `FRONTEND_OFFLOAD_GPU_PARSE_AVAILABLE` from routing, provider-load,
mock-provider, or host-only lifecycle evidence.

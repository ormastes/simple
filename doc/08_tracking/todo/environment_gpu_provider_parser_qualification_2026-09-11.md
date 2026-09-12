# Environment GPU provider/parser qualification

The hosted ABI-v1 lifetime substrate and typed task-consumption bridge are
implemented. The bridge requires live provider/resource/completion token
reprojection, derives resource lease identity from the runtime owner, and
never promotes a terminal readback to physical execution. GPU parser execution
must remain unavailable until all of the following are present:

- an authenticated, retained owner for the exact device-program image bytes;
- a runtime-owned exact device-program image token (the current typed image
  projection intentionally returns no authority words);
- a Vulkan parser kernel whose readback is compared with the CPU oracle;
- missing-feature, wrong-image, capacity+1, cancellation, device-loss,
  uncertain-submit, stale-generation, and replacement negative controls;
- an admitted self-hosted compiler and physical Vulkan device evidence bundle;
- immutable fence/timestamp/readback/retirement receipts and measured startup,
  latency, transfer, synchronization, and RSS budgets.

Do not set `FRONTEND_OFFLOAD_GPU_PARSE_AVAILABLE` from routing, provider-load,
mock-provider, or host-only lifecycle evidence.

The focused contract and authored manual are:

- `test/01_unit/lib/nogc_async_mut/gpu/environment_variant_native_task_bridge_v1_spec.spl`
- `doc/06_spec/01_unit/lib/nogc_async_mut/gpu/environment_variant_native_task_bridge_v1_spec.md`

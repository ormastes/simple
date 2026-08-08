# GPU Web Scene Offload — Domain Research

Primary references reviewed 2026-08-02: Vulkan 1.4 specification and
`vkFlushMappedMemoryRanges`, WebGPU and WGSL specifications, and Apple Metal
synchronization-event documentation.

- Vulkan can use persistently mapped bounded rings, but non-coherent writes
  require atom-aligned flushes and queue dependencies; completion/readback must
  wait for a fence or timeline value.
- WebGPU does not expose concurrently host/GPU mapped shared buffers. Its
  portable implementation is staging upload, dispatch, copy to MAP_READ
  staging, then asynchronous mapping. This is an implementation difference,
  not a semantic ABI difference.
- Packets need fixed-width versioned fields, monotonically correlated sequence
  and generations, bounded capacity, and a commit marker/checksum.
- Only pointer motion may coalesce under pressure. Down/up/key/text transitions
  must never be dropped or reordered.
- There must be one commit owner. CPU replay is legal only before a GPU commit;
  late GPU results are stale and ignored.
- GPU workgroups cannot use a global spin barrier. Hit ordering and mutation
  reduction must be deterministic integer algorithms split into ordered passes.
- OS input, clipboard, IME, accessibility, file/network, and other privileged
  effects remain CPU host services even when boundary/hit/dispatch is on GPU.

References:
- https://registry.khronos.org/vulkan/specs/latest/html/vkspec.html
- https://registry.khronos.org/vulkan/specs/latest/man/html/vkFlushMappedMemoryRanges.html
- https://gpuweb.github.io/gpuweb/
- https://gpuweb.github.io/gpuweb/wgsl/


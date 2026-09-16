# WM Metal Glass Multi-Receipt and Inactive Opacity

**Status:** source fixed and independently accepted / runtime unverified
**Affected lane:** hosted WM `DrawIrComposition -> Engine2D -> Metal`

The rejected WM glass candidate had three source defects:

1. Inactive opacity (`930`) creates a shared Metal offscreen with
   `gpu_only=false`; the device-glass operation rejects that surface, so the
   intended Metal path cannot complete.
2. Material receipt counts aggregate, but target/framebuffer handle/device
   identity are last-wins. The host therefore validates only the final receipt,
   not every requested material against the presented framebuffer.
3. A focused window-scene test expects
   `engine2d-cpu-rounded-material-v1` while production emits
   `engine2d-rounded-material-v1`.

The repaired source now gives `MetalBackend` one persistent session-owned
device identity, preserves it through device readback and every material
receipt, independently derives the ordered requested material IDs from the
submitted composition, and validates each receipt against the presented
framebuffer. Missing, duplicate, extra, reordered, unfulfilled, mixed-target,
handle, device, source, and checksum mismatches fail closed.

CPU seeded/delta composition preserves parent sampling and tested 500/930
opacity. Selected Metal explicitly rejects sub-opaque parent-sampling material
before dispatch until a true GPU-only delta path exists; it cannot claim a
Metal product frame through a mirror-backed offscreen. Requested blur 30 /
bounded CPU realization 4 remains explicit. Focused behavioral contracts and
independent highest-capability review found no remaining P0/P1 source issue.

## Remaining runtime verification

- With an admitted self-hosted runtime, run the exact focused contracts in a
  fresh scoped session:

  ```sh
  bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_device_identity_spec.spl --mode=interpreter
  bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_readback_handle_contract_spec.spl --mode=interpreter
  bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl --mode=interpreter
  bin/simple test test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl --mode=interpreter
  bin/simple test test/01_unit/os/compositor/host_compositor_entry_spec.spl --mode=interpreter
  ```

  Then obtain admitted macOS opaque-Metal device readback/capture evidence and
  retain the ordered per-material receipts. Inactive/sub-opaque Metal must
  remain an explicit fail-closed capability row until a GPU-only delta path is
  implemented and independently verified.

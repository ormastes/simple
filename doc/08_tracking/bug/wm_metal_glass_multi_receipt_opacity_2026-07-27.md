# WM Metal Glass Multi-Receipt and Inactive Opacity

**Status:** fail-closed / review-cycle cap reached
**Affected lane:** hosted WM `DrawIrComposition -> Engine2D -> Metal`

The current uncommitted WM glass candidate is not safe to merge:

1. Inactive opacity (`930`) creates a shared Metal offscreen with
   `gpu_only=false`; the device-glass operation rejects that surface, so the
   intended Metal path cannot complete.
2. Material receipt counts aggregate, but target/framebuffer handle/device
   identity are last-wins. The host therefore validates only the final receipt,
   not every requested material against the presented framebuffer.
3. A focused window-scene test expects
   `engine2d-cpu-rounded-material-v1` while production emits
   `engine2d-rounded-material-v1`.

CPU seeded/delta composition does preserve parent sampling and tested 500/930
opacity, and requested blur 30 / bounded CPU realization 4 is explicit. Those
partial findings are not a Metal product PASS.

## Required repair

- Define a GPU-only parent-seeded/delta composition path for sub-opaque Metal
  material batches, or explicitly fail before claiming Metal selection.
- Retain and validate one target/handle/device tuple per requested material
  receipt; reject any missing, mixed, or presented-frame-mismatched tuple.
- Reconcile the rounded-material capability identifier and its focused spec.
- With an admitted self-hosted runtime, run the exact focused contracts in a
  fresh scoped session:

  ```sh
  bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl --mode=interpreter
  bin/simple test test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl --mode=interpreter
  bin/simple test test/01_unit/os/compositor/host_compositor_entry_spec.spl --mode=interpreter
  ```

  Then obtain highest-capability review and admitted macOS device
  readback/capture evidence.

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

## Attempted on macOS arm64, 2026-09-12 (still unverified — blocked, not fixed)

Host: macOS arm64 (M4), seed `build/cargo-r2/release/simple`. Ran the five
commands above verbatim on this host:

- All five hang under `bin/simple test ... --mode=interpreter`: each prints
  `WARNING: test daemon unavailable; running directly` and then immediately
  `error: test-runner: code -1 (process_run_bounded killed the child at its
  budget) (outer bound 930000ms)` with verdict `timeout=1
  reason=outer-bound-timeout budget_ms=930000` — a spurious timeout verdict
  reported without the process actually running anywhere near 930s wall time.
  This reproduces the test-runner defect already tracked as
  `macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot` (Lane 3 of
  `doc/03_plan/infra/macos_open_bugs_fix_lanes_2026-09-12.md`) — the `test`
  subcommand itself is unusable on this mac host, independent of this bug's
  Metal claims.
- Falling back to `bin/simple run <spec>` (bypasses the broken test-runner
  daemon path) got further:
  - `backend_metal_device_identity_spec.spl` and `draw_ir_adv_spec.spl`:
    hard `E1034` unresolved-import error on `use common.ui.draw_ir.{...}`
    (missing `std.` prefix; `SIMPLE_JIT_STRICT` refuses to fall back to the
    interpreter). `executed=0` — these specs never ran a single example.
  - `backend_readback_handle_contract_spec.spl`: ran, 1 example, 1 FAILURE —
    `src/lib/gc_async_mut/gpu/engine2d/backend_rocm.spl: variable
    device_readback source missing framebuffer handle`.
  - `window_scene_draw_ir_spec.spl`: ran, 12 examples, 8 failures.
  - `host_compositor_entry_spec.spl`: ran, 61 examples, 19 failures.

None of this confirms or refutes the source fix described above — the
blocking issue is the host's `test` subcommand, and `host_compositor_core.spl`
/ `backend_rocm.spl` are owned by other in-flight lanes (Lane 4 of the same
plan), so their failures are not diagnosed or touched here. **Resume
condition:** once `macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot`
is fixed (Lane 3) so `bin/simple test <spec>` runs to completion on this host,
re-run the five commands above unmodified; if `backend_readback_handle_contract_spec.spl`,
`window_scene_draw_ir_spec.spl`, or `host_compositor_entry_spec.spl` still
fail, coordinate with the Lane 4 owner (`host_compositor_core.spl`,
`backend_rocm.spl`) before attributing the failures to this bug. Status stays
**runtime unverified**; this entry only narrows the blocker.

# SYS-GUI-008 Round-3 Plan — PPM Diff Harness (2026-04-15)

## Gate: Round-2 blocker must be fixed first

Round-2 ends at `[PANIC] heap exhausted` immediately after the virtio-gpu
controlq `GET_DISPLAY_INFO` notify.  Round-3 begins only when the guest
reaches `[sys-gui-008] render-ready` and the QMP screendump produces a
non-empty PPM.

## Round-2 remaining blocker (virtio-gpu ring fix)

1. Dump controlq descriptor / avail / used ring state immediately before
   `virtqueue_kick` (guest-side `rt_log` + QEMU monitor `info qtree` /
   `gva2gpa`).
2. Compare published ring layout against the repo's known-good virtqueue
   helpers (`src/lib/nogc_async_mut_noalloc/execution/virtio/virtqueue.spl`).
3. Ensure `VIRTIO_F_VERSION_1` is negotiated in the modern-PCI feature
   handshake (required for split-ring semantics on q35).
4. Fix the descriptor write / avail-idx increment so the device can consume
   without corrupting the bump allocator.

## Round-3 objectives (once guest reaches render-ready)

### 3-A  Capture baseline PPM via QMP screendump

- Spec: `test/system/sys_gui_008_virtio_gpu_baseline_spec.spl`
  (skeleton already merged, pending `render-ready` signal)
- Flow: build ELF → `spawn_guest_with_qmp` → wait for
  `[sys-gui-008] render-ready` → `capture_qemu_vm` → decode PPM →
  compare against `test/baselines/sys_gui_008/virtio_gpu_scene.ppm`

### 3-B  Write the PPM diff harness spec

- Spec: `test/system/sys_gui_008_ppm_diff_harness_spec.spl`
  (skeleton merged as part of wave-3; needs `it{}` bodies filled in)
- Two cases:
  1. Exact-match: in-process render vs. virtio-gpu QMP capture (≤ 1 % diff)
  2. Regression gate: new capture vs. committed baseline (≤ 0.1 % diff)

### 3-C  Commit the virtio-gpu baseline PPM

- Path: `test/baselines/sys_gui_008/virtio_gpu_scene.ppm`
- Resolution: 1024 × 768 (matching the framebuffer boot config in
  `examples/simple_os/arch/x86_64/sys_gui_008_entry.spl`)
- Run with `UPDATE_BASELINE=1 bin/simple test ...` once guest renders cleanly

### 3-D  Update tracking docs

- Row 4 of `doc/03_plan/gui_drawing_layer_variations.md` → ✅ Done
- `doc/08_tracking/todo/sys_gui_008_round2_status_2026-04-15.md` → add
  Round-3 landed note
- `doc/08_tracking/lane_matrix.md` (if present) → mark virtio-gpu lane green

## Acceptance criteria

- `bin/simple test test/system/sys_gui_008_virtio_gpu_baseline_spec.spl`
  exits 0 with 0 failures.
- `bin/simple test test/system/sys_gui_008_ppm_diff_harness_spec.spl`
  exits 0 with 0 failures.
- Baseline PPM committed and pixel match ≥ 99.0 %.

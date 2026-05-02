# SYS-GUI-008 Baseline PPMs

This directory holds the PPM baseline captures for the virtio-gpu rendering
lane (SYS-GUI-008).

## File layout

```
test/system/sys_gui_008/baselines/
    virtio_gpu_scene.ppm          # sys-gui-008 capture (virtio-gpu via QMP screendump)
    README.md                     # this file
```

## Comparison path

The Round-3 `it{}` block in
`test/system/sys_gui_008_virtio_gpu_baseline_spec.spl` reads two PPMs:

| Role            | Path                                                                 |
|-----------------|----------------------------------------------------------------------|
| sys-gui-006 ref | `test/baselines/simpleos_desktop_framebuffer/desktop_scene.ppm`      |
| sys-gui-008 cap | `test/system/sys_gui_008/baselines/virtio_gpu_scene.ppm`             |

The two paths differ because sys-gui-006 uses the shared `test/baselines/`
tree (managed by `simpleos_desktop_framebuffer_spec.spl`), while sys-gui-008
owns a sub-tree under `test/system/sys_gui_008/` to keep all virtio-gpu
artefacts co-located with the spec that produces them.

## Tolerance

virtio-gpu renders through Mesa/QEMU's software virtio emulation, which can
produce per-pixel deltas versus the BGA CPU framebuffer used in sys-gui-006.
The Round-3 diff gate uses a **max-channel delta <= 5 %** (i.e. <=12 on the
0-255 scale per channel) on all overlapping pixels; whole-scene match must be
>= 95 %.

## Recording a fresh baseline

```bash
# 1. Run QEMU manually (or let Round-2 capture) to produce the PPM:
#    build/os/simpleos_sys_gui_008_capture.ppm
# 2. Copy it here:
cp build/os/simpleos_sys_gui_008_capture.ppm \
   test/system/sys_gui_008/baselines/virtio_gpu_scene.ppm
# 3. Commit.
```

Or use the UPDATE_BASELINE env flag (Round-3 spec self-records on first run):

```bash
UPDATE_BASELINE=1 bin/simple test test/system/sys_gui_008_virtio_gpu_baseline_spec.spl
```

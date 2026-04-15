# SYS-GUI-008 Round-2 Status (2026-04-15)

## What Landed

- `test/system/sys_gui_008_virtio_gpu_baseline_spec.spl`
  now runs the real Round-2 flow:
  build -> `spawn_guest_with_qmp` -> wait for
  `[sys-gui-008] render-ready` -> QMP screendump capture.
- `src/os/compositor/qemu_capture.spl`
  no longer depends on the interpreter-hostile
  `rt_unix_socket_connect` extern path.
  It now performs the QMP greeting / `qmp_capabilities` /
  `screendump` handshake through a host `python3` subprocess launched
  via `rt_process_run`.
- `examples/simple_os/arch/x86_64/sys_gui_008_entry.spl`
  now logs the concrete `VirtioGpuDriver.init_from_grant(...)` error
  instead of collapsing everything to `virtio-gpu init failed`.
- `src/os/drivers/virtio/virtio_gpu.spl`
  now:
  - binds the modern virtio-pci capability windows on QEMU `q35`
  - allocates queue / command / response / framebuffer DMA from the
    baremetal identity-mapped heap contract (`virt == phys`)
  - logs the probed modern control-queue size and queue-notify path
  - propagates the exact transport / init failure point
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
  now fixes `rt_mmio_write_u16_real(...)` to use raw addresses and raw
  values, matching the other MMIO helpers instead of incorrectly
  decoding tagged integers.

## Current Live Failure

Direct QEMU boot of `sys_gui_008_entry.spl` now reports:

`[virtio-gpu] modern controlq probe: num_queues=2 queue_select=0 queue_size_reg=64 notify_mult=4`

`[virtio-gpu] Controlq ready (modern size=64)`

`[virtio-gpu] GET_DISPLAY_INFO hdr-ok`

`[virtio-gpu] send_command notified`

`[PANIC] heap exhausted`

So Round-2 is no longer blocked by the spec harness or QMP capture path.
It is also no longer blocked by BAR / capability discovery.
The remaining blocker is post-notify queue consumption: the guest builds
the command header correctly, but as soon as the device consumes the
published controlq descriptors, memory is corrupted badly enough to trip
the bump allocator.

## Evidence

- Direct host run of the built ELF now reaches:
  PCI discovery -> modern virtio-pci capability bind -> controlq ready
  -> `GET_DISPLAY_INFO hdr-ok` -> notify -> allocator panic.
- QEMU monitor checks confirmed:
  - `gva2gpa 0x<cmd_buf>` resolves to the same low address
  - the command buffer identity-maps in this lane
- Guest-side readback confirms the command header in CPU-visible memory is
  correct before notify.

This narrows the remaining fault surface to the descriptor / avail / used
ring state that the device consumes after notify, or another post-notify
DMA contract issue adjacent to queue publication.

## Next Tasks

1. Dump and validate the published controlq descriptor / avail / used ring
   contents immediately before notify (guest-side and via QEMU monitor).
2. Compare the GPU queue publication path against the repo’s known-good
   virtqueue helpers and normalize any remaining packed-field writes.
3. Recheck whether the modern path needs additional negotiated features
   (notably `VIRTIO_F_VERSION_1`) once the ring publication is correct.
4. After the queue-consumption fix, rerun:
   `bin/simple test test/system/sys_gui_008_virtio_gpu_baseline_spec.spl`
5. If the guest reaches `[sys-gui-008] render-ready`, commit the captured
   PPM and move to the Round-3 diff harness.

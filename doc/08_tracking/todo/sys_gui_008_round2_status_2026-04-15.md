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
- `examples/simple_os/arch/x86_64/boot/rt_extras.c`
  now provides strong `rt_ptr_write_i32(...)`, plus tagged-value aware
  raw pointer helpers for `i16/i32/i64` reads and writes so normal RAM
  protocol blobs can be written without storing boxed runtime values.
- `src/os/drivers/virtio/virtio_gpu.spl`
  now hardcodes the live SYS-GUI-008 boot-path protocol literals at the
  C boundary, which avoids the imported-constant boxing issue that was
  corrupting command headers and descriptor metadata in guest RAM.

## Current Live Failure

Direct QEMU boot of `sys_gui_008_entry.spl` now reports:

`[virtio-gpu] modern controlq probe: num_queues=2 queue_select=0 queue_size_reg=64 notify_mult=4`

`[virtio-gpu] Controlq ready (modern size=64)`

`[virtio-gpu] GET_DISPLAY_INFO hdr-ok`

`[virtio-gpu] send_command timeout`

`[virtio-gpu] GET_DISPLAY_INFO resp_type=0x0`

So Round-2 is no longer blocked by the spec harness or QMP capture path.
It is also no longer blocked by BAR / capability discovery.
The old post-notify allocator corruption is fixed. The remaining blocker
is now a clean controlq timeout: the guest stays alive, but the device
does not consume the published `GET_DISPLAY_INFO` request.

## Evidence

- Direct host run of the built ELF now reaches:
  PCI discovery -> modern virtio-pci capability bind -> controlq ready
  -> `GET_DISPLAY_INFO hdr-ok` -> notify -> allocator panic.
- QEMU monitor checks confirmed:
  - `gva2gpa 0x<cmd_buf>` resolves to the same low address
  - the command buffer identity-maps in this lane
- QEMU monitor now confirms the command buffer contains the correct raw
  header word `0x00000100` for `GET_DISPLAY_INFO`, and the response
  buffer stays zeroed before completion.
- Device common-config readback confirms the guest programmed the same
  controlq desc / avail / used addresses that it intended to use.
- QEMU monitor dumps of those desc / avail / used addresses still show
  zeroed memory, even after the guest-side publish path reports nonzero
  descriptor metadata. That is the next narrow mismatch to resolve.

This narrows the remaining fault surface to the queue-ring memory write
path itself: either the guest is still writing descriptor / avail / used
state to the wrong CPU-visible addresses, or the assumed `virt == phys`
DMA contract is incomplete for the controlq ring allocation even though
the smaller command/response buffers behave correctly.

## Next Tasks

1. Reconcile the controlq ring writes with the QEMU monitor dump:
   desc / avail / used are still zero in guest physical memory at the
   addresses programmed into the device.
2. Check whether the ring allocation path is landing in a different CPU
   mapping than the command/response buffers despite the current
   `virt == phys` assumption.
3. Compare the ring write path against the repo’s known-good virtqueue
   helpers and normalize any remaining 16-bit publication fields.
4. Recheck whether the modern path needs additional negotiated features
   (notably `VIRTIO_F_VERSION_1`) once the queue memory write path is
   confirmed.
5. After the queue-consumption fix, rerun:
   `bin/simple test test/system/sys_gui_008_virtio_gpu_baseline_spec.spl`
6. If the guest reaches `[sys-gui-008] render-ready`, commit the captured
   PPM and move to the Round-3 diff harness.

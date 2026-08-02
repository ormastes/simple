# SimpleOS I/O and Audio

SimpleOS routes input and audio lifecycle through the pure-Simple
`SimpleDeviceEvent` contract. QEMU ARM64 and RISC-V use VirtIO input and
VirtIO sound; x86 retains HDA and supports optional host CUDA audio offload.

## Owners

- `src/lib/common/io/simple_device_event.spl`: ordered bounded events.
- `src/lib/common/engine/audio/simple_audio_*.spl`: device, period, graph,
  remote-work, and fallback contracts.
- `src/os/drivers/virtio/virtio_input_*.spl`: keyboard/pointer transport.
- `src/os/drivers/virtio/virtio_snd_*.spl`: sound control and PCM queues.
- `src/os/services/audio/`: HDA, VirtIO sound, and offload services.
- `src/app/simpleos_audio_host/`: pure-Simple host CUDA daemon.

GLFW and SDL3 are independent dynamically loaded hosted adapters. Missing
libraries produce explicit unavailable results; neither backend aliases the
other. Native audio reports its actual miniaudio backend, including Null when
no real endpoint exists.

## QEMU CUDA audio

The supported architecture is guest-to-host offload, not an in-guest CUDA
driver. The guest publishes bounded Q15 input and kernel payloads through an
audio-specific `ivshmem-plain` region. The host daemon submits PTX through the
CUDA driver API, performs device readback, checks CPU parity, and publishes a
generation/correlation-bound completion.

Two ivshmem devices are required:

1. ordinal `0`: render/host-GPU wire;
2. ordinal `1`: audio wire.

The audio mapper must select ordinal `1` and program a distinct BAR2 window.
It fails unavailable when the second device is absent rather than aliasing the
render wire.

## Focused verification

```sh
bin/simple test test/01_unit/lib/common/engine/audio/simple_audio_contract_spec.spl --mode=interpreter
bin/simple test test/01_unit/lib/common/engine/audio/simple_audio_device_spec.spl --mode=interpreter
bin/simple test test/01_unit/lib/common/engine/audio/simple_audio_offload_spec.spl --mode=interpreter
bin/simple test test/01_unit/lib/common/io/simple_device_event_spec.spl --mode=interpreter
bin/simple test test/03_system/io_audio/simple_audio_graph_spec.spl --mode=interpreter
bin/simple test test/03_system/io_audio/simple_audio_ivshmem_protocol_spec.spl --mode=interpreter
bin/simple test test/03_system/io_audio/simple_audio_platform_offload_spec.spl --mode=interpreter
bin/simple test test/03_system/io_audio/simple_audio_qemu_transport_contract_spec.spl --mode=interpreter
```

Live VirtIO runners:

```sh
SIMPLE_BIN=<admitted-pure-simple> sh scripts/check/check-simpleos-virtio-snd-qemu.shs --arch aarch64
SIMPLE_BIN=<admitted-pure-simple> sh scripts/check/check-simpleos-virtio-snd-qemu.shs --arch riscv64
```

## Current synchronized status

The focused suite passes 37/37 examples. The QEMU transport contract passes
6/6 after restoring `map_qemu_audio_ivshmem_bar2`: render/host-GPU selects
ordinal `0`, audio selects ordinal `1`, and absence of the second device fails
closed instead of aliasing the render wire. Mapper and audio-service source
checks also pass.

This is **PASS** for the focused transport regression. It does not replace the
separate live two-ivshmem CUDA readback gate, which must still be run when the
guest, host daemon, QEMU/OVMF, and CUDA device environment is available.

Metal/macOS, Windows, and BSD runtime claims require native evidence on those
platforms. Linux-only compilation or unavailable results are not native PASS.

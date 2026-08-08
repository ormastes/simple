# Architecture: Pure-Simple QEMU CUDA Audio Driver

Application/audio graph → CPU reference → `SimpleAudioRemoteRing` publish → QEMU ivshmem → prewarmed host CUDA service → device readback → generation/deadline/parity admission → period ring/HDA or VirtIO-snd. `SimpleDeviceEventRing` owns ordered lifecycle events. CPU output always exists before publication.

The transport uses a second 8 MiB `ivshmem-plain` PCI function, never the
blocking Draw IR wire. Eight 256-byte control slots reference fixed bounded Q15
input, kernel, and output areas. The guest owns initialization/publication and
uses its monotonic clock for the 60% period deadline; the host reports service
elapsed time only because host and guest monotonic epochs are unrelated.

`simpleos_audio_host` retains one CUDA context/module, validates both payload
checksums, runs the Q15 PTX convolution, performs device-to-host readback, and
publishes provenance only after CPU-oracle parity. Direct HDA remains available
and CPU-owned independently of optional offload.

The guest owns policy and is entirely Simple. The host owns NVIDIA `libcuda`; receipts say `remote-host-cuda`. Direct NVIDIA/VFIO is a separate experimental capsule. Audio never imports Engine2D. Shared GPU protocol code contributes only correlation/provenance vocabulary.

Invariants: bounded power-of-two-independent slots; no overwrite before consume; monotonic `free→published→processing→completed→free`; exact generation/correlation; deadline at 60% period; stale/late/mismatched results fail closed; shutdown invalidates all generations and emits one receipt.

# Detail Design: Pure-Simple QEMU CUDA Audio Driver

`SimpleAudioRemoteRing` stores immutable work descriptors and completion receipts in bounded preallocated arrays. Publish and poll are nonblocking operations. The first admitted work kind is partitioned convolution/HRTF. Each descriptor carries slot generation, sequence, correlation, period/deadline, frame/channel/kernel dimensions and CPU checksum. Completion additionally carries provider, handle, device identity, readback checksum and normalized error.

Admission accepts only `remote-host-cuda`, positive provenance, matching identifiers, completion before deadline and error ≤1e-5. Timeout, reset, malformed completion and device loss release the slot to CPU fallback. A future MMIO adapter maps the same record fields onto the audio-specific ivshmem wire; it must not call the existing blocking Draw IR poll loop.

The MMIO adapter is now implemented. Its payload layout is fixed at a 4096-byte
header/control prefix followed by eight 512 KiB slot regions. Each region has
bounded Q15 input (32768 samples), kernel (4096 samples), and output storage.
Publication writes payload/checksums before the release barrier and state; the
host claims nonblocking and completion is generation/correlation safe.

Direct, Engine2D, and Engine3D callers share `SimpleAudioGraph`. The graph owns
epochs, bounded source slots, format validation, direct PCM routing, 2D pan,
3D distance/doppler/occlusion/HRTF metadata, cancellation, and teardown.

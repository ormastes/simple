# RV32 secure boot entropy — domain findings

Virtio 1.2 defines entropy device ID 4 with one `requestq`. The driver supplies
device-writable buffers and must use the device-reported written length; a
device may return fewer bytes than requested. Consequently the Simple owner
must accumulate bounded completions until exactly 16 bytes are obtained or
fail, and must never read beyond the reported length.

QEMU supports an RNG backend and virtio-rng device. A production-like QEMU lane
should use an explicit host random backend and record its argv/provenance; the
guest must still discover, negotiate, and drive the virtqueue. Merely adding a
QEMU device does not make entropy available.

The repository/OpenSBI interface has no standard random-byte SBI call. Boot
injection is viable only when firmware/loader authenticates the handoff and the
buffer stays kernel-only, single-consumer, and wiped after registry adoption.

References: OASIS Virtual I/O Device 1.2, entropy device section; QEMU system
invocation RNG backend documentation.

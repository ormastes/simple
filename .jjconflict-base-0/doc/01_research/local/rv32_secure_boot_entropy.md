# RV32 secure boot entropy — local audit

The current RV32 entropy module exposes only a mixed u64 derived from timer,
wall time, DTB address, hart ID, and a constant; its own comment says no true
random source is available. No virtio-rng device ID, queue driver, or entropy
provenance owner exists under `src/os/drivers`. The canonical RV32 DTS contains
UART, CLINT, and PLIC only. Current RV32 QEMU launch paths do not attach a
virtio-rng device.

The generic production crypto entropy API is fail-closed, but no audited RV32
platform implementation connects it to a hardware/virtual entropy source.
Therefore the transition registry must remain unavailable today.

Preferred implementation order is: add a bounded virtio-rng MMIO requestq
owner and attach `virtio-rng-device` to the canonical QEMU configuration; then
admit exactly 16 returned bytes with a virtio provenance receipt. An
authenticated kernel-only boot injection is an alternative. The early mixer is
never a fallback. OpenSBI exposes no standard supervisor random-byte call in
the current repository interface.

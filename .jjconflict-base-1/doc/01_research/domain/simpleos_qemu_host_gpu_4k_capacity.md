<!-- codex-research -->
# SimpleOS QEMU Host-GPU 4K Capacity — Domain Research

## QEMU Mechanism

QEMU's `ivshmem-plain` device is backed by a named host memory backend; the
backend's `size` is supplied by the launcher rather than fixed by the device.
The official documentation demonstrates both small POSIX shared-memory regions
and much larger hugepage-backed regions. This confirms that SimpleOS's 8 MiB
limit is a protocol/guest-mapping decision, not a QEMU device ceiling.

Source: [QEMU Inter-VM Shared Memory device](https://www.qemu.org/docs/master/system/devices/ivshmem.html).

`memory-backend-file` requires the launcher to provide an explicit size and
shared backing when another process must observe writes. Consequently the QEMU
backend/BAR and negotiated usable capacity must agree; the backing file must be
at least that large. SimpleOS may choose an exact-file-size launcher invariant,
but QEMU itself does not require one. Changing only one peer remains unsafe.

Source: [QEMU system emulator manual](https://www.qemu.org/docs/master/system/qemu-manpage.html).

## Design Implications

### Larger single arena

A larger region preserves the current immutable-request/correlated-receipt
model and permits one checksum over the complete frame. It costs virtual/shared
address space and requires deliberate BAR placement, but does not inherently
require a new QEMU device or interrupt model.

### Runtime-negotiated arena

QEMU supports explicitly sized shared backends, so launch-time selection among
bounded sizes is feasible. The guest still needs trustworthy BAR-size
discovery, and the protocol must negotiate the actual capacity rather than
compare against one compile-time global.

### Tiled transfer

Keeping an 8 MiB arena requires a protocol state machine for tile identity,
ordering, duplication, whole-frame correlation, retries, and final checksum.
It also conflicts with checksum-before-first-scanout-write unless the guest
keeps a complete hidden buffer or replays all tiles after validation. This is a
protocol-complexity trade, not a QEMU requirement.

## Operational Constraints

`ivshmem-plain` is polling-friendly and does not require the interrupt-capable
ivshmem server/doorbell configuration. The current SimpleOS design can retain
its bounded polling behavior for either fixed or negotiated arena sizing.
Migration semantics remain out of scope; QEMU documents additional master and
reattachment requirements when migrating ivshmem devices.

# RV32 authenticated user-entry adoption v1

## Scope

This prerequisite binds a live loader authority slot, its authenticated RV32
ELF layout evidence, and an immutable U-mode `sret` frame. The layout evidence
is not an ownership-bound Sv32 mapping receipt. This change does not implement
the missing authoritative Sv32 mapper, publish a runnable task, execute `sret`,
or change `executable_riscv32_process_image_ready_v1()` from false.

## Ownership

The executable authority registry remains the only mutable owner. Under its
existing mutex it validates the exact live Armed token, target, path, entry,
clean consumer, and authenticated non-overlapping load ranges. It then changes
the slot to `JointReserved` and mints paired opaque joint and RV32-entry leases.
Both leases and the exact `sepc`/`sp`/sanitized-`sstatus` tuple are consumed by
one registry transition; the generic joint commit rejects a slot carrying an
RV32-entry nonce, preventing downgrade bypass. The committed frame is returned
from registry-owned state only after that transition.

Copied leases are handles, not state. Stale, substituted, aborted, or replayed
coordinates fail against the live slot generation and nonces. Storage remains
bounded by the existing 4096-slot authority registry; no second table or scan
is added.

## Privilege frame

`riscv32_user_sret_state_v1` rejects zero/kernel-half or odd entry addresses, zero or
kernel-half stacks, and non-16-byte-aligned stacks. It clears `sstatus.SPP` and
`SIE`, sets `SPIE`, and narrows `sepc`/`sp` only after bounds checks. Clearing
SPP is mandatory: setting it would make `sret` return to S-mode.

## Remaining integration gate

Scheduler adoption must remain disconnected until the authoritative Sv32 page
mapper produces ownership-bound mapping receipts for every segment and stack
page. Only then may it consume the paired reservation, install the proven SATP
root, publish the TCB, and enter U-mode. Static source or unit evidence is not a
QEMU launch receipt.

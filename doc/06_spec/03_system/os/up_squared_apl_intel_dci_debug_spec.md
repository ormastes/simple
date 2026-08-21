# UP Squared Apollo Lake Intel DCI debug specification

Executable source:
`test/03_system/os/up_squared_apl_intel_dci_debug_spec.spl`.
This is a manually maintained companion because the deployed Stage 4
test/docgen runtime is currently absent. The admitted Stage 3 compiler builds
the freestanding UP2 closure, and the OVMF oracle executes the boot, shell, and
RSP memory path.

## Admit the Intel DCI connection

Inventory must distinguish a real Target Connection Agent Apollo Lake session
from Smart KM Link, Tigard, or connector presence. Missing licensed tooling or
connection receipt is BLOCKED. OpenRC warm reset is forbidden.

## Stage and commit the SimpleOS payload

The producer writes payload first and commits a generation/nonce/length/SHA-256
descriptor last. Partial, stale, replayed, malformed, or digest-mismatched
mailboxes fail before mutation.

## Validate the physical ELF plan

Every `PT_LOAD` is copied by file offset to physical address and zero-filled to
memory size. Overflow, overlap, W+X, non-allowlisted memory, or an entry outside
an executable segment fails. Contiguous ELF copy plus RIP assignment is never a
valid plan.

## Admit one storage write

The request binds one exact model/serial/transport/capacity and byte range to
the image digest. Root, swap, mounted, held, identity-mismatched, unconfirmed,
or out-of-bounds targets fail. Hardware must flush and verify exact readback.

## Load and verify RAM with the free monitor

After the shell command `gdb`, send checksummed GDB RSP packets. The monitor
advertises `PacketSize=1000`, admits at most 1024 bytes per `m`/`M`, and confines
access to `0x0a000000..0x0b000000`. The OVMF scenario writes ASCII `SIMP` and
requires exact readback `53494d50` before detach. Register, breakpoint,
continue, step, and reset requests remain unsupported rather than fabricated.

## Physical completion

Connection, RAM load, boot/VFS `ls /`, and storage readback are separate receipt
levels. This manual's host-independent scenarios cannot promote unavailable
physical evidence to PASS.

## Traceability

| Requirement | Executable evidence | Physical evidence |
|---|---|---|
| REQ-006 | partial/final mailbox admission | DCI mailbox write receipt pending |
| REQ-007 | reviewed three-segment physical ELF plan | RAM boot receipt pending |
| REQ-009 | exact identity, busy-state, bounds policy | device enumeration pending |
| REQ-010 | hash-bound challenge admission | flush/readback receipt pending |
| REQ-013 | bounded `M` plus exact `m` readback under OVMF | physical CN16 receipt pending |

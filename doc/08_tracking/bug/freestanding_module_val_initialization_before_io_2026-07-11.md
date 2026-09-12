# Freestanding Module Values Are Zero Before Early Hardware I/O
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Symptom

Pure-Simple freestanding code in `bga_init.spl` loaded module-level `val`
hardware constants from runtime storage before module initialization. This is
unsafe for early I/O even though it was not the sole cause of the observed BGA
readback failure.

## Evidence

- The stage3 pure-Simple kernel linked real `inw`/`outw` implementations.
- QEMU `info pci` reported the stdvga controller.
- Serial evidence reported `device_id=0 width=0 height=0` both before and after
  immediate constants, proving that constant materialization alone did not fix
  the QEMU data-port problem.
- Disassembly of the qualified pure-Simple `bga_write` loaded
  `BGA_INDEX_PORT` and `BGA_DATA_PORT` through module storage, while the
  bootstrap-local function embedded port immediates.

## Required Compiler Fix

Freestanding lowering must either materialize immutable scalar module values
as constants or guarantee module initialization before any entry-reachable
function. Until then, early hardware protocol constants must remain immediate
inside the owning I/O functions. This does not permit requested framebuffer
dimensions to substitute for device readback. The BGA owner now also uses
QEMU's documented aligned `0x1d0` word data port instead of relying on the
x86-only odd-address `0x1cf` compatibility port. Because both port paths still
returned zero on the PCI stdvga device, the production owner now prefers the
device's discovered BAR2 flat-register MMIO interface and retains port I/O only
as the non-MMIO fallback.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

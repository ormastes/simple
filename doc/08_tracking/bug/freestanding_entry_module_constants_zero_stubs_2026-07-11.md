# Freestanding Entry Constants Become Zero Stubs
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

Stage3 Cranelift freestanding builds emit module-level scalar `val`s declared
in the entry file as weak functions returning zero instead of initialized data.
Imported module constants are emitted as initialized data.

## Evidence

`gui_entry_desktop.spl` symbols such as `FB_W`, `FB_H`, and
`DIRECT_QEMU_TOTAL_MEMORY` appeared as weak text symbols whose bodies were
`xor eax,eax; ret`. Consequently PMM received zero bounds and BGA received a
zero requested mode, while PCI discovery itself remained valid.

## Required Fix

The native-project data-export/mangling pass must classify entry-module
`Node::Let` immutable globals as data and preserve `global_init_values` through
per-module compilation. Until fixed, early freestanding entry hardware values
are local immediates at their owning operations. They must not be replaced by
fake device readback or fixed evidence metadata.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

# Freestanding Entry Constants Become Zero Stubs
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


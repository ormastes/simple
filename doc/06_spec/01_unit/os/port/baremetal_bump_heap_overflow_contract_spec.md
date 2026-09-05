# RISC-V baremetal bump heap overflow safety

The executable contract at `test/01_unit/os/port/baremetal_bump_heap_overflow_contract_spec.spl` verifies that RV32, normal RV64, and the RV64 GHDL runtime use the shared checked bump-heap owner.

It checks rejection without offset movement for alignment and multiplication overflow, valid alignment and monotonic allocation, exact zeroing after a checked `calloc` product, fail-closed moving `realloc`, NULL-form `realloc` allocation, and heap-end rejection. This is host C evidence only; it is not RISC-V board or QEMU execution evidence.

# RV64 Streamed FAT ELF Loader Contract

Source: `test/01_unit/os/kernel/loader/rv64_streamed_fat_elf_loader_contract_test.shs`

Evidence class: `host-fixture` plus `source-contract`.

The test checks bounded streamed FAT reads, cycle detection, monotonic cursor
reuse, dynamic page ownership, rollback, PT_LOAD bounds, and W^X rejection. It
also builds and inspects a RISC-V ELF larger than 4 MiB to prove the host
fixture is not limited by the removed fixed buffers. It does not boot QEMU or
prove the guest loader executed that ELF.


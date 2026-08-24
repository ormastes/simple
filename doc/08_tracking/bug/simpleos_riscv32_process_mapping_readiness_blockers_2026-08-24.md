# SimpleOS RV32 process mapping readiness blockers — 2026-08-24

RV32 ELF admission exists and the bounded initial-stack owner can now serialize
four-byte SysV words, but canonical process-image readiness remains false.

1. `user_address_space.spl` delegates RV32 creation/mapping to generic VMM
   entrypoints instead of an authoritative RV32 paging owner.
2. RV32 paging copies kernel root indices 512 through 1023, while the current
   `0x81000000` user stack falls in copied Sv32 root index 516.
3. `Rv32ContextSwitch.create` sets `SSTATUS_SPP`, selecting supervisor return
   instead of U-mode return.
4. Detailed authenticated mapping evidence is currently available only after
   loader retrieval in image preparation; readiness requires a pre-commit gate
   so malformed evidence cannot consume the one-shot authority.

Until all four are resolved together, `executable_target_dispatch_v1` must
keep `riscv32.process_image_builder_ready = false`.

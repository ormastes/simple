# riscv64 elf_boot_link fixture: CALL, PCREL_HI20/LO12_I/LO12_S, HI20/LO12_I,
# BRANCH/JAL, R_RISCV_64, with R_RISCV_RELAX hints (assembled with -mrelax so
# the hints are present; the link must ignore them = ld.lld --no-relax).
    .section .text.boot,"ax"
    .globl _start
_start:
    call helper
.Lpc0:
    auipc a0, %pcrel_hi(counter)
    ld a1, %pcrel_lo(.Lpc0)(a0)
.Lpc1:
    auipc a2, %pcrel_hi(counter)
    sd a1, %pcrel_lo(.Lpc1)(a2)
    lui a3, %hi(message)
    addi a3, a3, %lo(message)
    beqz a1, 1f
    j _start
1:  wfi
    .section .rodata
message: .asciz "rv"
    .section .data
    .p2align 3
counter: .dword 7
ptr:     .dword helper

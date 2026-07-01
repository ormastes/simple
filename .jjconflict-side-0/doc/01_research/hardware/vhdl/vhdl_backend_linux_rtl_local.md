<!-- codex-research -->
# VHDL Backend + Linux RTL Domain Research

Linux-capable generated RISC-V RTL has a much higher bar than "VHDL compiles".

Primary references:

- Linux RISC-V boot requirements: https://docs.kernel.org/next/arch/riscv/boot.html
- Linux RISC-V boot image header: https://docs.kernel.org/next/riscv/boot-image-header.html
- RISC-V privileged supervisor ISA: https://docs.riscv.org/reference/isa/priv/supervisor.html

## Linux Boot Requirements That Matter

Linux RISC-V boot requires firmware/bootloader setup, not just a CPU reset vector:

- `$a0` must contain current hart ID.
- `$a1` must contain the device tree address.
- `$satp` must be zero on entry.
- Kernel placement must obey PMD alignment: 2 MiB for RV64, 4 MiB for RV32.
- Hardware description must be supplied by DTB or ACPI.
- Firmware must correctly describe reserved memory.

The RISC-V privileged architecture also implies:

- Supervisor mode CSRs and trap behavior.
- Timer, software, and external interrupt paths.
- Page-based translation modes such as Sv32/Sv39.
- `sret`, `sfence.vma`, `satp`, and interrupt delegation behavior.

## Linux-Capable SoC Minimum

| Area | Minimum for practical Linux |
|---|---|
| ISA | RV64GC preferred; RV64IMA minimum for controlled kernel configs. RV32IMA possible but experimental. Include `Zicsr` and `Zifencei`. |
| Privilege | M/S/U modes, traps, CSRs, delegation, `mret`, `sret`, `satp`, `sfence.vma`. |
| MMU | RV32 Sv32 or RV64 Sv39. |
| Timer | CLINT-like `mtime/mtimecmp` or equivalent SBI timer service. |
| Interrupts | PLIC-like external interrupt controller and local software/timer interrupts. |
| UART | DT-described console, usually 16550-compatible for simplest Linux integration. |
| Memory | DRAM at a DT-described physical base, commonly `0x80000000`; boot ROM and MMIO decode. |
| Firmware | Boot ROM plus OpenSBI/U-Boot or direct Linux handoff implementing required register/CSR state. |
| DTB | CPUs, memory, chosen/stdout, interrupt hierarchy, timer, UART, reserved memory, rootfs/initrd. |

## Implication For This Repo

The existing Simple-generated FPGA VHDL scaffold does not meet Linux boot requirements because it lacks CPU execution, privilege, MMU, interrupts, timer, UART device model, memory bus, boot firmware, and DTB generation.

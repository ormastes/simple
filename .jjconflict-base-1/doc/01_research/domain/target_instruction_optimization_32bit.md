<!-- codex-research -->
# Target Instruction Optimization and 32-bit Support - Domain Research

Date: 2026-05-15

## Sources

- Intel 64 and IA-32 Architectures Optimization Reference Manual: https://www.intel.cn/content/dam/doc/manual/64-ia-32-architectures-optimization-manual.pdf
- Intel x86 MOV reference: https://www.felixcloutier.com/x86/mov
- Intel x86 MOVZX reference: https://www.felixcloutier.com/x86/movzx
- System V AMD64 ABI, including LP64 and ILP32/x32 discussion: https://refspecs.linuxbase.org/elf/x86_64-SysV-psABI.pdf
- X32 ABI performance paper summary: https://www.techonline.com/tech-papers/the-x32-abi-a-new-software-convention-for-performance-on-intel-64-processors/
- Evaluation of x32 ABI in LHC applications: https://www.sciencedirect.com/science/article/pii/S1877050913005371
- Agner Fog x86 optimization manuals: https://www.agner.org/optimize/optimizing_assembly.pdf
- RISC-V unprivileged ISA manual: https://docs.riscv.org/reference/isa/_attachments/riscv-unprivileged.pdf
- RISC-V vector extension: https://docs.riscv.org/reference/isa/unpriv/v-st-ext.html
- RISC-V bitmanip extension: https://docs.riscv.org/reference/isa/unpriv/b-st-ext.html
- GCC x86 options: https://gcc.gnu.org/onlinedocs/gcc/x86-Options.html
- GCC AArch64 options and target attributes: https://gcc.gnu.org/onlinedocs/gcc/AArch64-Attributes.html
- GCC RISC-V options: https://gcc.gnu.org/onlinedocs/gcc/RISC-V-Options.html
- Arm A64 instruction-set guide: https://documentation-service.arm.com/static/68cd1a81cccf2a5517018d62
- Arm compiler reference feature identifiers: https://documentation-service.arm.com/static/65f99551b145b95232658cd9

## Findings

### x86-64 using 32-bit forms

In x86-64, 32-bit general-purpose register writes zero the high 32 bits of the corresponding 64-bit register. This makes 32-bit ALU and move forms safe only when the value is proven unsigned or the high bits are dead or known zero. It is not safe for signed 64-bit values, pointers, address computations that can exceed 32 bits, or values crossing calls unless ABI extension rules are satisfied.

32-bit x86-64 instruction forms are often shorter because they avoid REX.W and can use imm32 encodings. They can reduce instruction-cache pressure and code size. Profitability is workload and microarchitecture dependent, so the optimization must be target-gated and benchmarked.

The Linux x32 ABI shows the broader pointer-density idea: use the x86-64 ISA and register ABI benefits while keeping pointers and `long` at 32 bits. That is not the same as native IA-32 and should not be conflated with i386 support.

### Native IA-32 support

Native IA-32 requires an ABI and object-format path, not just narrower instructions. It needs SysV i386 calling convention, 32-bit stack discipline, 32-bit relocation/object emission, register allocation for fewer general-purpose registers, and separate ABI conformance tests.

### ARM and AArch64

AArch64 has separate 32-bit `Wn` and 64-bit `Xn` register views. Writes to `Wn` zero the high half. Like x86-64, this enables safe 32-bit forms for proven 32-bit values. AArch64 feature gating should cover NEON, CRC32, AES, SHA, PMULL, SVE/SVE2 where available. ARM32 should start with scalar, Thumb-2/ARMv7-A, NEON/VFP, CRC, crypto where target features explicitly opt in.

### RISC-V 32/64

RISC-V feature gating should use extension strings and profiles. Initial families should include scalar base, `M`, `A`, `F`, `D`, `C`, bitmanip `Zba/Zbb/Zbs/Zbc`, crypto `Zk*`, vector `V`, and embedded vector subsets where supported. RV32 and RV64 are separate families because pointer size, ABI, and available word operations differ.

## Design conclusion

Use a shared target optimization planner with per-family legality and cost rules, then dispatch only legal/profitable idioms to target lowerers. Add explicit target-family rows for x86-64, x86-32, AArch64, ARM32, RV64, and RV32. Unsupported features must be disabled with a reason or rejected when requested strictly.


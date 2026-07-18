<!-- codex-research -->
# RV32/RV64 Simple-Generated FPGA CPU and Linux — Domain Research

Date: 2026-07-18

<!-- sdn-diagram:id=riscv32_riscv64_fpga_simpleos_production.domain_research -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv32_riscv64_fpga_simpleos_production.domain_research hash=sha256:auto render=ascii
@layout dag
@direction LR

RISC_V_privileged_spec -> Sv32_Sv39_PMP
Linux_boot_requirements -> OpenSBI_DT_interrupts
ACT4 -> ISA_privilege_compliance
RVFI_riscv_formal -> Non_vacuous_RTL_proof
QEMU_virt -> Media_platform_oracle
Buildroot -> Deterministic_login_rootfs
KV260 -> Timing_DRC_DDR_terminal_evidence
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv32_riscv64_fpga_simpleos_production.domain_research hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Research Question

What must a Simple-generated RV32/RV64 soft CPU implement and prove before it
can honestly claim Linux boot, physical FPGA execution, and FPGA-language
qualification?

Only primary specifications, project documentation, or first-party project
repositories are used below.

## Privilege Architecture Is Part of the CPU, Not Boot Metadata

The RISC-V privileged architecture defines M, S, and U modes as the conventional
three-level stack for Unix-like operating systems. M-mode is mandatory; S/U
provide the execution and protection boundary expected by Linux. PMP is the
standard M-mode physical-region protection mechanism and applies to S/U fetch,
load, and store, plus M-mode accesses made under MPRV with a lower effective
privilege. The specification also notes that Sv32 can address 34-bit physical
space, so an RV32 design must not silently truncate translated addresses to
XLEN. Sources: [Privileged architecture introduction](https://docs.riscv.org/reference/isa/priv/priv-intro.html),
[machine-level ISA and PMP](https://docs.riscv.org/reference/isa/priv/machine.html).

Implication for Simple: an enum that says `Sv32` or `Sv39` does not establish a
Linux CPU. Privilege state, CSR semantics, traps, page translation, and PMP must
sit on the executing fetch/data path and be present in emitted RTL.

## Sv32/Sv39 Correctness Surface

The supervisor specification requires more than a page-number lookup:

- valid leaf/non-leaf PTE rules and aligned superpages;
- R/W/X/U permissions, SUM and MXR behavior;
- page-fault causes for fetch/load/store;
- accessed/dirty policy using Svade faults or atomic hardware A/D updates;
- canonical virtual addresses for RV64 modes;
- SATP mode/ASID/root semantics;
- `SFENCE.VMA` ordering and address/ASID-scoped invalidation, although a small
  implementation may legally over-fence globally;
- non-speculative dirty updates and correctly ordered page-table memory effects.

Source: [RISC-V supervisor-level ISA](https://docs.riscv.org/reference/isa/priv/supervisor.html).

The smallest valid first implementation may globally flush its TLB for every
`SFENCE.VMA`, because the specification explicitly permits over-fencing. It may
not ignore the fence, permissions, faults, or A/D contract.

## Linux Entry Contract

Linux requires the boot hart ID in `a0`, the device-tree address in `a1`, and
`satp=0` on entry. Resident firmware and PMP-protected memory must be described
so Linux does not include them in its direct map. Linux then installs its own
temporary and final virtual mappings. Source:
[RISC-V kernel boot requirements](https://docs.kernel.org/next/arch/riscv/boot.html).

The QEMU `virt` machine is a useful reference contract because it exposes
RV32GC/RV64GC CPUs, CLINT, PLIC, NS16550 UART, RAM, and a generated DTB. QEMU
can directly load Linux with its default OpenSBI firmware. It remains a
software/platform oracle, not proof of generated RTL. Source:
[QEMU RISC-V `virt` machine](https://qemu.readthedocs.io/en/master/system/riscv/virt.html).

## OpenSBI and Platform Firmware

OpenSBI is the reference M-mode SBI implementation between platform hardware
and an S-mode OS. Its generic platform depends on a correct FDT and matching
timer/IPI/console drivers. Multi-hart systems require IPI and timer nodes; a
single-hart first target still needs a timer and console contract that matches
the FDT. Sources: [OpenSBI project](https://github.com/riscv-software-src/opensbi),
[generic platform requirements](https://github.com/riscv-software-src/opensbi/blob/master/docs/platform/generic.md).

OpenSBI firmware forms support different loaders. `FW_JUMP` expects a fixed next
stage; `FW_PAYLOAD` embeds it. The previous stage supplies hart ID and an
8-byte-aligned FDT pointer. A deterministic initial qualification image can use
`FW_PAYLOAD` to reduce loader variables, then add `FW_JUMP` once external DDR
and artifact loading are stable. Source:
[OpenSBI firmware documentation](https://github.com/riscv-software-src/opensbi/blob/master/docs/firmware/fw.md).

## Interactive Login Is Stronger Than a Boot Marker

A Linux banner proves the kernel started; it does not prove init, a root
filesystem, terminal input, or basic file access. Buildroot can generate a
small initramfs and configures `/etc/inittab` for a serial getty when the target
port and baud rate are selected. Source:
[Buildroot user manual](https://buildroot.org/downloads/manual/manual.pdf).

The required evidence sequence should be observable and fail closed:

1. OpenSBI banner;
2. Linux version and DT initialization;
3. init/rootfs completion;
4. `login:` prompt;
5. transmitted username and accepted shell prompt;
6. transmitted `ls /`;
7. expected directory names and a unique completion marker.

The same pinned firmware/kernel/DT/rootfs hashes must be used in QEMU, RTL
simulation, and FPGA runs. Otherwise the stages validate different products.

## Compliance and Formal Evidence

RISC-V Architectural Certification Tests use ACT4 with a UDB configuration,
DUT-specific model macros, a linker script, Sail-derived expected results, and
self-checking ELF files. The project explicitly says certification tests are
not a replacement for additional verification. Source:
[RISC-V Architectural Certification Tests](https://github.com/riscv/riscv-arch-test).

`riscv-formal` connects a real processor through RVFI to processor-independent
ISA checks using SymbiYosys. A port list or idle wrapper is not proof; retired
instructions and memory effects must drive RVFI, and the harness must contain
properties/checks over those signals. Source:
[riscv-formal](https://github.com/YosysHQ/riscv-formal).

For this project the evidence layers should be additive:

- focused Simple unit checks for MMU/PMP algorithms;
- differential checks against a software/reference model;
- ACT4 architectural tests for each declared UDB profile;
- RVFI/SymbiYosys proofs over actual emitted RTL;
- Linux boot and terminal scenarios;
- synthesis/timing/resource checks;
- physical-board execution.

## Prior Art for a Linux FPGA Soft CPU

VexRiscv demonstrates the minimum practical RV32 Linux shape: RV32IMA,
supervisor/user support, exceptions, MMU, caches, and an FPGA-oriented pipeline.
Its Linux configuration and published area/frequency results are useful
differential and budgeting references. It may be an oracle, but using its
generated Verilog as the product would not qualify Simple's compiler.
Source: [VexRiscv](https://github.com/SpinalHDL/VexRiscv).

LiteX demonstrates the surrounding SoC expectations: RAM/ROM, timer, UART,
debug, external memory, board/toolchain backends, and Linux-capable CPU
integration. Source: [LiteX](https://github.com/enjoy-digital/litex).

## What “FPGA Design Language” Qualification Should Mean

Established hardware-construction platforms cover more than text emission.
Chisel combines a typed construction language with FIRRTL transformation and
Verilog generation. Amaranth describes a toolchain including the language,
standard library, simulator, and build system across an FPGA workflow. Sources:
[Chisel introduction](https://www.chisel-lang.org/docs.html),
[Chisel/FIRRTL overview](https://www.chisel-lang.org/),
[Amaranth introduction](https://amaranth-lang.org/docs/amaranth/v0.3/intro.html).

For Simple, qualification should therefore require:

- tracked `.spl` as the authoritative hardware source;
- typed hardware boundaries and fail-closed unsupported diagnostics;
- deterministic compiler-generated RTL and source maps;
- executable simulation generated from real test intent;
- formal and differential verification;
- vendor/open-source synthesis and timing/resource reports;
- reproducible bitstream creation and board programming;
- live board execution of a non-trivial workload (here Linux login and `ls`);
- no handwritten or emitted-string parallel CPU that supplies the passing
  result while the Simple source remains disconnected.

## KV260 Physical Evidence Requirements

The connected board is consistent with a KV260 carrier: AMD documents an
integrated FTDI USB UART/JTAG interface and a PMOD header. The board has ample
PL resources, but a Linux softcore still needs a real memory path and terminal
transport. Sources: [KV260 interface guide](https://docs.amd.com/r/en-US/ug1089-kv260-starter-kit/Interfaces),
[KV260 product brief](https://www.amd.com/content/dam/amd/en/documents/products/som/kria/k26/kv260-product-brief.pdf).

AMD's Linux instructions identify the second enumerated FTDI port as the PS
UART and use 115200 8N1. That does not automatically expose a PL softcore UART.
Source: [KV260 UART setup](https://xilinx.github.io/kria-apps-docs/kv260/2022.1/linux_boot/ubuntu_22_04/build/html/docs/uart.html).

An output-only ILA marker is insufficient for the requested interactive login.
The final setup needs either a 3.3 V PMOD UART adapter with RX/TX/GND or a
proven bidirectional PS/PL terminal bridge included in the design and transcript.

## Domain Conclusion

The standards support an incremental implementation: global TLB flushes,
single hart, a small deterministic initramfs, and one board are adequate first
targets. They do not support replacing execution with metadata or PASS markers.
The recommended strategy is compiler-first modular integration of the existing
Simple models, with QEMU as artifact/platform oracle and VexRiscv as optional
differential oracle, followed by generated-RTL and physical-board proof.

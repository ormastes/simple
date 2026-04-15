# Feature Requirements: RV64GC CPU Emulation

**Date:** 2026-04-07
**Status:** Draft
**Namespace:** `hardware.rv64gc.*`
**Depends on:** Existing RV32IMAC emulation patterns (`hardware.rv32imac.*`)

---

## 1. Overview

Full RV64GC hardware emulation in Simple language, matching the QEMU `virt` machine layout. The emulator implements RV64I base integer ISA plus M (multiply/divide), A (atomics), F (single-precision float), D (double-precision float), C (compressed), Zicsr, and Zifencei extensions. Includes M/S/U privilege modes, Sv39 MMU, multicore SMP, and essential device models (UART, CLINT, PLIC).

Follows the spec-first methodology established by the RV32IMAC emulation: tests define API contracts before implementation.

---

## 2. Functional Requirements

### 2.1 RV64I Base Integer ISA

**REQ-RV64GC-001: 64-bit General Purpose Register File**
The emulator shall provide 32 general-purpose registers (x0-x31), each 64 bits wide. Register x0 shall be hardwired to zero (writes are silently discarded, reads always return 0). A 64-bit program counter (PC) shall be maintained separately.

**REQ-RV64GC-002: RV64I Arithmetic and Logic Instructions**
The emulator shall execute all RV64I base integer instructions:
- Arithmetic: ADD, ADDI, SUB, LUI, AUIPC, ADDW, ADDIW, SUBW
- Logic: AND, ANDI, OR, ORI, XOR, XORI
- Shifts: SLL, SLLI, SRL, SRLI, SRA, SRAI, SLLW, SLLIW, SRLW, SRLIW, SRAW, SRAIW
- Compare: SLT, SLTI, SLTU, SLTIU
- All W-suffix instructions shall operate on the lower 32 bits and sign-extend the result to 64 bits.

**REQ-RV64GC-003: Branch and Jump Instructions**
The emulator shall execute: BEQ, BNE, BLT, BGE, BLTU, BGEU, JAL, JALR. Branch targets shall be computed as PC-relative signed offsets. JALR shall mask the LSB of the computed target to zero.

**REQ-RV64GC-004: Load and Store Instructions**
The emulator shall execute: LB, LH, LW, LD, LBU, LHU, LWU, SB, SH, SW, SD. Loads shall sign-extend (LB/LH/LW) or zero-extend (LBU/LHU/LWU) as specified. Misaligned accesses shall raise an address-misaligned exception.

**REQ-RV64GC-005: System Instructions**
The emulator shall execute: ECALL, EBREAK, FENCE, FENCE.I (Zifencei). ECALL shall generate an environment-call exception for the current privilege mode. EBREAK shall generate a breakpoint exception.

### 2.2 M Extension (Multiply/Divide)

**REQ-RV64GC-010: Integer Multiply**
The emulator shall execute: MUL, MULH, MULHSU, MULHU, MULW. MUL returns the lower 64 bits of the 128-bit product. MULH/MULHSU/MULHU return the upper 64 bits (signed x signed, signed x unsigned, unsigned x unsigned respectively). MULW operates on 32-bit operands and sign-extends the result.

**REQ-RV64GC-011: Integer Divide**
The emulator shall execute: DIV, DIVU, REM, REMU, DIVW, DIVUW, REMW, REMUW. Division by zero shall return the architecturally defined values (DIV: -1, DIVU: 2^64-1, REM: dividend, REMU: dividend). Signed overflow (MIN_INT / -1) shall return MIN_INT for DIV and 0 for REM.

### 2.3 A Extension (Atomics)

**REQ-RV64GC-020: Load-Reserved / Store-Conditional**
The emulator shall execute: LR.W, LR.D, SC.W, SC.D. LR shall place a reservation on the accessed address. SC shall succeed (writing memory and returning 0 in rd) only if the reservation is still valid; otherwise it returns a nonzero value. The reservation set shall be tracked per hart.

**REQ-RV64GC-021: Atomic Memory Operations**
The emulator shall execute all AMO instructions for both .W and .D widths: AMOSWAP, AMOADD, AMOAND, AMOOR, AMOXOR, AMOMAX, AMOMAXU, AMOMIN, AMOMINU. Each AMO shall atomically load the value at the address, apply the operation, store the result, and return the original value. Acquire (aq) and release (rl) bits shall be respected for memory ordering.

### 2.4 F Extension (Single-Precision Floating Point)

**REQ-RV64GC-030: Floating-Point Register File**
The emulator shall provide 32 floating-point registers (f0-f31), each 64 bits wide. When the F extension is active without D, only the lower 32 bits are significant; the upper 32 bits shall be filled with 1s (NaN-boxing).

**REQ-RV64GC-031: Single-Precision Arithmetic**
The emulator shall execute: FADD.S, FSUB.S, FMUL.S, FDIV.S, FSQRT.S, FMIN.S, FMAX.S, FMADD.S, FMSUB.S, FNMADD.S, FNMSUB.S. All operations shall comply with IEEE 754-2008 rounding and exception semantics.

**REQ-RV64GC-032: Single-Precision Conversion and Move**
The emulator shall execute: FCVT.W.S, FCVT.WU.S, FCVT.S.W, FCVT.S.WU, FCVT.L.S, FCVT.LU.S, FCVT.S.L, FCVT.S.LU, FMV.X.W, FMV.W.X, FSGNJ.S, FSGNJN.S, FSGNJX.S, FCLASS.S, FEQ.S, FLT.S, FLE.S.

**REQ-RV64GC-033: Single-Precision Load/Store**
The emulator shall execute: FLW, FSW. Misaligned FP loads/stores shall raise an address-misaligned exception.

**REQ-RV64GC-034: Floating-Point CSR (FCSR)**
The emulator shall maintain the FCSR register with fields: fflags (accrued exception flags: NV, DZ, OF, UF, NX) and frm (rounding mode: RNE, RTZ, RDN, RUP, RMM). Dynamic rounding mode (frm=0b111) shall use the frm field.

### 2.5 D Extension (Double-Precision Floating Point)

**REQ-RV64GC-040: Double-Precision Arithmetic**
The emulator shall execute: FADD.D, FSUB.D, FMUL.D, FDIV.D, FSQRT.D, FMIN.D, FMAX.D, FMADD.D, FMSUB.D, FNMADD.D, FNMSUB.D. IEEE 754-2008 compliant.

**REQ-RV64GC-041: Double-Precision Conversion and Move**
The emulator shall execute: FCVT.S.D, FCVT.D.S, FCVT.W.D, FCVT.WU.D, FCVT.D.W, FCVT.D.WU, FCVT.L.D, FCVT.LU.D, FCVT.D.L, FCVT.D.LU, FMV.X.D, FMV.D.X, FSGNJ.D, FSGNJN.D, FSGNJX.D, FCLASS.D, FEQ.D, FLT.D, FLE.D.

**REQ-RV64GC-042: Double-Precision Load/Store**
The emulator shall execute: FLD, FSD.

**REQ-RV64GC-043: NaN-Boxing**
When the D extension is active, single-precision values stored in FP registers shall be NaN-boxed: the upper 32 bits must be all 1s. If a single-precision instruction reads a non-NaN-boxed value, it shall treat the input as the canonical NaN.

### 2.6 C Extension (Compressed Instructions)

**REQ-RV64GC-050: 16-bit Compressed Instruction Decode**
The emulator shall decode 16-bit compressed instructions (identified by bits [1:0] != 0b11) and expand them to their 32-bit equivalents. The PC shall advance by 2 for compressed instructions and by 4 for standard instructions.

**REQ-RV64GC-051: RV64C Instruction Set**
The emulator shall support all RV64C instructions including RV64-specific variants: C.LDSP, C.SDSP, C.LD, C.SD, C.ADDIW, C.SUBW, C.ADDW, in addition to the base RV32C set (C.ADDI, C.LI, C.LUI, C.ADDI16SP, C.SRLI, C.SRAI, C.ANDI, C.SUB, C.XOR, C.OR, C.AND, C.J, C.BEQZ, C.BNEZ, C.LWSP, C.SWSP, C.LW, C.SW, C.MV, C.ADD, C.JALR, C.JR, C.EBREAK, C.NOP).

### 2.7 Zicsr Extension

**REQ-RV64GC-060: CSR Instructions**
The emulator shall execute: CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI. CSR access shall check the privilege level encoded in the CSR address (bits [9:8]) against the current privilege mode. Attempts to access a CSR with insufficient privilege shall raise an illegal-instruction exception. Writes to read-only CSRs (bits [11:10] = 0b11) shall raise an illegal-instruction exception.

**REQ-RV64GC-061: CSR Register File**
The emulator shall implement the following CSR groups with correct read/write masks:

| CSR Group | Addresses | Count | Description |
|-----------|-----------|-------|-------------|
| M-mode trap | mstatus, misa, medeleg, mideleg, mie, mtvec, mcounteren, mscratch, mepc, mcause, mtval, mip | 12 | Machine trap handling |
| M-mode info | mvendorid, marchid, mimpid, mhartid | 4 | Machine information (read-only) |
| M-mode config | menvcfg, mseccfg | 2 | Machine environment config |
| M-mode PMP | pmpcfg0-15, pmpaddr0-63 | Up to 80 | Physical memory protection |
| S-mode trap | sstatus, sie, stvec, scounteren, sscratch, sepc, scause, stval, sip, satp | 10 | Supervisor trap handling |
| S-mode config | senvcfg | 1 | Supervisor environment config |
| U-mode counters | cycle, time, instret | 3 | User-mode read-only counters |
| FP | fflags, frm, fcsr | 3 | Floating-point status |

### 2.8 Privilege Modes

**REQ-RV64GC-070: Machine Mode (M-mode)**
The emulator shall boot in M-mode. M-mode has full access to all CSRs and physical memory. The mstatus register shall track MIE, MPIE, MPP fields correctly across trap entry and MRET.

**REQ-RV64GC-071: Supervisor Mode (S-mode)**
The emulator shall support S-mode with trap delegation via medeleg/mideleg. The sstatus register shall be a restricted view of mstatus. SRET shall restore privilege from SPP and interrupt enable from SPIE.

**REQ-RV64GC-072: User Mode (U-mode)**
The emulator shall support U-mode. U-mode code cannot access S-mode or M-mode CSRs. Counter access shall be gated by mcounteren and scounteren. ECALL from U-mode generates cause 8 (environment call from U-mode).

**REQ-RV64GC-073: Privilege Transitions**
The emulator shall implement correct privilege transitions:
- Trap entry: save current PC to xepc, set xcause, update xstatus (xPIE = xIE, xIE = 0, xPP = current_priv), jump to xtvec.
- MRET: restore privilege from mstatus.MPP, set mstatus.MIE = mstatus.MPIE.
- SRET: restore privilege from sstatus.SPP, set sstatus.SIE = sstatus.SPIE.

**REQ-RV64GC-074: Physical Memory Protection (PMP)**
The emulator shall implement PMP checking for S-mode and U-mode accesses. PMP supports TOR, NAPOT, and NA4 address matching modes. M-mode bypasses PMP unless the L (locked) bit is set.

### 2.9 Sv39 Virtual Memory

**REQ-RV64GC-080: Sv39 Page Table Walk**
The emulator shall implement Sv39 three-level page table translation. Virtual addresses are 39 bits (sign-extended to 64 bits). The page table walk uses VPN[2] (bits 38:30), VPN[1] (bits 29:21), VPN[0] (bits 20:12) to index 512-entry page tables. The satp CSR selects the translation mode (0=Bare, 8=Sv39) and root page table PPN.

**REQ-RV64GC-081: Superpages**
The emulator shall support 1GB gigapages (leaf at level 2) and 2MB megapages (leaf at level 1). Misaligned superpages (non-zero lower PPN bits for the page size) shall generate a page fault.

**REQ-RV64GC-082: Page Table Entry Flags**
The emulator shall check PTE flags: V (valid), R (read), W (write), X (execute), U (user), G (global), A (accessed), D (dirty). A page fault shall be generated if: PTE is not valid, leaf PTE has W=1 but R=0, access violates R/W/X permissions, S-mode accesses U-page without SUM, or U-mode accesses non-U page.

**REQ-RV64GC-083: TLB**
The emulator shall maintain a software TLB to cache recent translations. SFENCE.VMA shall invalidate TLB entries (all, by address, by ASID, or by address+ASID).

**REQ-RV64GC-084: Access and Dirty Bit Management**
The emulator shall set the A bit on the PTE when a page is accessed and the D bit when a page is written. If A or D is not set and the access requires it, the emulator shall either set the bit or raise a page fault (implementation-defined; raising a fault is preferred for simplicity).

### 2.10 QEMU Virt Memory Map

**REQ-RV64GC-090: Memory Map**
The emulator shall implement the QEMU `virt` machine memory map:

| Address Range | Size | Device |
|--------------|------|--------|
| `0x0000_0000 - 0x0000_0FFF` | 4KB | Debug (optional) |
| `0x0010_0000 - 0x0010_0FFF` | 4KB | Test finisher (optional) |
| `0x0200_0000 - 0x0200_FFFF` | 64KB | CLINT |
| `0x0C00_0000 - 0x0FFF_FFFF` | 64MB | PLIC |
| `0x1000_0000 - 0x1000_0FFF` | 4KB | UART0 (NS16550A) |
| `0x1000_1000 - 0x1000_8FFF` | 32KB | virtio (8 slots, optional) |
| `0x2000_0000 - 0x2000_1FFF` | 8KB | FW_CFG (optional) |
| `0x8000_0000 - configurable` | Default 128MB | DRAM |

### 2.11 Device Emulation

**REQ-RV64GC-100: UART (NS16550A)**
The emulator shall implement an NS16550A-compatible UART at `0x1000_0000`. Minimum register set: RBR/THR (data), IER (interrupt enable), IIR/FCR (FIFO control), LCR (line control), LSR (line status). TX shall output characters to a configurable sink (stdout, buffer, or callback). RX shall accept input from a configurable source. The UART shall generate PLIC IRQ 10 when configured.

**REQ-RV64GC-101: CLINT (Core Local Interruptor)**
The emulator shall implement the CLINT at `0x0200_0000`. Registers:
- `msip[hart]` at `0x0200_0000 + 4*hart`: machine software interrupt pending (IPI).
- `mtimecmp[hart]` at `0x0200_4000 + 8*hart`: machine timer compare.
- `mtime` at `0x0200_BFF8`: global timer counter.
The CLINT shall generate a machine timer interrupt when `mtime >= mtimecmp[hart]` and a machine software interrupt when `msip[hart]` bit 0 is set.

**REQ-RV64GC-102: PLIC (Platform-Level Interrupt Controller)**
The emulator shall implement the PLIC at `0x0C00_0000` with the standard register layout:
- Source priority: base + 4*source (sources 1-1023).
- Pending bits: base + 0x1000 (read-only, 32 sources per word).
- Enable bits: base + 0x2000 + 0x80*context.
- Threshold: base + 0x200000 + 0x1000*context.
- Claim/complete: base + 0x200004 + 0x1000*context.
Context numbering: M-mode = hart*2, S-mode = hart*2+1.

### 2.12 Multicore SMP

**REQ-RV64GC-110: Hart State Isolation**
Each hart shall have its own register file (GPR + FPR + PC), CSR state, privilege level, and reservation set. All harts share physical memory and device models.

**REQ-RV64GC-111: Hart Scheduling**
The emulator shall support configurable multi-hart scheduling:
- Round-robin: each hart executes N instructions per quantum.
- Single-step: one instruction per hart per cycle (lockstep for debugging).
- The default configuration shall be 1 hart; additional harts are added via API.

**REQ-RV64GC-112: Inter-Processor Interrupts**
IPI shall be delivered via CLINT `msip` registers. Writing 1 to `msip[hart]` shall set the machine software interrupt pending bit for that hart.

**REQ-RV64GC-113: Memory Ordering**
FENCE instructions shall enforce ordering between harts. In the round-robin scheduler, a FENCE is a no-op (sequential consistency is implicit). In future parallel execution modes, FENCE shall act as a barrier.

---

## 3. API Contract (Spec-First)

The following APIs define the test contracts. Tests shall be written before implementation.

### 3.1 Register File

```simple
# hardware.rv64gc.core.rv64_regfile
struct Rv64RegFile:
    fn read_gpr(index: i64) -> u64       # x0 always returns 0
    fn write_gpr(index: i64, value: u64)  # x0 writes are discarded
    fn read_fpr(index: i64) -> u64        # f0-f31
    fn write_fpr(index: i64, value: u64)
    fn read_pc() -> u64
    fn write_pc(value: u64)
    fn reset()
```

### 3.2 ALU

```simple
# hardware.rv64gc.core.rv64_execute
fn alu_execute(op: AluOp, a: u64, b: u64) -> u64
fn alu_execute_w(op: AluOp, a: u64, b: u64) -> u64  # 32-bit W-variants
```

### 3.3 Decoder

```simple
# hardware.rv64gc.core.rv64_decode
fn decode(instruction: u32) -> Rv64Instruction
fn decode_compressed(half: u16) -> Rv64Instruction
fn is_compressed(half: u16) -> bool
```

### 3.4 CSR

```simple
# hardware.rv64gc.core.rv64_csr
struct Rv64CsrFile:
    fn read(addr: u16, priv_level: PrivMode) -> Result<u64, CsrError>
    fn write(addr: u16, value: u64, priv_level: PrivMode) -> Result<(), CsrError>
    fn set_bits(addr: u16, mask: u64, priv_level: PrivMode) -> Result<u64, CsrError>
    fn clear_bits(addr: u16, mask: u64, priv_level: PrivMode) -> Result<u64, CsrError>
```

### 3.5 MMU

```simple
# hardware.rv64gc.core.rv64_mmu
struct Rv64Mmu:
    fn translate(vaddr: u64, access: MemAccess, priv_level: PrivMode) -> Result<u64, PageFault>
    fn flush_tlb()
    fn flush_tlb_addr(vaddr: u64)
    fn flush_tlb_asid(asid: u16)
```

### 3.6 Hart (Top-Level CPU)

```simple
# hardware.rv64gc.core.rv64_hart
struct Rv64Hart:
    fn step() -> Result<(), TrapInfo>     # Execute one instruction
    fn reset()
    fn get_priv() -> PrivMode
    fn set_priv(mode: PrivMode)
    fn hart_id() -> u64
```

### 3.7 SoC (System-on-Chip)

```simple
# hardware.rv64gc.soc.rv64_soc
struct Rv64Soc:
    fn new(ram_size: u64, num_harts: u64) -> Rv64Soc
    fn step(n: u64)                       # Execute n instructions across all harts
    fn run_until_halt()                   # Run until WFI or breakpoint
    fn load_binary(addr: u64, data: [u8])
    fn read_memory(addr: u64, size: u64) -> [u8]
    fn uart_output() -> text              # Get accumulated UART output
```

---

## 4. Test Plan Structure

Tests follow the RV32IMAC convention with BDD describe/it blocks.

```
test/unit/hardware/rv64gc/
    rv64_regfile_spec.spl       # REQ-RV64GC-001
    rv64_alu_spec.spl           # REQ-RV64GC-002
    rv64_decode_spec.spl        # REQ-RV64GC-002, -003, -004, -050, -051
    rv64_muldiv_spec.spl        # REQ-RV64GC-010, -011
    rv64_atomic_spec.spl        # REQ-RV64GC-020, -021
    rv64_fpu_single_spec.spl    # REQ-RV64GC-030 to -034
    rv64_fpu_double_spec.spl    # REQ-RV64GC-040 to -043
    rv64_compressed_spec.spl    # REQ-RV64GC-050, -051
    rv64_csr_spec.spl           # REQ-RV64GC-060, -061
    rv64_privilege_spec.spl     # REQ-RV64GC-070 to -074
    rv64_mmu_spec.spl           # REQ-RV64GC-080 to -084
    rv64_pipeline_spec.spl      # Integration of decode+execute+writeback

test/unit/hardware/rv64gc/soc/
    rv64_uart_spec.spl          # REQ-RV64GC-100
    rv64_clint_spec.spl         # REQ-RV64GC-101
    rv64_plic_spec.spl          # REQ-RV64GC-102

test/integration/hardware/rv64gc/
    rv64_compliance_spec.spl    # ISA compliance against riscv-tests
    rv64_core_smoke_spec.spl    # Basic instruction execution
    rv64_hello_world_spec.spl   # End-to-end UART hello world
    rv64_smp_spec.spl           # REQ-RV64GC-110 to -113
    rv64_boot_linux_spec.spl    # Boot a minimal Linux kernel (stretch goal)

test/system/
    rv64gc_spec.spl             # Full system test
```

---

## 5. Implementation Phases

| Phase | Scope | Requirements |
|-------|-------|-------------|
| 1 | RV64I core: regfile, decode, ALU, loads/stores, branches | REQ-001 to -005 |
| 2 | M extension + pipeline integration | REQ-010, -011 |
| 3 | Zicsr + privilege modes (M/S/U) | REQ-060 to -074 |
| 4 | Sv39 MMU | REQ-080 to -084 |
| 5 | Device models (UART, CLINT, PLIC) + memory map | REQ-090 to -102 |
| 6 | F + D extensions (floating point) | REQ-030 to -043 |
| 7 | A extension (atomics) | REQ-020, -021 |
| 8 | C extension (compressed) | REQ-050, -051 |
| 9 | Multicore SMP | REQ-110 to -113 |
| 10 | Compliance testing + optimization | All |

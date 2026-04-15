# RV64GC CPU Emulation — Design

**Date:** 2026-04-07
**Architecture:** [rv64gc_cpu](../04_architecture/rv64gc_cpu.md)

## Design Goal

Provide a cycle-approximate RV64GC emulator that can boot supervisor-class
software on the QEMU `virt` memory map. All code in Simple (`.spl`), using
composition and traits, with shared decode logic in `riscv_common/`.

---

## Package Definitions

### rv64_types_pkg

```
XLEN: i64 = 64
FLEN: i64 = 64                # D extension: double-precision width
NUM_REGS: i64 = 32
NUM_FREGS: i64 = 32
NUM_PMP: i64 = 16
PAGE_SIZE: i64 = 4096
SV39_LEVELS: i64 = 3
SV39_VPN_BITS: i64 = 9
SV39_PPN_BITS: i64 = 44
SV39_PAGE_OFFSET: i64 = 12
```

### rv64_isa_pkg

Extends `riscv_isa_pkg` with RV64-specific opcodes:

```
OP_IMM_32: i64 = 0x1B         # ADDIW, SLLIW, SRLIW, SRAIW
OP_32: i64 = 0x3B             # ADDW, SUBW, SLLW, SRLW, SRAW, MULW, DIVW, REMW
```

Plus funct3/funct7 codes for M-extension 64-bit variants and W-suffix ops.

### rv64_csr_addrs

CSR address constants as `i64`. Full list in CSR section below.

### rv64_fp_types_pkg

```
FP_SIGN_BIT_F: i64            # bit 31
FP_SIGN_BIT_D: i64            # bit 63
FP_EXP_MASK_F: i64            # bits [30:23]
FP_EXP_MASK_D: i64            # bits [62:52]
FP_FRAC_MASK_F: i64           # bits [22:0]
FP_FRAC_MASK_D: i64           # bits [51:0]
CANONICAL_NAN_F: i64 = 0x7FC0_0000
CANONICAL_NAN_D: i64 = 0x7FF8_0000_0000_0000
NAN_BOX_MASK: i64 = 0xFFFF_FFFF_0000_0000  # upper 32 bits all-1 for NaN-boxing
```

Rounding mode enum:

```
enum RoundingMode:
    RNE    # Round to Nearest, ties to Even (0b000)
    RTZ    # Round towards Zero (0b001)
    RDN    # Round Down / towards -inf (0b010)
    RUP    # Round Up / towards +inf (0b011)
    RMM    # Round to Nearest, ties to Max Magnitude (0b100)
    DYN    # Dynamic — read from fcsr.frm (0b111)
```

FP exception flags (bitfield in `fcsr.fflags`):

```
FP_NX: i64 = 0x01    # Inexact
FP_UF: i64 = 0x02    # Underflow
FP_OF: i64 = 0x04    # Overflow
FP_DZ: i64 = 0x08    # Divide by Zero
FP_NV: i64 = 0x10    # Invalid Operation
```

---

## Core Classes

### Rv64RegFile

```
class Rv64RegFile:
    regs: List<i64>           # length 32, regs[0] always reads as 0

    fn read(idx: i64) -> i64:
        if idx == 0: 0
        else: self.regs[idx]

    me write(idx: i64, val: i64):
        if idx != 0:
            self.regs[idx] = val
```

### Rv64FpuRegFile

Stores 64-bit values (D-width). Single-precision values are NaN-boxed.

```
class Rv64FpuRegFile:
    regs: List<i64>           # length 32, 64-bit each

    fn read_d(idx: i64) -> i64:
        self.regs[idx]

    fn read_f(idx: i64) -> i64:
        val := self.regs[idx]
        # Check NaN-boxing: upper 32 bits must be all-1
        if (val >> 32) == 0xFFFF_FFFF:
            val & 0xFFFF_FFFF          # return lower 32 bits
        else:
            CANONICAL_NAN_F            # not properly boxed -> canonical NaN

    me write_d(idx: i64, val: i64):
        self.regs[idx] = val

    me write_f(idx: i64, val: i64):
        # NaN-box: set upper 32 bits to all-1
        self.regs[idx] = val | NAN_BOX_MASK
```

### Rv64CsrFile

Sparse CSR storage using a map. Enforces read/write permissions and privilege
checks.

```
class Rv64CsrFile:
    data: Map<i64, i64>       # addr -> value

    fn read(addr: i64, priv_mode: PrivilegeMode) -> Result<i64, CsrError>
    me write(addr: i64, val: i64, priv_mode: PrivilegeMode) -> Result<Unit, CsrError>
    me set_bits(addr: i64, mask: i64, priv_mode: PrivilegeMode) -> Result<i64, CsrError>
    me clear_bits(addr: i64, mask: i64, priv_mode: PrivilegeMode) -> Result<i64, CsrError>
```

**Permission check:** CSR address bits `[11:10]` encode read/write access
(`11` = read-only), bits `[9:8]` encode minimum privilege level.

#### Full CSR List

**M-mode CSRs:**

| Address | Name | Description |
|---------|------|-------------|
| `0x300` | `mstatus` | Machine status (MIE, MPIE, MPP, MPRV, SUM, MXR, TVM, TW, TSR, FS, XS, SD) |
| `0x301` | `misa` | ISA and extensions (MXL=2 for RV64, IMAFDC bits) |
| `0x302` | `medeleg` | Machine exception delegation |
| `0x303` | `mideleg` | Machine interrupt delegation |
| `0x304` | `mie` | Machine interrupt enable (MSIE, MTIE, MEIE, SSIE, STIE, SEIE) |
| `0x305` | `mtvec` | Machine trap vector base (MODE: direct/vectored) |
| `0x306` | `mcounteren` | Machine counter enable |
| `0x310` | `mstatush` | Upper 32 bits of mstatus (RV32 only — not used in RV64) |
| `0x320` | `mcountinhibit` | Counter inhibit |
| `0x340` | `mscratch` | Machine scratch register |
| `0x341` | `mepc` | Machine exception PC |
| `0x342` | `mcause` | Machine trap cause |
| `0x343` | `mtval` | Machine trap value |
| `0x344` | `mip` | Machine interrupt pending |
| `0x34A` | `menvcfg` | Machine environment config |
| `0xF11` | `mvendorid` | Vendor ID (read-only, 0) |
| `0xF12` | `marchid` | Architecture ID (read-only, 0) |
| `0xF13` | `mimpid` | Implementation ID (read-only, 0) |
| `0xF14` | `mhartid` | Hart ID (read-only) |
| `0xF15` | `mconfigptr` | Config pointer (read-only, 0) |

**S-mode CSRs:**

| Address | Name | Description |
|---------|------|-------------|
| `0x100` | `sstatus` | Supervisor status (view of mstatus: SIE, SPIE, SPP, SUM, MXR, FS, XS, SD) |
| `0x104` | `sie` | Supervisor interrupt enable (view of mie: SSIE, STIE, SEIE) |
| `0x105` | `stvec` | Supervisor trap vector base |
| `0x106` | `scounteren` | Supervisor counter enable |
| `0x10A` | `senvcfg` | Supervisor environment config |
| `0x140` | `sscratch` | Supervisor scratch |
| `0x141` | `sepc` | Supervisor exception PC |
| `0x142` | `scause` | Supervisor trap cause |
| `0x143` | `stval` | Supervisor trap value |
| `0x144` | `sip` | Supervisor interrupt pending (view of mip) |
| `0x180` | `satp` | Supervisor address translation and protection (MODE + ASID + PPN) |

**FP CSRs:**

| Address | Name | Description |
|---------|------|-------------|
| `0x001` | `fflags` | FP accrued exception flags (NV, DZ, OF, UF, NX) |
| `0x002` | `frm` | FP dynamic rounding mode |
| `0x003` | `fcsr` | FP control and status (frm + fflags combined) |

**PMP CSRs (16 entries):**

| Address | Name | Description |
|---------|------|-------------|
| `0x3A0`..`0x3A3` | `pmpcfg0`..`pmpcfg3` | PMP configuration (8 entries per register in RV64) |
| `0x3B0`..`0x3BF` | `pmpaddr0`..`pmpaddr15` | PMP address registers (54-bit physical address) |

**Counter CSRs:**

| Address | Name | Description |
|---------|------|-------------|
| `0xB00` | `mcycle` | Machine cycle counter (64-bit) |
| `0xB02` | `minstret` | Machine instructions retired (64-bit) |
| `0xC00` | `cycle` | Cycle counter (U-mode read, if mcounteren permits) |
| `0xC01` | `time` | Timer (memory-mapped CLINT in practice, CSR reads redirect) |
| `0xC02` | `instret` | Instructions retired (U-mode read) |

---

## Extension Modules

### rv64_muldiv (M extension)

Operations on 64-bit integers. `W`-suffix variants operate on lower 32 bits and
sign-extend the 32-bit result.

| Instruction | Operation |
|-------------|-----------|
| `MUL` | `rd = (rs1 * rs2)[63:0]` |
| `MULH` | `rd = (signed(rs1) * signed(rs2))[127:64]` |
| `MULHSU` | `rd = (signed(rs1) * unsigned(rs2))[127:64]` |
| `MULHU` | `rd = (unsigned(rs1) * unsigned(rs2))[127:64]` |
| `DIV` | Signed division (division by zero returns -1) |
| `DIVU` | Unsigned division (division by zero returns 2^64 - 1) |
| `REM` | Signed remainder |
| `REMU` | Unsigned remainder |
| `MULW` | 32-bit multiply, sign-extend to 64 |
| `DIVW`, `DIVUW`, `REMW`, `REMUW` | 32-bit variants |

`MULH` implementation: split each operand into high/low 32-bit halves, perform
four 64-bit partial products, accumulate with carry to extract bits [127:64].

### rv64_atomics (A extension)

```
class ReservationSet64:
    valid: bool
    addr: i64

fn lr_d(hart, bus, addr) -> Result<i64, MemError>:
    # Load-Reserved: read doubleword + set reservation
    val := bus.read64(addr)?
    hart.reservation = ReservationSet64(valid: true, addr: addr)
    val

fn sc_d(hart, bus, addr, val) -> Result<i64, MemError>:
    # Store-Conditional: write if reservation valid + matching
    if hart.reservation.valid and hart.reservation.addr == addr:
        bus.write64(addr, val)?
        hart.reservation.valid = false
        0    # success
    else:
        hart.reservation.valid = false
        1    # failure
```

AMO (Atomic Memory Operations): `AMOSWAP.D`, `AMOADD.D`, `AMOAND.D`,
`AMOOR.D`, `AMOXOR.D`, `AMOMAX[U].D`, `AMOMIN[U].D`. Each reads memory,
computes, writes back atomically (single-threaded emulation makes this trivial).

32-bit variants (`.W`) operate on lower 32 bits and sign-extend.

### rv64_float (F extension) and rv64_double (D extension)

Both use software IEEE 754 arithmetic on `i64` bit patterns. No hardware FP
used — all operations decompose into sign/exponent/mantissa manipulation using
integer shifts and masks.

**Common operations:** `FADD`, `FSUB`, `FMUL`, `FDIV`, `FSQRT`, `FMIN`, `FMAX`,
`FEQ`, `FLT`, `FLE`, `FSGNJ[N|X]`, `FCVT` (int<->float), `FMV` (bitwise),
`FMADD`, `FMSUB`, `FNMADD`, `FNMSUB`.

**Algorithm sketch for FADD.D:**
1. Unpack both operands: sign, exponent (11-bit biased), mantissa (52-bit + implicit 1).
2. Handle special cases: NaN (return canonical NaN, set NV if signaling), infinity,
   zero.
3. Align mantissas: shift smaller exponent's mantissa right by exponent difference.
   Track guard/round/sticky bits for rounding.
4. Add or subtract mantissas depending on signs.
5. Normalize: shift result left/right, adjust exponent. Detect overflow (-> infinity)
   and underflow (-> subnormal or zero).
6. Round according to `frm` rounding mode. Set `fflags` (NX if inexact, OF/UF as
   needed).
7. Pack result: combine sign + biased exponent + mantissa fraction bits.

**NaN-boxing (F in D registers):**
- Writing single-precision: upper 32 bits set to `0xFFFF_FFFF`.
- Reading single-precision: if upper 32 bits are not all-1, return canonical NaN
  (`0x7FC0_0000`).
- Double-precision reads/writes use the full 64 bits as-is.

**Rounding mode dispatch:**
```
fn round(sign: i64, mantissa: i64, guard: i64, round_bit: i64, sticky: i64,
         mode: RoundingMode) -> i64:
    match mode:
        RNE: round_nearest_even(mantissa, guard, round_bit, sticky)
        RTZ: mantissa                    # truncate
        RDN: if sign == 1: round_up(mantissa, guard, round_bit, sticky)
             else: mantissa
        RUP: if sign == 0: round_up(mantissa, guard, round_bit, sticky)
             else: mantissa
        RMM: round_nearest_max_magnitude(mantissa, guard, round_bit, sticky)
        DYN: pass_todo                   # resolved before calling
```

### rv64_zicsr

Implements `CSRRW`, `CSRRS`, `CSRRC` and their immediate variants (`CSRRWI`,
`CSRRSI`, `CSRRCI`).

```
fn exec_csrrw(hart, csr_addr, rs1_val) -> Result<i64, TrapCause>:
    old := hart.csrs.read(csr_addr, hart.priv_mode)?
    hart.csrs.write(csr_addr, rs1_val, hart.priv_mode)?
    old
```

Special handling for `sstatus`/`sie`/`sip` which are views of `mstatus`/`mie`/`mip`
with restricted bit masks.

### rv64_zifencei

`FENCE.I` flushes the TLB and any decode cache. In this emulator, it invalidates
`Rv64Tlb` entries and is otherwise a no-op since there is no instruction cache.

---

## MMU: Sv39 Page Table Walk

### Sv39 Address Format

```
Virtual address (39-bit, sign-extended to 64):
  [63:39] sign extension (must match bit 38)
  [38:30] VPN[2]   (9 bits)
  [29:21] VPN[1]   (9 bits)
  [20:12] VPN[0]   (9 bits)
  [11:0]  page offset (12 bits)

Page Table Entry (64-bit):
  [63:54] reserved
  [53:10] PPN       (44 bits)
  [9:8]   RSW       (reserved for SW)
  [7]     D (dirty)
  [6]     A (accessed)
  [5]     G (global)
  [4]     U (user)
  [3]     X (execute)
  [2]     W (write)
  [1]     R (read)
  [0]     V (valid)
```

### Walk Algorithm

```
fn sv39_translate(bus, satp, vaddr, access_type, priv_mode) -> Result<i64, TrapCause>:
    # 1. Check canonical address (bits [63:39] must equal bit 38)
    if not is_canonical_sv39(vaddr):
        return Err(page_fault(access_type))

    # 2. Extract root PPN from satp
    root_ppn := satp & 0xFFF_FFFF_FFFF       # bits [43:0]
    a := root_ppn * PAGE_SIZE

    # 3. Walk 3 levels (i = 2, 1, 0)
    var i = 2
    var a = a
    while i >= 0:
        # Read PTE from physical memory
        pte_addr := a + vpn_field(vaddr, i) * 8
        pte := bus.read64_physical(pte_addr)?

        # Check V bit
        if (pte & 1) == 0:
            return Err(page_fault(access_type))

        r := (pte >> 1) & 1
        w := (pte >> 2) & 1
        x := (pte >> 3) & 1

        # Leaf PTE? (R or X set)
        if r == 1 or x == 1:
            # Permission checks
            check_permissions(pte, access_type, priv_mode)?
            # Superpage alignment check
            if i > 0:
                check_superpage_alignment(pte, i)?
            # Update A and D bits
            update_ad_bits(bus, pte_addr, pte, access_type)
            # Compose physical address
            return Ok(compose_paddr(pte, vaddr, i))
        else:
            # Non-leaf: W without R is invalid
            if w == 1:
                return Err(page_fault(access_type))
            # Next level
            a = ((pte >> 10) & 0xFFF_FFFF_FFFF) * PAGE_SIZE
            i = i - 1

    # Exhausted levels without finding leaf
    Err(page_fault(access_type))
```

### Rv64Tlb

Simple direct-mapped TLB to cache recent translations.

```
class Rv64Tlb:
    entries: List<TlbEntry>       # fixed size (e.g., 64)
    size: i64

class TlbEntry:
    valid: bool
    vpn: i64                      # virtual page number
    ppn: i64                      # physical page number
    perm: i64                     # R/W/X/U bits
    level: i64                    # superpage level (0=4K, 1=2M, 2=1G)

    fn lookup(vpn: i64) -> Option<TlbEntry>
    me insert(vpn: i64, ppn: i64, perm: i64, level: i64)
    me flush()                    # SFENCE.VMA
    me flush_addr(vpn: i64)       # SFENCE.VMA with rs1
```

### Rv64Pmp

Physical Memory Protection — 16 entries, checked on every physical access
when in S/U mode (or M-mode with MPRV set).

```
class Rv64Pmp:
    cfg: List<i64>                # 16 config bytes (R/W/X/A/L fields)
    addr: List<i64>              # 16 address registers

    fn check(paddr: i64, size: i64, access_type: AccessType,
             priv_mode: PrivilegeMode) -> Result<Unit, PmpError>
```

Address matching modes (A field): OFF, TOR (top of range), NA4 (4-byte),
NAPOT (naturally aligned power-of-2).

---

## Privilege and Trap Handling

### rv64_privilege

```
class Rv64Privilege:
    fn can_access_csr(addr: i64, mode: PrivilegeMode) -> bool:
        required := (addr >> 8) & 3       # bits [9:8]
        mode_val >= required

    fn check_tvm(csrs, mode):             # Trap Virtual Memory
        # Accessing satp in S-mode when TVM=1 raises illegal instruction

    fn check_tw(csrs, mode):              # Timeout Wait
        # WFI in S-mode when TW=1 raises illegal instruction after timeout

    fn check_tsr(csrs, mode):             # Trap SRET
        # SRET in S-mode when TSR=1 raises illegal instruction
```

### rv64_trap — Trap Delegation Algorithm

```
fn take_trap(hart, cause, tval):
    is_interrupt := (cause >> 63) & 1
    cause_code := cause & 0x7FFF_FFFF_FFFF_FFFF

    # Determine target mode
    delegated := false
    if hart.priv_mode != M:
        if is_interrupt == 1:
            delegated = (hart.csrs.read(MIDELEG) >> cause_code) & 1 == 1
        else:
            delegated = (hart.csrs.read(MEDELEG) >> cause_code) & 1 == 1

    if delegated:
        trap_to_s_mode(hart, cause, tval)
    else:
        trap_to_m_mode(hart, cause, tval)

fn trap_to_m_mode(hart, cause, tval):
    # Save state
    hart.csrs.write(MEPC, hart.pc)
    hart.csrs.write(MCAUSE, cause)
    hart.csrs.write(MTVAL, tval)
    # Update mstatus: MPP = current mode, MPIE = MIE, MIE = 0
    mstatus := hart.csrs.read(MSTATUS)
    mstatus = set_field(mstatus, MPP, hart.priv_mode)
    mstatus = set_field(mstatus, MPIE, get_field(mstatus, MIE))
    mstatus = set_field(mstatus, MIE, 0)
    hart.csrs.write(MSTATUS, mstatus)
    # Jump to handler
    hart.priv_mode = M
    hart.pc = compute_tvec(hart.csrs.read(MTVEC), cause)

fn trap_to_s_mode(hart, cause, tval):
    # Same pattern with SEPC, SCAUSE, STVAL, SSTATUS, SPP, SPIE, SIE, STVEC
    hart.csrs.write(SEPC, hart.pc)
    hart.csrs.write(SCAUSE, cause)
    hart.csrs.write(STVAL, tval)
    sstatus := hart.csrs.read(SSTATUS)
    sstatus = set_field(sstatus, SPP, hart.priv_mode)
    sstatus = set_field(sstatus, SPIE, get_field(sstatus, SIE))
    sstatus = set_field(sstatus, SIE, 0)
    hart.csrs.write(SSTATUS, sstatus)
    hart.priv_mode = S
    hart.pc = compute_tvec(hart.csrs.read(STVEC), cause)

fn compute_tvec(tvec, cause) -> i64:
    base := tvec & ~3                     # bits [63:2]
    mode := tvec & 3
    if mode == 1 and (cause >> 63) == 1:  # vectored mode, interrupt
        base + (cause & 0x7FFF_FFFF_FFFF_FFFF) * 4
    else:
        base                              # direct mode
```

### rv64_interrupt — Interrupt Priority

```
fn pending_interrupt(hart) -> Option<i64>:
    mip := hart.csrs.read(MIP)
    mie_reg := hart.csrs.read(MIE)
    enabled := mip & mie_reg

    # Check global interrupt enable
    if hart.priv_mode == M and get_field(mstatus, MIE) == 0:
        return nil
    if hart.priv_mode == S and get_field(sstatus, SIE) == 0:
        # S-mode: only M-mode interrupts can preempt
        enabled = enabled & ~delegated_interrupts()

    # Priority order (highest first): MEI, MSI, MTI, SEI, SSI, STI
    priority := [11, 3, 7, 9, 1, 5]
    for bit in priority:
        if (enabled >> bit) & 1 == 1:
            return Some(bit | (1 << 63))   # interrupt bit set in cause
    nil
```

---

## Multicore (SMP)

### rv64_hart — Single Hart

```
class Rv64Hart:
    hart_id: i64
    pc: i64
    priv_mode: PrivilegeMode
    regs: Rv64RegFile
    fregs: Rv64FpuRegFile
    csrs: Rv64CsrFile
    reservation: ReservationSet64
    wfi: bool
    tlb: Rv64Tlb
    cycle_count: i64
    instret_count: i64

    fn step(bus: Rv64Bus) -> Result<Unit, HaltReason>:
        # Check pending interrupts
        if val irq = pending_interrupt(self):
            take_trap(self, irq, 0)
        if self.wfi:
            self.cycle_count = self.cycle_count + 1
            return Ok(())
        # Fetch
        raw := fetch(self, bus)?
        # Decode
        op := decode(raw)?
        # Execute + writeback (updates regs, pc, csrs)
        execute(self, bus, op)?
        self.cycle_count = self.cycle_count + 1
        self.instret_count = self.instret_count + 1
        Ok(())
```

### rv64_hart_manager — Round-Robin Stepping

```
class Rv64HartManager:
    harts: List<Rv64Hart>
    current: i64

    fn step_all(bus: Rv64Bus) -> Result<Unit, HaltReason>:
        for hart in self.harts:
            hart.step(bus)?
        Ok(())

    fn step_one(bus: Rv64Bus) -> Result<Unit, HaltReason>:
        # Round-robin: advance one hart per call
        self.harts[self.current].step(bus)?
        self.current = (self.current + 1) % self.harts.len()
        Ok(())
```

**Atomic memory ordering:** Since emulation is single-threaded with round-robin
stepping, all memory operations are sequentially consistent by construction.
`LR/SC` correctness relies on the `ReservationSet64` per hart — any hart's
store (or another hart's `SC`) to the reserved address invalidates the
reservation. The hart manager invalidates reservations on cross-hart stores:

```
fn invalidate_reservations(harts, addr: i64, exclude_hart: i64):
    for hart in harts:
        if hart.hart_id != exclude_hart:
            if hart.reservation.valid and hart.reservation.addr == addr:
                hart.reservation.valid = false
```

**IPI (Inter-Processor Interrupt) via CLINT:** Hart A writes to
`CLINT.msip[hart_B]` which sets the MSIP bit in hart B's `mip` register.
On the next `step()` of hart B, `pending_interrupt()` detects the software
interrupt and traps.

---

## Peripheral Modules

### rv64_uart (16550-compatible)

```
class Rv64Uart:
    rx_fifo: List<i64>          # receive buffer
    tx_fifo: List<i64>          # transmit buffer
    ier: i64                     # Interrupt Enable Register
    iir: i64                     # Interrupt Identification Register
    lcr: i64                     # Line Control Register
    mcr: i64                     # Modem Control Register
    lsr: i64                     # Line Status Register
    dll: i64                     # Divisor Latch Low
    dlm: i64                     # Divisor Latch High

    fn read(offset: i64) -> i64      # register read (0x00..0x07)
    me write(offset: i64, val: i64)  # register write
    me push_input(byte: i64)         # external input -> rx_fifo
    fn has_interrupt() -> bool        # check if UART interrupt pending
```

Offset 0 = THR/RBR (transmit/receive holding), offset 5 = LSR.
DLAB (bit 7 of LCR) switches offsets 0/1 to divisor latch registers.

### rv64_clint (Core Local Interruptor)

```
class Rv64Clint:
    msip: List<i64>             # software interrupt pending, per hart
    mtimecmp: List<i64>         # timer compare, per hart
    mtime: i64                  # global timer

    fn read(addr: i64) -> i64
    me write(addr: i64, val: i64)
    me tick()                   # increment mtime, check mtimecmp
```

**Address map within CLINT (relative to base `0x0200_0000`):**
- `0x0000`..`0x3FFF`: `msip[hart]` (4 bytes each, at `hart * 4`)
- `0x4000`..`0xBFF7`: `mtimecmp[hart]` (8 bytes each, at `0x4000 + hart * 8`)
- `0xBFF8`: `mtime` (8 bytes)

Timer interrupt: when `mtime >= mtimecmp[hart]`, set MTIP in that hart's `mip`.

### rv64_plic (Platform-Level Interrupt Controller)

```
class Rv64Plic:
    priority: List<i64>         # source priority (1..1023)
    pending: List<i64>          # pending bitfield
    enable: List<List<i64>>     # enable bits per context
    threshold: List<i64>        # threshold per context
    claim: List<i64>            # claimed source per context

    fn read(addr: i64) -> i64
    me write(addr: i64, val: i64)
    fn highest_pending(context: i64) -> Option<i64>
    me claim_interrupt(context: i64) -> i64
    me complete_interrupt(context: i64, source: i64)
```

PLIC context = hart_id * 2 (M-mode) or hart_id * 2 + 1 (S-mode).

---

## Bus Address Decode

```
class Rv64Bus:
    ram: Rv64Ram
    clint: Rv64Clint
    plic: Rv64Plic
    uart: Rv64Uart

    fn read8(addr: i64) -> Result<i64, BusError>:
        route(addr, |dev, off| dev.read8(off))

    fn read32(addr: i64) -> Result<i64, BusError>:
        route(addr, |dev, off| dev.read32(off))

    fn read64(addr: i64) -> Result<i64, BusError>:
        route(addr, |dev, off| dev.read64(off))

    me write8(addr: i64, val: i64) -> Result<Unit, BusError>:
        route_mut(addr, |dev, off| dev.write8(off, val))

    # write32, write64 analogous

    fn route(addr: i64, f) -> Result<i64, BusError>:
        if addr >= 0x8000_0000:
            f(self.ram, addr - 0x8000_0000)
        else if addr >= 0x1000_0000 and addr < 0x1000_0100:
            f(self.uart, addr - 0x1000_0000)
        else if addr >= 0x0C00_0000 and addr < 0x1000_0000:
            f(self.plic, addr - 0x0C00_0000)
        else if addr >= 0x0200_0000 and addr < 0x0201_0000:
            f(self.clint, addr - 0x0200_0000)
        else:
            Err(BusError(addr: addr, kind: AccessFault))
```

RAM checked first (most frequent access). Remaining devices in descending
address order.

---

## Top-Level Assembly

### rv64_soc

```
class Rv64Soc:
    harts: Rv64HartManager
    bus: Rv64Bus
    ram: Rv64Ram
    clint: Rv64Clint
    plic: Rv64Plic
    uart: Rv64Uart

    static fn create(config: SocConfig) -> Rv64Soc:
        ram := Rv64Ram(size: config.ram_size)
        clint := Rv64Clint(num_harts: config.num_harts)
        plic := Rv64Plic(num_sources: config.num_irq_sources)
        uart := Rv64Uart()
        bus := Rv64Bus(ram: ram, clint: clint, plic: plic, uart: uart)
        hart_list := [for i in 0..config.num_harts:
            Rv64Hart(hart_id: i, pc: config.reset_vector, priv_mode: M)]
        harts := Rv64HartManager(harts: hart_list, current: 0)
        Rv64Soc(harts: harts, bus: bus, ram: ram, clint: clint,
                plic: plic, uart: uart)
```

### rv64_machine

```
class Rv64Machine:
    soc: Rv64Soc
    config: MachineConfig

    fn load_binary(data: List<i64>, addr: i64):
        # Write data bytes into RAM at addr
        for i in 0..data.len():
            self.soc.ram.write8(addr - 0x8000_0000 + i, data[i])

    fn run(max_cycles: i64) -> Result<Unit, HaltReason>:
        var cycles = 0
        while cycles < max_cycles:
            self.soc.clint.tick()
            self.soc.harts.step_all(self.soc.bus)?
            # Check UART output
            while self.soc.uart.tx_fifo.len() > 0:
                emit(self.soc.uart.tx_fifo.pop_front())
            cycles = cycles + 1
        Ok(())

class MachineConfig:
    num_harts: i64              # default 1
    ram_size: i64               # default 128 MiB
    reset_vector: i64           # default 0x8000_0000
    dtb_addr: i64               # device tree blob address
```

---

## Non-Goals

- No out-of-order execution or pipeline simulation (instruction-accurate, not
  cycle-accurate).
- No VirtIO devices (future extension).
- No S-mode timer via sstc extension (uses SBI ecall to M-mode for timer setup).
- No hypervisor extension (H).
- No vector extension (V).

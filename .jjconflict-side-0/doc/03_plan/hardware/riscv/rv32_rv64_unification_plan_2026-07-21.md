# RV32/RV64 RTL Unification Plan (2026-07-21)

**Status:** P1 Architecture Plan (Not a quick fix)  
**Bug:** RISCV-001 from audit  
**Scope:** Generated-RTL lane only (`src/lib/hardware/rv32i_rtl/`, `src/lib/hardware/rv64gc_rtl/`)  
**Excludes:** Production FPGA handwritten VHDL cores (`examples/09_embedded/fpga_riscv/`)

---

## Verification Findings

### Path Status
**REAL PATHS CONFIRMED:**
- `src/lib/hardware/rv32i_rtl/` — 12 .spl files, 2,508 lines
- `src/lib/hardware/rv64gc_rtl/` — 13 .spl files, 3,164 lines  
- **Total:** 5,672 lines of generated RTL

**NOT PLACEHOLDERS:** One minor placeholder comment found in RV64 decode.spl about M extension, but these are substantial implementations with real RTL logic.

### Module Overlap Analysis
**Shared modules (10):** alu.spl, core.spl, csr.spl, csr_s.spl, decode.spl, __init__.spl, lsu.spl, pkg.spl, regfile.spl, trap.spl

**RV32-only:** rvfi.spl (formal verification interface), mmu_sv32.spl (Sv32 MMU)

**RV64-only:** atomics.spl (A extension), mul_div.spl (M extension), mmu_sv39.spl (Sv39 MMU)

### Divergence Points (from pkg.spl diff analysis)
1. **Opcode definitions:** RV64 extends RV32 with OP_OP_IMM_32 (W-suffix), OP_OP_32, OP_AMO
2. **ALU operations:** RV64 adds W-suffix ops (operate on low 32 bits, sign-extend result)
3. **Load/store:** RV64 adds LD/LWU/SD (64-bit variants)
4. **Address spaces:** Sv32 vs Sv39 MMU
5. **Extensions:** RV64 has M/A/C CSR and privilege state; RV32 is M-mode baremetal
6. **Register width:** u32 vs i64 for program counters and operands

### Estimated Shared Code
Based on module overlap and structural analysis: **~70-80% shared potential** if unified around XLEN parameter.

---

## Unification Architecture

### Target Structure
```
src/lib/hardware/riscv_rtl/
├── common/
│   ├── pkg.spl              # XLEN-parameterized constants
│   ├── alu.spl              # Width-generic ALU with W-suffix support
│   ├── decode.spl           # Shared decoder with extension gating
│   ├── regfile.spl          # Parameterized register file
│   ├── csr.spl              # Base CSR file (M-mode only)
│   ├── trap.spl             # Shared trap handling
│   └── lsu.spl              # Shared load-store unit
├── xlen_spec.spl            # RiscvXlenSpec abstraction
├── rv32/
│   ├── core.spl             # RV32I-specific core integration
│   ├── mmu_sv32.spl         # Sv32 MMU (RV32-only)
│   ├── rvfi.spl             # RV32 formal verification
│   └── csr_s.spl            # Optional S-mode (RV32 only, minimal)
└── rv64/
    ├── core.spl             # RV64GC-specific core integration
    ├── mmu_sv39.spl         # Sv39 MMU (RV64-only)
    ├── atomics.spl          # A extension (RV64-only)
    ├── mul_div.spl          # M extension (RV64-only)
    └── csr_s.spl            # Full S-mode (RV64)
```

### RiscvXlenSpec Abstraction
```spl
# Core XLEN specification
struct RiscvXlenSpec:
    xlen_bits: u32        # 32 or 64
    xlen_type: Type        # u32 or i64
    addr_type: Type        # Physical address type
    pc_type: Type          # Program counter type
    has_m_extension: bool
    has_a_extension: bool
    has_s_mode: bool
    mmu_variant: string   # "none" | "sv32" | "sv39"

# Singleton specifications
val RV32I_SPEC: RiscvXlenSpec = RiscvXlenSpec(
    xlen_bits: 32,
    xlen_type: u32,
    addr_type: u32,
    pc_type: u32,
    has_m_extension: false,
    has_a_extension: false,
    has_s_mode: false,
    mmu_variant: "sv32"
)

val RV64GC_SPEC: RiscvXlenSpec = RiscvXlenSpec(
    xlen_bits: 64,
    xlen_type: i64,
    addr_type: i64,
    pc_type: i64,
    has_m_extension: true,
    has_a_extension: true,
    has_s_mode: true,
    mmu_variant: "sv39"
)
```

---

## Migration Sequencing

### Phase 1: Foundation (2-3 weeks)
1. **Create common infrastructure** in `src/lib/hardware/riscv_rtl/common/`
2. **Implement RiscvXlenSpec** abstraction with RV32I/RV64GC singletons
3. **Move shared modules** (alu, decode, regfile, csr, trap, lsu, pkg) to common/
4. **Parameterize common modules** to accept RiscvXlenSpec at compile time
5. **Add compiler support** for generic specialization to concrete types

### Phase 2: RV32 Port (1 week)
1. **Create rv32/ directory** structure
2. **Move RV32-specific modules** (core, mmu_sv32, rvfi, csr_s)
3. **Update imports** from `rv32i_rtl.*` to `riscv_rtl.common.*` + `riscv_rtl.rv32.*`
4. **Verify RV32 tests pass** against new structure

### Phase 3: RV64 Port (1-2 weeks)
1. **Create rv64/ directory** structure  
2. **Move RV64-specific modules** (core, mmu_sv39, atomics, mul_div, csr_s)
3. **Add extension gating** for M/A/C in decoder and ALU
4. **Update imports** to use common + rv64 paths
5. **Verify RV64 tests pass** including M/A extensions

### Phase 4: Integration & Cleanup (1 week)
1. **Remove old directories** `rv32i_rtl/` and `rv64gc_rtl/`
2. **Update all imports** across codebase
3. **Run full test suite** (including production FPGA path)
4. **Documentation updates** for new structure

**Total estimated time:** 5-7 weeks

---

## Key Divergence Points to Address

### Decoder
- **Shared:** Base I instruction decoding (opcode, funct3, funct7)
- **Divergent:** RV64 W-suffix instructions (ADDIW, SLLIW, etc.), RV64 AMO opcodes
- **Solution:** Extension gating in decoder based on `has_m_extension`, `has_a_extension`

### ALU
- **Shared:** Basic integer ops (ADD, SUB, AND, OR, XOR, shifts, compare)
- **Divergent:** RV64 W-suffix ops (32-bit ops with sign-extension), RV64 64-bit shifts
- **Solution:** Width-generic ALU with `xlen_bits` parameter controlling overflow and sign-extension behavior

### Register File
- **Shared:** 32 general-purpose registers, read/write logic
- **Divergent:** Register width (u32 vs i64), zero-extension behavior
- **Solution:** Parameterized `RegFile<XLEN>` type

### LSU
- **Shared:** Load/store alignment checks, memory interface
- **Divergent:** RV64 64-bit loads/stores (LD, SD, LWU), RV32 32-bit only
- **Solution:** Width-generic LSU with `xlen_bits` controlling max transfer size

### CSR
- **Shared:** M-mode CSR access patterns, mstatus/mie/mip/mcause/mepcmtvec
- **Divergent:** RV64 S-mode CSRs, RV64 mstatus.FS for FPU, RV64 privilege modes
- **Solution:** Base CSR file + optional S-mode extension layer

### MMU
- **Divergent:** Sv32 vs Sv39 page table formats, address translation width
- **Solution:** Separate mmu_sv32.spl and mmu_sv39.spl with shared MMU interface trait

### Core State
- **Shared:** Semihosting detection, halt logic
- **Divergent:** RV64 adds M/A extension state, privilege mode, wider PC
- **Solution:** Parameterized `CoreState<XLEN, SPEC>` with optional extension state

---

## Acceptance Criteria

1. **Code sharing:** ≥85% of CPU source shared between RV32 and RV64
2. **No duplicated modules:** Decoder, ALU, regfile, LSU, CSR, trap logic unified
3. **RV32I correctness:** All existing RV32 tests pass
4. **RV64GC correctness:** All existing RV64 tests pass (including M/A extensions)
5. **Extension isolation:** RV64-only ops absent from RV32 build
6. **Width correctness:** W-suffix ops only in RV64, correct sign-extension behavior
7. **Manifest accuracy:** Generated RTL correctly reports XLEN and capabilities

---

## Dependencies & Risks

### Dependencies
- **Compiler generic support:** Requires working generic specialization (BUG-COMPILER-001)
- **AOP weaving:** Must not break on unified modules (BUG-COMPILER-002)
- **Verification infrastructure:** RVFI and test harnesses must support new structure

### Risks
- **Compiler instability:** If generic specialization fails, fall back to manual code generation
- **Performance impact:** Generic compilation may slow bootstrap; measure before committing
- **Regression window:** Large refactor may introduce subtle bugs; extensive testing required

---

## Next Steps

1. **Confirm compiler generic support** is sufficient for this unification (address BUG-COMPILER-001 first)
2. **Prototype RiscvXlenSpec** in a separate branch to validate approach
3. **Measure bootstrap performance** impact of unified generics
4. **Create verification test suite** for both RV32 and RV64 before migration
5. **Execute phased migration** with test gates at each phase

**This plan should be filed as P1 work, not executed immediately. Address higher-priority audit bugs first (RISCV-004, RISCV-007, VERIFY-001).**

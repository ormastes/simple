# Remote JIT Execution - Combination Matrix

**Date:** 2026-02-05
**Status:** Design Complete

---

## 1. Target × Debugger Matrix

### 1.1 All Combinations

| ID | Target | Debugger | Transport | HW BP | Status | Priority |
|----|--------|----------|-----------|-------|--------|----------|
| **C1** | RISC-V32 | GDB | TCP (QEMU) | 4 | **Implement** | **P0** |
| **C2** | RISC-V32 | TRACE32 | RCL/TCP | 4 | **Implement** | **P1** |
| C3 | RISC-V32 | GDB | TCP (OpenOCD) | 4 | Design | P2 |
| C4 | RISC-V32 | GDB | Serial | 4 | Design | P3 |
| **C5** | ARM32 | GDB | TCP (QEMU) | 6 | Design | P2 |
| **C6** | ARM32 | TRACE32 | RCL/TCP | 6 | Design | P2 |
| C7 | ARM32 | GDB | TCP (OpenOCD) | 6 | Design | P3 |
| C8 | ARM32 | GDB | Serial | 6 | Design | P3 |

### 1.2 Implementation Priorities

```
P0 (Must Have):
├── C1: RISC-V32 + GDB + QEMU
│   └── Foundation for all other work
│
P1 (Should Have):
├── C2: RISC-V32 + TRACE32
│   └── Validates debugger abstraction
│
P2 (Nice to Have):
├── C5: ARM32 + GDB + QEMU
├── C6: ARM32 + TRACE32
│   └── Validates target abstraction
│
P3 (Future):
├── C3, C4, C7, C8
│   └── Production hardware support
```

---

## 2. Architecture Component Matrix

### 2.1 Target Components

| Component | RISC-V32 | ARM32 | Notes |
|-----------|----------|-------|-------|
| Register count | 33 | 17 | x0-x31+PC vs R0-R15+CPSR |
| Register size | 4 bytes | 4 bytes | Both 32-bit |
| PC index | 32 | 15 | Different positions |
| SP index | 2 (x2) | 13 (R13) | Different |
| Return reg | 10 (a0) | 0 (R0) | Different |
| Arg regs | a0-a7 | R0-R3 | 8 vs 4 |
| EBREAK/BKPT | 0x00100073 | 0xBE00 | Different |
| Instruction align | 2 (C ext) | 2 (Thumb) | Same |

### 2.2 Debugger Components

| Component | GDB RSP | TRACE32 | Notes |
|-----------|---------|---------|-------|
| Transport | TCP socket | TCP/API | Both TCP |
| Protocol | Text packets | Commands | Different |
| Memory read | `m addr,len` | `Data.dump` | Different syntax |
| Memory write | `M addr,len:data` | `Data.Set` | Different syntax |
| Register read | `p regnum` | `Register(name)` | Index vs name |
| Breakpoint set | `Z1,addr,kind` | `Break.Set /Hard` | Different |
| Continue | `c` | `Go` | Different |
| Single step | `s` | `Step` | Different |
| Halt | Ctrl-C (0x03) | `Break` | Different |

### 2.3 HW Breakpoint Components

| Component | RISC-V32 | ARM32 | Notes |
|-----------|----------|-------|-------|
| Instruction BP | 2-4 triggers | 6-8 FPB | Different count |
| Data watchpoint | shared | 4 DWT | Different |
| Total available | 4 (QEMU) | 10-12 | Different |
| Configuration | CSR tdata1/2 | FP_COMPn/DWT | Different registers |
| Sharing needed | **Yes** | Optional | RISC-V more constrained |

---

## 3. Code Sharing Matrix

### 3.1 Shared Components (Target-Agnostic)

| Component | File | Shared By |
|-----------|------|-----------|
| Error types | `error.spl` | All |
| Common types | `types.spl` | All |
| Target trait | `target/mod.spl` | All targets |
| Debugger trait | `debugger/mod.spl` | All debuggers |
| BP Manager | `breakpoint/mod.spl` | All combinations |
| Hit Predictor | `breakpoint/predictor.spl` | All combinations |
| Exec Manager | `manager.spl` | All combinations |

### 3.2 Target-Specific Components

| Component | RISC-V32 | ARM32 |
|-----------|----------|-------|
| Target impl | `target/riscv32.spl` | `target/arm32.spl` |
| Code gen | `codegen/riscv32_gen.spl` | `codegen/arm32_gen.spl` |
| Register names | RISC-V ABI | ARM AAPCS |
| Instruction encoding | RV32IMAC | Thumb-2 |

### 3.3 Debugger-Specific Components

| Component | GDB | TRACE32 |
|-----------|-----|---------|
| Debugger impl | `debugger/gdb.spl` | `debugger/trace32.spl` |
| Packet layer | `debugger/gdb_packet.spl` | N/A (direct API) |
| FFI bindings | `socket.spl` | `trace32_ffi.spl` |
| Protocol handling | RSP encoding | T32 command strings |

---

## 4. Feature Support Matrix

### 4.1 Core Features

| Feature | C1 | C2 | C5 | C6 | Notes |
|---------|----|----|----|----|-------|
| Memory read | ✅ | ✅ | ✅ | ✅ | All support |
| Memory write | ✅ | ✅ | ✅ | ✅ | All support |
| Register read | ✅ | ✅ | ✅ | ✅ | All support |
| Register write | ✅ | ✅ | ✅ | ✅ | All support |
| Continue | ✅ | ✅ | ✅ | ✅ | All support |
| Halt | ✅ | ✅ | ✅ | ✅ | All support |
| Single step | ✅ | ✅ | ✅ | ✅ | All support |

### 4.2 Breakpoint Features

| Feature | C1 | C2 | C5 | C6 | Notes |
|---------|----|----|----|----|-------|
| HW instruction BP | ✅ | ✅ | ✅ | ✅ | Core feature |
| HW read watchpoint | ✅ | ✅ | ✅ | ✅ | All support |
| HW write watchpoint | ✅ | ✅ | ✅ | ✅ | All support |
| HW access watchpoint | ✅ | ✅ | ✅ | ✅ | All support |
| SW BP sharing | ✅ | ✅ | ✅ | ✅ | Our innovation |
| Conditional BP | ⏳ | ⏳ | ⏳ | ⏳ | Future work |

### 4.3 Advanced Features

| Feature | C1 | C2 | C5 | C6 | Notes |
|---------|----|----|----|----|-------|
| Flash programming | ❌ | ✅ | ❌ | ✅ | TRACE32 only |
| Trace buffer | ❌ | ✅ | ❌ | ✅ | TRACE32 only |
| Coverage analysis | ❌ | ✅ | ❌ | ✅ | TRACE32 only |
| Multi-core | ❌ | ⏳ | ❌ | ⏳ | Future |
| RTOS awareness | ❌ | ⏳ | ❌ | ⏳ | Future |

---

## 5. Test Coverage Matrix

### 5.1 Unit Tests (No Hardware)

| Test | Target | Status |
|------|--------|--------|
| RiscV32Target | RISC-V32 | ✅ Implement |
| Arm32Target | ARM32 | ⏳ Design |
| GdbPacketLayer | - | ✅ Implement |
| BreakpointManager | - | ✅ Implement |
| HitPredictor | - | ✅ Implement |

### 5.2 Integration Tests (QEMU)

| Test | Combination | Status |
|------|-------------|--------|
| GDB connect | C1 | ✅ Implement |
| GDB memory ops | C1 | ✅ Implement |
| GDB register ops | C1 | ✅ Implement |
| GDB breakpoints | C1 | ✅ Implement |
| BP sharing (10 BP) | C1 | ✅ Implement |
| Code execution | C1 | ✅ Implement |
| ARM32 + QEMU | C5 | ⏳ Design |

### 5.3 Hardware Tests

| Test | Combination | Status |
|------|-------------|--------|
| TRACE32 connect | C2 | ⏳ If available |
| TRACE32 memory | C2 | ⏳ If available |
| Real RISC-V board | C1/C2 | ⏳ If available |
| Real ARM board | C5/C6 | ⏳ If available |

---

## 6. API Compatibility Matrix

### 6.1 Common API (All Combinations)

```simple
# These methods work identically across all combinations
trait Debugger:
    fn connect(config: DebugConfig) -> Result<Self, Error>
    fn disconnect()
    fn read_memory(addr: u64, size: usize) -> Result<[u8], Error>
    fn write_memory(addr: u64, data: [u8]) -> Result<(), Error>
    fn read_register(index: usize) -> Result<u64, Error>
    fn write_register(index: usize, value: u64) -> Result<(), Error>
    fn resume() -> Result<(), Error>
    fn halt() -> Result<(), Error>
    fn single_step() -> Result<(), Error>
    fn set_hw_breakpoint(addr: u64, type: BpType) -> Result<(), Error>
    fn clear_hw_breakpoint(addr: u64, type: BpType) -> Result<(), Error>
```

### 6.2 Combination-Specific API

| API | C1 (RV+GDB) | C2 (RV+T32) | C5 (ARM+GDB) | C6 (ARM+T32) |
|-----|-------------|-------------|--------------|--------------|
| `connect_qemu()` | ✅ | ❌ | ✅ | ❌ |
| `connect_trace32()` | ❌ | ✅ | ❌ | ✅ |
| `connect_openocd()` | ⏳ | ❌ | ⏳ | ❌ |
| `flash_program()` | ❌ | ✅ | ❌ | ✅ |
| `read_trace()` | ❌ | ✅ | ❌ | ✅ |

---

## 7. Performance Comparison Matrix

### 7.1 Latency (estimated)

| Operation | C1 (QEMU) | C2 (T32 Sim) | C1 (Real) | C2 (Real) |
|-----------|-----------|--------------|-----------|-----------|
| Connect | 10ms | 50ms | 100ms | 200ms |
| Read 4B | 0.5ms | 1ms | 2ms | 0.5ms |
| Write 4B | 0.5ms | 1ms | 2ms | 0.5ms |
| Read 1KB | 5ms | 10ms | 50ms | 5ms |
| Write 1KB | 5ms | 10ms | 50ms | 5ms |
| Set BP | 1ms | 2ms | 5ms | 1ms |
| Resume | 0.5ms | 1ms | 2ms | 0.5ms |

### 7.2 BP Sharing Overhead

| Scenario | 1 BP | 5 BP | 10 BP | 20 BP |
|----------|------|------|-------|-------|
| Avg rotations | 0 | 2.5 | 5 | 10 |
| With predictor | 0 | 1 | 2 | 4 |
| Improvement | - | 60% | 60% | 60% |

---

## 8. Dependency Matrix

### 8.1 External Dependencies

| Dependency | C1 | C2 | C5 | C6 | Notes |
|------------|----|----|----|----|-------|
| QEMU | ✅ | ❌ | ✅ | ❌ | Free, open source |
| TRACE32 | ❌ | ✅ | ❌ | ✅ | Commercial license |
| OpenOCD | ⏳ | ❌ | ⏳ | ❌ | Free, open source |
| Real hardware | ❌ | ⏳ | ❌ | ⏳ | Optional |

### 8.2 Internal Dependencies

```
┌──────────────────┐
│ manager.spl      │ Depends on all below
├──────────────────┤
│ breakpoint/*.spl │ Depends on debugger trait
├──────────────────┤
│ debugger/*.spl   │ GDB or TRACE32 implementation
├──────────────────┤
│ target/*.spl     │ RISC-V32 or ARM32 target
├──────────────────┤
│ types.spl        │ Common types
│ error.spl        │ Error types
│ socket.spl       │ TCP FFI (for GDB)
│ trace32_ffi.spl  │ T32 FFI (for TRACE32)
└──────────────────┘
```

---

## 9. Migration Path

### 9.1 Adding New Target

To add a new target (e.g., MIPS32):

1. Create `src/remote/target/mips32.spl`
2. Implement `Target` trait
3. Add register definitions
4. Add instruction encoding for EBREAK equivalent
5. Add code generator (optional)
6. Add tests

**Effort:** ~200 lines, 1-2 days

### 9.2 Adding New Debugger

To add a new debugger (e.g., J-Link):

1. Create `src/remote/debugger/jlink.spl`
2. Implement `Debugger` trait
3. Add J-Link-specific protocol handling
4. Add FFI bindings for J-Link SDK
5. Add tests

**Effort:** ~500 lines, 3-5 days

### 9.3 Adding New Transport

To add a new transport (e.g., USB):

1. Create FFI bindings for USB
2. Add transport abstraction layer
3. Modify GDB debugger to use transport abstraction
4. Add USB-specific error handling

**Effort:** ~300 lines, 2-3 days

---

## 10. Summary

### 10.1 What We're Building

| Phase | Deliverable | Combinations |
|-------|-------------|--------------|
| P0 | Core framework + RISC-V32 + GDB | C1 |
| P1 | TRACE32 support | C1, C2 |
| P2 | ARM32 support | C1, C2, C5, C6 |
| P3 | Production hardware | All |

### 10.2 Key Innovation

**Single HW Breakpoint Sharing:**
- Enables unlimited SW breakpoints with only 1 HW BP
- Works across all target/debugger combinations
- Predictive algorithm minimizes overhead (60% reduction)
- Critical for RISC-V32 with limited triggers

### 10.3 Code Reuse

| Component | Lines | Reused By |
|-----------|-------|-----------|
| Shared framework | ~1000 | All combinations |
| Per-target impl | ~200 | All debuggers for that target |
| Per-debugger impl | ~500 | All targets for that debugger |

**Total new code per combination:** ~200-500 lines (after framework)

# 32-bit Architecture Support Implementation

**Status**: In Progress  
**Target Completion**: Q1 2026  
**Current Phase**: LLVM IR Generation

## Overview

This document tracks the implementation of 32-bit architecture support via the LLVM backend. Cranelift does NOT support 32-bit, so LLVM is the only path for i686, ARMv7, and RISC-V 32.

## Supported 32-bit Targets

### i686 (x86 32-bit)
- **Target Triple**: `i686-unknown-linux-gnu`
- **Windows**: `i686-pc-windows-msvc`
- **Use Cases**: Legacy x86 systems, embedded x86
- **Baseline ISA**: i686 (Pentium Pro+)
- **SIMD**: SSE2 optional
- **Status**: Target triple mapping ✅

### ARMv7 (ARM 32-bit)
- **Target Triple**: `armv7-unknown-linux-gnueabihf`
- **Hard Float**: Yes (gnueabihf)
- **Use Cases**: Raspberry Pi 2/3, older Android, embedded ARM
- **Baseline ISA**: ARMv7-A
- **SIMD**: NEON (optional but common)
- **Status**: Target triple mapping ✅

### RISC-V 32 (RV32)
- **Target Triple**: `riscv32-unknown-linux-gnu`
- **Bare Metal**: `riscv32-unknown-none-elf`
- **Use Cases**: Embedded RISC-V, IoT devices
- **Baseline ISA**: RV32I or RV32G
- **Extensions**: M (multiply), A (atomic), C (compressed)
- **Status**: Target triple mapping ✅

## Implementation Checklist

### Phase 1: Target Infrastructure ✅ COMPLETE
- [x] TargetArch enum includes 32-bit variants
- [x] pointer_size() returns Bits32 for 32-bit targets
- [x] Backend selection auto-chooses LLVM for 32-bit
- [x] Target triple mapping for all 32-bit targets

### Phase 2: LLVM Integration ✅ COMPLETE
- [x] inkwell dependency with llvm18-0
- [x] Feature flag for optional LLVM
- [x] LlvmBackend structure with Context
- [x] get_target_triple() for all targets

### Phase 3: Type System 🚧 IN PROGRESS
- [x] Basic type mapping (i32, i64, f32, f64, bool)
- [x] Pointer width detection (32-bit vs 64-bit)
- [ ] Pointer types for 32-bit
- [ ] Struct layout for 32-bit alignment
- [ ] Array types with 32-bit indexing

### Phase 4: IR Generation 🚧 IN PROGRESS
- [x] Module creation
- [x] Function signature generation (stub)
- [ ] Basic blocks
- [ ] Binary operations (add, sub, mul, div)
- [ ] Load/Store with 32-bit addresses
- [ ] Function calls
- [ ] Return statements

### Phase 5: Object Emission ⏳ PENDING
- [ ] ELF object generation (Linux)
- [ ] PE/COFF object generation (Windows)
- [ ] 32-bit relocations
- [ ] Symbol table
- [ ] Debug info (DWARF32)

### Phase 6: Runtime Integration ⏳ PENDING
- [ ] 32-bit runtime value representation
- [ ] GC for 32-bit pointers
- [ ] FFI calling conventions (cdecl, stdcall)
- [ ] Stack alignment (4-byte on 32-bit)

### Phase 7: Testing ⏳ PENDING
- [ ] Cross-compilation tests
- [ ] QEMU-based runtime tests
- [ ] Real hardware testing (RPi 2/3)
- [ ] Integration tests

## 32-bit Specific Considerations

### Memory Layout
- **Pointer Size**: 4 bytes (not 8)
- **Alignment**: 4-byte natural alignment
- **Address Space**: 2^32 = 4GB max
- **Stack Growth**: Downward (like 64-bit)

### Calling Conventions

**i686**:
- **cdecl**: Arguments on stack (caller cleans)
- **stdcall**: Arguments on stack (callee cleans)
- **fastcall**: First 2 args in ECX/EDX
- **Return**: EAX (32-bit), EDX:EAX (64-bit)

**ARMv7**:
- **AAPCS**: r0-r3 for first 4 args
- **Hard Float**: s0-s15 / d0-d7 for FP args
- **Return**: r0 (32-bit), r0:r1 (64-bit)
- **Stack**: 8-byte aligned

**RISC-V 32**:
- **Standard**: a0-a7 for first 8 args
- **Float**: fa0-fa7 for FP args
- **Return**: a0 (32-bit), a0:a1 (64-bit)
- **Stack**: 16-byte aligned (even on RV32)

### Performance Impact

32-bit vs 64-bit performance characteristics:

| Aspect | 32-bit | 64-bit | Impact |
|--------|--------|--------|--------|
| Pointer size | 4 bytes | 8 bytes | 50% memory savings for pointer-heavy |
| Address space | 4 GB | 16 EB | Limits large datasets |
| Integer ops | Same | Same | No difference for i32/u32 |
| 64-bit int ops | Slower | Native | 2-4x slower on 32-bit |
| Cache usage | Better | Worse | Smaller pointers = more cache hits |
| Register pressure | Higher | Lower | Fewer 64-bit registers |

### Testing Strategy

**Cross-Compilation** (no hardware needed):
```bash
# Build for i686
cargo build --features llvm --target i686-unknown-linux-gnu

# Build for ARMv7
cargo build --features llvm --target armv7-unknown-linux-gnueabihf

# Build for RISC-V 32
cargo build --features llvm --target riscv32-unknown-linux-gnu
```

**QEMU Testing**:
```bash
# Install QEMU user-mode emulation
sudo apt-get install qemu-user-static

# Run i686 binary
qemu-i386-static ./target/i686-unknown-linux-gnu/debug/simple

# Run ARMv7 binary
qemu-arm-static ./target/armv7-unknown-linux-gnueabihf/debug/simple

# Run RISC-V 32 binary
qemu-riscv32-static ./target/riscv32-unknown-linux-gnu/debug/simple
```

**Real Hardware Testing**:
- **i686**: Old laptop or VM
- **ARMv7**: Raspberry Pi 2/3, BeagleBone
- **RISC-V 32**: SiFive HiFive1, Kendryte K210

## Current Test Results

### Without LLVM Feature (default)
```
cargo test -p simple-compiler --lib
✅ 3 tests pass (feature check, selection logic, target support)
```

### With LLVM Feature (development)
```
cargo test -p simple-compiler --lib --features llvm
🚧 Target triple tests pass
🚧 Module creation tests pass
🚧 IR generation tests in progress
```

## Milestones

### M1: Cross-Compilation ✅ COMPLETE
- Date: 2025-12-13
- Can build compiler targeting 32-bit
- No runtime tests yet

### M2: Basic IR Generation 🚧 IN PROGRESS
- Target: 2025-12-20
- Generate LLVM IR for simple functions
- Arithmetic operations
- Basic control flow

### M3: Object Emission ⏳ PLANNED
- Target: 2026-01-10
- Emit ELF/PE objects
- Link with runtime
- Hello world works

### M4: Runtime Integration ⏳ PLANNED
- Target: 2026-01-31
- 32-bit GC working
- FFI calls working
- Basic stdlib working

### M5: Full Test Suite ⏳ PLANNED
- Target: 2026-02-28
- All compiler tests pass
- QEMU runtime tests
- Real hardware validation

## Known Issues

1. **LLVM Toolchain**: Not everyone has LLVM 18 installed
   - Solution: Feature flag makes it optional
   
2. **Cross-Compilation Dependencies**: Need 32-bit system libraries
   - Solution: Document required packages
   
3. **Testing Infrastructure**: Need QEMU or real hardware
   - Solution: CI with QEMU, optional real hardware

4. **ABI Compatibility**: 32-bit calling conventions complex
   - Solution: Use LLVM's built-in ABI handling

## Resources

- **LLVM Target Triples**: https://llvm.org/docs/LangRef.html#target-triple
- **i686 ABI**: https://uclibc.org/docs/psABI-i386.pdf
- **ARM ABI**: https://developer.arm.com/documentation/ihi0042/latest
- **RISC-V ABI**: https://github.com/riscv-non-isa/riscv-elf-psabi-doc
- **Inkwell Examples**: https://github.com/TheDan64/inkwell/tree/master/examples

## See Also

- `doc/architecture/support.md` - Complete architecture matrix
- `doc/llvm_backend.md` - LLVM backend user guide
- `src/common/src/target.rs` - Target abstraction
- `src/compiler/src/codegen/llvm.rs` - LLVM backend implementation

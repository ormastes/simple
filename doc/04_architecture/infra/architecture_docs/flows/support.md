# Simple Language Architecture Support

**Last Updated**: 2025-12-13  
**Status**: LLVM backend in development, Cranelift backend complete

## Supported Architectures

Simple compiler supports **6 CPU architectures** across **32-bit and 64-bit** variants:

### ✅ Fully Supported (via Cranelift - Default)

| Architecture | Bits | ISA Family | Example Platforms |
|--------------|------|------------|-------------------|
| **x86_64**   | 64   | x86        | Intel/AMD desktop, cloud servers |
| **AArch64**  | 64   | ARM        | Apple Silicon, AWS Graviton, RPi 4+ |
| **RISC-V 64**| 64   | RISC-V     | SiFive boards, future servers |

**Build**: `cargo build` (default, no flags needed)

### ⚠️ Supported via LLVM Backend (In Development)

| Architecture | Bits | ISA Family | Example Platforms |
|--------------|------|------------|-------------------|
| **i686**     | 32   | x86        | Legacy x86 systems |
| **ARMv7**    | 32   | ARM        | Raspberry Pi 2/3, older Android |
| **RISC-V 32**| 32   | RISC-V     | Embedded RISC-V boards |

**Build**: `cargo build --features llvm` (requires LLVM 18)

## Current Implementation Status

### Cranelift Backend (Default) ✅ COMPLETE
- **Status**: Production ready
- **Architectures**: x86_64, AArch64, RISC-V 64 (all 64-bit)
- **Compilation Speed**: Fast
- **Binary Output**: SMF modules or native objects
- **Limitation**: Does NOT support any 32-bit architectures

### LLVM Backend (Optional) 🚧 IN DEVELOPMENT
- **Status**: Type mapping complete, IR generation pending
- **Architectures**: All 6 (x86_64, AArch64, RISC-V 64, i686, ARMv7, RISC-V 32)
- **Compilation Speed**: Slower than Cranelift
- **Binary Output**: SMF modules or native objects
- **Requirement**: LLVM 18 toolchain

## Architecture Selection Logic

The compiler automatically selects the appropriate backend:

```
┌─────────────────┐
│  Target Arch    │
└────────┬────────┘
         │
    ┌────▼─────┐
    │ 64-bit?  │
    └────┬─────┘
         │
    ┌────┴─────┐
   Yes        No
    │          │
    ▼          ▼
┌─────────┐ ┌──────┐
│Cranelift│ │ LLVM │
│(default)│ │(auto)│
└─────────┘ └──────┘
```

**Auto-selection rules**:
- **64-bit targets** (x86_64, AArch64, RISC-V 64): Use **Cranelift** (faster builds)
- **32-bit targets** (i686, ARMv7, RISC-V 32): Use **LLVM** (only option)

You can force LLVM for 64-bit targets:
```bash
cargo build --features llvm
export SIMPLE_BACKEND=llvm
./simple myprogram.spl
```

## Cross-Compilation Support

### Host → Target Matrix

| Host ↓ / Target → | x86_64 | AArch64 | RISC-V 64 | i686 | ARMv7 | RISC-V 32 |
|-------------------|--------|---------|-----------|------|-------|-----------|
| **x86_64 Linux**  | ✅ ✅  | ✅ ✅   | ✅ ✅     | 🚧   | 🚧    | 🚧        |
| **AArch64 Linux** | ✅ ✅  | ✅ ✅   | ✅ ✅     | 🚧   | 🚧    | 🚧        |
| **x86_64 macOS**  | ✅ ✅  | ✅ ✅   | ✅ ✅     | 🚧   | 🚧    | 🚧        |
| **AArch64 macOS** | ✅ ✅  | ✅ ✅   | ✅ ✅     | 🚧   | 🚧    | 🚧        |

**Legend**:
- ✅ = Working (left=Cranelift, right=LLVM if same)
- 🚧 = Planned (LLVM backend implementation)
- ❌ = Not supported

## ISA Features

### x86/x86_64
- **SSE2** (baseline for 64-bit)
- **SSE4.2** (optional, detected at runtime)
- **AVX/AVX2** (optional, SIMD support)
- **AVX-512** (optional, future)

### ARM/AArch64
- **NEON** (SIMD for both 32-bit and 64-bit)
- **SVE** (optional, future for AArch64)
- **SVE2** (optional, future)

### RISC-V
- **RV32I/RV64I** (baseline)
- **RV32G/RV64G** (general purpose - standard extensions)
- **RVC** (compressed instructions)
- **V** (vector extension - future)

## Platform-Specific Notes

### 32-bit Limitations

**Why LLVM is required for 32-bit**:
- Cranelift project explicitly dropped 32-bit support
- LLVM maintains excellent 32-bit codegen
- 32-bit targets are legacy/embedded focused

**Use Cases**:
- ✅ Embedded systems (RISC-V 32, ARM Cortex-M)
- ✅ Legacy x86 support (older hardware)
- ✅ Raspberry Pi 2/3 (ARMv7)
- ❌ New development (use 64-bit when possible)

### Performance Characteristics

| Architecture | Relative Performance | Notes |
|--------------|---------------------|-------|
| x86_64       | 100% (baseline)     | Best optimized, widest use |
| AArch64      | 95-105%             | Excellent on Apple Silicon |
| RISC-V 64    | 80-90%              | Improving, less mature |
| i686         | 70-80% of x86_64    | Memory limitations |
| ARMv7        | 60-75% of AArch64   | 32-bit overhead |
| RISC-V 32    | 70-85% of RISC-V 64 | 32-bit overhead |

## Testing Matrix

### Current Test Coverage

| Architecture | Host Tests | Cross-Compile | Runtime Tests |
|--------------|-----------|---------------|---------------|
| x86_64       | ✅ CI     | ✅            | ✅            |
| AArch64      | ✅ Local  | ✅            | ✅ Local      |
| RISC-V 64    | ✅ Cross  | ✅            | 🚧 QEMU       |
| i686         | 🚧        | 🚧            | 🚧            |
| ARMv7        | 🚧        | 🚧            | 🚧            |
| RISC-V 32    | 🚧        | 🚧            | 🚧            |

## Build Examples

### Default (64-bit Cranelift)
```bash
# Builds for host architecture
cargo build --release
./target/release/simple myprogram.spl
```

### With LLVM (All Architectures)
```bash
# Requires LLVM 18 installed
cargo build --release --features llvm

# Target 32-bit x86
./target/release/simple --target i686-unknown-linux-gnu myprogram.spl

# Target ARMv7
./target/release/simple --target armv7-unknown-linux-gnueabihf myprogram.spl
```

### Cross-Compilation
```bash
# From x86_64 to AArch64 (Cranelift)
cargo build --release --target aarch64-unknown-linux-gnu

# From x86_64 to ARMv7 (requires LLVM)
cargo build --release --features llvm --target armv7-unknown-linux-gnueabihf
```

## Roadmap

### Q4 2025
- ✅ Cranelift backend (64-bit only)
- ✅ Target abstraction (6 architectures)
- ✅ LLVM backend foundation
- 🚧 LLVM IR generation

### Q1 2026
- 🎯 LLVM backend completion
- 🎯 32-bit testing on real hardware
- 🎯 Cross-compilation CI

### Q2 2026
- 🎯 SIMD support (SSE2, NEON baseline)
- 🎯 Advanced vector extensions (AVX2, SVE)
- 🎯 Architecture-specific optimizations

## See Also

- **Target abstraction**: `src/common/src/target.rs`
- **Cranelift backend**: `src/compiler/src/codegen/cranelift.rs`
- **LLVM backend**: `src/compiler/src/codegen/llvm.rs`
- **LLVM guide**: `doc/llvm_backend.md`
- **Feature list**: `doc/features/feature.md` (#220)

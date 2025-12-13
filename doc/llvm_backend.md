# LLVM Backend

The Simple compiler supports an optional LLVM backend that provides 32-bit architecture support and broader platform coverage.

## Features

- **32-bit Architecture Support**: i686, ARMv7, RISC-V 32
- **64-bit Alternative**: Can be used instead of Cranelift for x86_64, AArch64, RISC-V 64
- **Shared Infrastructure**: Uses same MIR and runtime FFI as Cranelift backend

## Default Behavior

By default, Simple uses:
- **Cranelift** for 64-bit targets (fast compilation)
- **LLVM** auto-selected for 32-bit targets (when enabled)

## Building with LLVM Support

### Prerequisites

LLVM 18 development libraries must be installed:

**Ubuntu/Debian:**
```bash
wget https://apt.llvm.org/llvm.sh
chmod +x llvm.sh
sudo ./llvm.sh 18
export LLVM_SYS_180_PREFIX=/usr/lib/llvm-18
```

**macOS (Homebrew):**
```bash
brew install llvm@18
export LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18
```

**Windows:**
Download and install from https://releases.llvm.org/download.html

### Build Commands

```bash
# Enable LLVM backend
cargo build --features llvm

# Run tests with LLVM
cargo test --features llvm

# Build without LLVM (Cranelift only)
cargo build
```

## Usage

The backend is automatically selected based on target architecture:

```rust
use simple_compiler::codegen::{BackendKind, NativeBackend};
use simple_common::target::{Target, TargetArch, TargetOS};

// Automatically selects LLVM for 32-bit
let target = Target::new(TargetArch::X86, TargetOS::Linux);
let backend_kind = BackendKind::for_target(&target);
// Returns BackendKind::Llvm

// Automatically selects Cranelift for 64-bit
let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
let backend_kind = BackendKind::for_target(&target);
// Returns BackendKind::Cranelift

// Force LLVM for testing
let backend_kind = BackendKind::force_llvm();
```

## Architecture Support

| Architecture | Bits | Cranelift | LLVM |
|--------------|------|-----------|------|
| x86_64       | 64   | ✅        | ✅   |
| AArch64      | 64   | ✅        | ✅   |
| RISC-V 64    | 64   | ✅        | ✅   |
| i686         | 32   | ❌        | ✅   |
| ARMv7        | 32   | ❌        | ✅   |
| RISC-V 32    | 32   | ❌        | ✅   |

## Implementation Status

**Current**: Type mapping and backend trait implementation complete

**Phases**:
1. ✅ Dependencies and scaffolding
2. ✅ Type system (basic types)
3. ✅ Backend trait interface
4. ⏳ Function compilation (LLVM IR generation)
5. ⏳ Object emission
6. ⏳ Pipeline integration

See `doc/status/llvm_backend.md` for detailed progress.

## Design Principles

1. **Feature-Gated**: LLVM is optional to avoid forcing LLVM dependency
2. **Shared MIR**: Both backends consume the same MIR representation
3. **Consistent Runtime**: Same runtime FFI specs across backends
4. **Auto-Selection**: Transparent backend choice based on target
5. **Fast Default**: Cranelift remains default for faster builds

## Limitations

- LLVM backend currently in development (stub implementation)
- Requires LLVM 18 toolchain
- Slower compilation than Cranelift
- Not all MIR instructions implemented yet

## Future Work

- JIT support via LLVM ORC
- SIMD intrinsic coverage
- Advanced optimizations (LTO, PGO)
- Target-specific tuning

## See Also

- `doc/plans/23_llvm_backend_support.md` - Implementation plan
- `doc/feature.md` - Feature #220 breakdown
- `src/compiler/src/codegen/backend_trait.rs` - Backend abstraction

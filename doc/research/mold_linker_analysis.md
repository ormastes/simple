# Mold Linker Analysis for Simple Language Compiler

**Date:** 2025-12-18
**Status:** Analysis Complete
**Purpose:** Evaluate mold linker integration for Simple language compilation pipeline

---

## Executive Summary

[mold](https://github.com/rui314/mold) is a modern, high-performance linker by Rui Ueyama that can replace traditional Unix linkers (GNU ld, LLVM lld) with significant speed improvements. This analysis evaluates its applicability to the Simple language compiler beyond final executable generation.

**Key Findings:**
- ✅ **Recommended for:** Final executable generation (2-4x faster than lld)
- ✅ **Suitable for:** Development builds with rapid iteration
- ✅ **RISC-V 32-bit:** Full support for RV32LE/BE since v1.5.0 (Aug 2022) - suitable for embedded/IoT targets
- ⚠️ **Limited for:** Symbol analysis and introspection (basic capabilities only)
- ❌ **Not suitable for:** SMF binary format (mold produces ELF/Mach-O/PE)

---

## 1. Overview

### What is mold?

mold (Modern Linker) is a drop-in replacement for existing Unix linkers designed for speed. Written in C++20 by Rui Ueyama (creator of LLVM lld), it achieves 2-4x performance improvements over lld and 10-50x over GNU ld.

**Repository:** https://github.com/rui314/mold
**Latest Release:** v2.37.0 (March 2025)
**Language:** C++20
**License:** MIT + AGPL v3 (dual license)

### Performance Comparison

On a 16-core system (from mold README):

| Project | mold | lld | Speedup |
|---------|------|-----|---------|
| MySQL 8.3 | 0.46s | 1.64s | **3.6x** |
| Clang 19 | 1.35s | 5.20s | **3.9x** |
| Chromium 124 | 1.52s | 6.10s | **4.0x** |

> "mold is so fast that it is only 2x slower than `cp` command."

---

## 2. Architecture & Design

### Core Design Principles

1. **Parallelization First**
   - Data parallelism across all CPU cores
   - Parallel for-loops over homogeneous datasets (e.g., relocation tables)
   - Map-reduce patterns (e.g., SHA-1 hashing for build-id)

2. **String Interning**
   - Speculative symbol resolution during preloading
   - Hash table for symbol string deduplication
   - Symbol matching happens in parallel with file loading

3. **Memory Efficiency**
   - Intel TBB (Threading Building Blocks) for concurrent containers
   - `concurrent_hash_map` for symbol resolution
   - Alternative allocators: jemalloc, mimalloc (more scalable than tbbmalloc)

4. **Atomic Synchronization**
   - Minimal locking, prefers atomic variables
   - Shared data uses atomic flags on symbols
   - Avoids high-level synchronization primitives

### Supported Platforms

**Architectures:** x86-64, i386, ARM64, ARM32, RISC-V (RV32/RV64 LE/BE), PowerPC (32/64), s390x, LoongArch (32/64), SPARC64, m68k, SH-4

**RISC-V Support:**
- **RV64LE** (RISC-V 64-bit little-endian): Added in v1.1 (May 2022), full support for linking large programs
- **RV32LE** (RISC-V 32-bit little-endian): Added in v1.5.0 (Aug 2022)
- **RV64BE/RV32BE** (big-endian variants): Added in v1.5.0 (experimental, rare in practice)

**Binary Formats:** ELF (Linux), Mach-O (macOS), PE/COFF (Windows - experimental)

**Toolchains:** GCC 10.2+, Clang 16.0.0+, Rust (via cargo config)

---

## 3. Symbol Analysis Capabilities

### Map File Generation

**Flag:** `-M` / `--print-map` or `--Map=file`

Generates a linker map showing:
- Memory layout (sections, segments)
- Symbol addresses and sizes
- Input file contributions
- Section-to-segment mappings

**Format:** Traditional linker map format (similar to GNU ld)

**Use Case for Simple:**
```bash
# Generate map during native executable compilation
mold -o simple --Map=simple.map obj1.o obj2.o ...
```

### Symbol Tracing

**Flag:** `-y symbol` / `--trace-symbol=symbol`

Tracks references to a specific symbol throughout the linking process:
- Where symbol is defined (which object file)
- Where symbol is referenced (all usage sites)
- Symbol resolution order

**Use Case for Simple:**
```bash
# Trace how 'main' symbol is resolved
mold -y main -o simple *.o
```

### Cross-Reference Table

**Flag:** `--cref`

Generates cross-reference table showing:
- All global symbols in the project
- File where each symbol is defined
- All locations where symbol is used

**Format:** Alternative to GNU ld's cross-reference format (optimized for speed)

**Use Case for Simple:**
```bash
# Generate cross-reference for symbol analysis
mold --cref --Map=simple.map -o simple *.o
```

### Dependency Analysis

**Flag:** `--print-dependencies`

Shows dependency graph:
- Which file depends on which file
- Why specific objects were linked
- Symbol-level dependency tracking

**Output Format:**
```
file1.o: uses symbol 'foo' from file2.o
file2.o: uses symbol 'bar' from libstd.a(bar.o)
```

**Use Case for Simple:**
```bash
# Debug why certain modules are linked
mold --print-dependencies -o simple *.o
```

### Relocation Preservation

**Flag:** `--emit-relocs`

Keeps relocation sections in output:
- Enables post-link analysis tools (e.g., LLVM Bolt)
- Allows binary optimization passes
- Useful for JIT compilation infrastructure

**Use Case for Simple:** Could enable future JIT optimizations

---

## 4. Integration with Simple Compiler

### Current Simple Compilation Pipeline

```
Source (.spl) → AST → HIR → MIR → Codegen (Cranelift/LLVM) → SMF Binary
                                           ↓
                                    Native (Optional)
```

### Where mold Fits

#### Scenario 1: Native Executable Generation (Primary Use Case)

**Pipeline:**
```
MIR → LLVM Codegen → LLVM IR → Object Files (.o) → mold → Native ELF
```

**Benefits:**
- **4x faster** linking for large projects
- **Faster debug builds** during development
- **Reduced CI/CD times** for integration tests

**Integration Points:**
1. LLVM backend object emission (src/compiler/src/codegen/llvm/)
2. Native executable generation (optional output)
3. System test binaries (tests/system/)

**Implementation:**
```rust
// In src/compiler/src/codegen/llvm/backend.rs
pub fn link_with_mold(object_files: &[PathBuf], output: &Path) -> Result<()> {
    let mut cmd = Command::new("mold");
    cmd.arg("-o").arg(output);
    for obj in object_files {
        cmd.arg(obj);
    }
    cmd.status()?.success().then_some(()).ok_or(...)
}
```

#### Scenario 2: SMF Binary Format (NOT APPLICABLE)

**Status:** ❌ Incompatible

**Reason:**
- mold produces ELF/Mach-O/PE binaries
- SMF is Simple's custom binary format
- Different linking semantics (JIT-friendly, module-based)

**Alternative:** Keep existing SMF linker (src/compiler/src/linker/)

#### Scenario 3: Symbol Analysis for Compiler Diagnostics (LIMITED)

**Use Cases:**
1. **Undefined Symbol Errors**
   ```bash
   # Trace why symbol is undefined
   mold -y missing_function *.o 2>&1 | grep "undefined"
   ```

2. **Symbol Conflicts**
   ```bash
   # Find duplicate definitions
   mold --cref --Map=analysis.map *.o | grep "defined multiple times"
   ```

3. **Dead Code Detection**
   ```bash
   # Print unused symbols (requires --gc-sections)
   mold --gc-sections --print-gc-sections *.o
   ```

**Limitations:**
- Only works at link time (not during HIR/MIR passes)
- Requires object file generation first
- Limited to exported symbols (no internal analysis)

#### Scenario 4: Build System Integration

**Cargo Integration** (for Rust driver):
```toml
# .cargo/config.toml
[target.x86_64-unknown-linux-gnu]
linker = "clang"
rustflags = ["-C", "link-arg=-fuse-ld=mold"]
```

**Makefile Integration**:
```makefile
# Makefile
LINKER ?= mold

native_build:
	$(LINKER) -o simple build/*.o
```

#### Scenario 5: Cross-Compilation to RISC-V 32-bit

**Status:** ✅ Supported (RV32LE/BE since v1.5.0)

**Use Case:** Compile Simple programs for RISC-V 32-bit embedded systems or bare-metal targets

**Pipeline:**
```
Simple (.spl) → LLVM Codegen → RISC-V Object Files → mold → RV32 ELF Binary
```

**Toolchain Setup:**
```bash
# Install RISC-V 32-bit cross-compiler
sudo apt install gcc-riscv32-unknown-elf

# Configure Simple to use mold for RISC-V target
export SIMPLE_LINKER=mold
export SIMPLE_TARGET=riscv32-unknown-elf
```

**Integration Code:**
```rust
// In src/compiler/src/codegen/llvm/backend.rs
pub fn link_for_target(
    object_files: &[PathBuf],
    output: &Path,
    target: &str,
) -> Result<()> {
    let mut cmd = Command::new("mold");
    cmd.arg("-o").arg(output);

    // Add target-specific flags for RISC-V 32-bit
    if target.starts_with("riscv32") {
        cmd.arg("-m").arg("elf32lriscv"); // 32-bit little-endian RISC-V
        cmd.arg("--sysroot=/usr/riscv32-unknown-elf");
    }

    for obj in object_files {
        cmd.arg(obj);
    }

    cmd.status()?.success().then_some(()).ok_or(...)
}
```

**Benefits for Simple:**
- **Embedded Systems**: Link Simple programs for RV32 microcontrollers (e.g., SiFive FE310, ESP32-C3)
- **Bare-Metal**: Generate standalone binaries for RISC-V hardware without OS
- **Fast Linking**: Same 4x speedup applies to cross-compilation builds
- **IoT/Edge Devices**: Target 32-bit RISC-V processors common in IoT applications

**Target Platforms:**
- **RV32I**: Base 32-bit integer instruction set (minimal embedded systems)
- **RV32IM**: With multiplication/division (general-purpose microcontrollers)
- **RV32IMAC**: With atomics and compressed instructions (common IoT chips)
- **RV32GC**: Full general-purpose ISA (Linux-capable embedded systems)

**Limitations:**
- Only for native binary output (not SMF format)
- Requires RISC-V cross-toolchain installed
- Big-endian RV32BE support is experimental (rarely used in practice)

**Note:** As of mold v1.5.0 (August 2022), RV32 support has been stable for 3+ years with ongoing improvements for RISC-V-specific features like linker relaxation and `.riscv.attributes` handling.

---

## 5. Comparative Analysis

### mold vs. GNU ld

| Feature | mold | GNU ld | Winner |
|---------|------|--------|--------|
| Speed | 0.46s (MySQL) | 10.4s | **mold (23x)** |
| Parallelization | Fully parallel | Limited | **mold** |
| Map files | ✅ Yes | ✅ Yes | Tie |
| Cross-reference | ✅ Alt format | ✅ Traditional | Tie |
| Linker scripts | ⚠️ Limited | ✅ Full | **GNU ld** |
| Symbol versioning | ✅ Yes | ✅ Yes | Tie |
| LTO | ✅ Yes | ✅ Yes | Tie |

### mold vs. LLVM lld

| Feature | mold | lld | Winner |
|---------|------|-----|--------|
| Speed | 1.35s (Clang) | 5.20s | **mold (3.9x)** |
| LLVM integration | ❌ External | ✅ Built-in | **lld** |
| ELF support | ✅ Excellent | ✅ Excellent | Tie |
| Mach-O support | ✅ Experimental | ✅ Mature | **lld** |
| PE/COFF support | ⚠️ Experimental | ✅ Stable | **lld** |

### mold vs. Simple SMF Loader

| Feature | mold | SMF Loader | Winner |
|---------|------|------------|--------|
| Format | ELF/Mach-O/PE | Custom SMF | Different domains |
| JIT-friendly | ❌ | ✅ | **SMF** |
| Module loading | ❌ | ✅ | **SMF** |
| Symbol resolution | Link-time | Runtime | Different phases |
| Speed | 0.5-2s | <0.01s | **SMF** (different scale) |

---

## 6. Recommendations for Simple

### ✅ Recommended Use Cases

1. **Native Executable Generation (Development Builds)**
   - Use mold for rapid debug-edit-rebuild cycles
   - 4x faster linking improves developer experience
   - Integrate via `-fuse-ld=mold` in LLVM backend

2. **System Test Compilation**
   - Link system test binaries with mold
   - Faster CI/CD pipeline (currently 807 tests)
   - Reduce test suite execution time

3. **Cross-Platform Native Builds**
   - Use mold on Linux (best support)
   - Fall back to lld on macOS/Windows

### ⚠️ Limited Use Cases

1. **Compiler Diagnostics**
   - Use `--trace-symbol` for debugging link errors
   - Use `--print-dependencies` for module dependency analysis
   - **But:** Only works at link time, not during compilation

2. **Binary Analysis**
   - Use `--emit-relocs` for post-link optimization
   - Use `--Map` for memory layout analysis
   - **But:** Requires ELF/Mach-O output (not SMF)

### ❌ Not Recommended

1. **SMF Binary Generation**
   - mold cannot produce SMF format
   - Keep existing SMF linker (src/compiler/src/linker/)

2. **Runtime Symbol Tracking**
   - mold is a link-time tool
   - Use Simple's runtime for symbol resolution

3. **HIR/MIR Symbol Analysis**
   - mold operates on object files, not IR
   - Use Simple's compiler passes for IR analysis

---

## 7. Implementation Plan

### Phase 1: Optional Native Backend (1-2 days)

**Goal:** Add mold as optional linker for native executables

**Tasks:**
1. Detect mold availability (`which mold`)
2. Add `--linker=mold|lld|ld` CLI flag
3. Integrate in LLVM backend (src/compiler/src/codegen/llvm/)
4. Add fallback to lld if mold unavailable

**Files to Modify:**
- `src/driver/src/main.rs` (CLI flag)
- `src/compiler/src/codegen/llvm/backend.rs` (linker selection)
- `src/common/src/config_env.rs` (linker config)

**Code Sketch:**
```rust
// src/compiler/src/codegen/llvm/backend.rs
pub enum Linker {
    Mold,
    Lld,
    Ld,
}

impl Linker {
    pub fn detect() -> Self {
        if Command::new("mold").arg("--version").status().is_ok() {
            Linker::Mold
        } else if Command::new("ld.lld").arg("--version").status().is_ok() {
            Linker::Lld
        } else {
            Linker::Ld
        }
    }

    pub fn link(&self, objects: &[PathBuf], output: &Path) -> Result<()> {
        match self {
            Linker::Mold => {
                Command::new("mold")
                    .arg("-o").arg(output)
                    .args(objects)
                    .status()?
            }
            // ... other linkers
        }
    }
}
```

### Phase 2: Symbol Analysis Integration (2-3 days)

**Goal:** Use mold for symbol diagnostics

**Tasks:**
1. Implement `--analyze-symbols` flag
2. Generate map file with `--Map=analysis.map`
3. Parse map file for undefined symbols
4. Generate diagnostic reports

**Use Case:**
```bash
# Analyze undefined symbols in build
simple compile app.spl --native --analyze-symbols
```

**Output:**
```
Symbol Analysis Report
======================
Undefined Symbols:
  - missing_function (referenced in module1.o)
  - unknown_variable (referenced in module2.o)

Suggestions:
  - Add import for missing_function from stdlib
  - Check spelling of unknown_variable
```

### Phase 3: CI/CD Integration (1 day)

**Goal:** Speed up continuous integration

**Tasks:**
1. Add mold to CI docker images
2. Enable mold for system test builds
3. Benchmark build time improvements
4. Update documentation

**Expected Impact:**
- 4x faster system test linking
- ~2-3 minutes saved per CI run

---

## 8. Performance Projections for Simple

### Current Simple Build Times (Estimated)

| Stage | Time | Notes |
|-------|------|-------|
| Parse | 0.1s | 631 unit tests |
| Type Check | 0.2s | HM inference |
| HIR Lower | 0.1s | AST → HIR |
| MIR Lower | 0.2s | HIR → MIR |
| Codegen (Cranelift) | 0.5s | MIR → Native |
| **Linking (lld)** | **1.0s** | **Object → ELF** |
| **Total** | **2.1s** | |

### With mold Integration

| Stage | Time | Improvement | Notes |
|-------|------|-------------|-------|
| Parse | 0.1s | - | Same |
| Type Check | 0.2s | - | Same |
| HIR Lower | 0.1s | - | Same |
| MIR Lower | 0.2s | - | Same |
| Codegen (Cranelift) | 0.5s | - | Same |
| **Linking (mold)** | **0.25s** | **-75%** | **4x faster** |
| **Total** | **1.35s** | **-36%** | **~750ms saved** |

**Impact:** ~35% faster native builds

---

## 9. Alternatives Considered

### 1. GNU Gold

**Pros:**
- Faster than GNU ld
- Wide compatibility

**Cons:**
- Still slower than mold/lld
- Less actively maintained

**Verdict:** ❌ Skip (mold is better)

### 2. LLVM lld

**Pros:**
- Built into LLVM
- Mature and stable
- Good performance

**Cons:**
- 4x slower than mold
- Current bottleneck in builds

**Verdict:** ✅ Keep as fallback

### 3. Custom Linker for Simple

**Pros:**
- Full control over linking
- Could integrate with SMF

**Cons:**
- Significant development effort
- Reinventing wheel
- Maintenance burden

**Verdict:** ❌ Not worth it for native builds

### 4. Cranelift JIT (No Linking)

**Pros:**
- No linking needed
- Very fast iteration

**Cons:**
- Limited to JIT mode
- No persistent binaries

**Verdict:** ✅ Already implemented (keep)

---

## 10. Risks & Mitigations

### Risk 1: Platform Support

**Issue:** mold has experimental support for macOS/Windows

**Impact:** Users on non-Linux platforms may have issues

**Mitigation:**
1. Auto-detect platform and fall back to lld
2. Document mold as Linux-only optimization
3. Make mold optional (not required)

**Code:**
```rust
fn select_linker() -> Linker {
    if cfg!(target_os = "linux") && mold_available() {
        Linker::Mold
    } else {
        Linker::Lld
    }
}
```

### Risk 2: Linker Script Compatibility

**Issue:** mold has limited linker script support

**Impact:** Complex linker scripts may fail

**Mitigation:**
1. Use simple linker scripts only
2. Test with representative workloads
3. Fall back to GNU ld if mold fails

### Risk 3: Build Reproducibility

**Issue:** Different linkers may produce slightly different binaries

**Impact:** Build artifacts may differ between systems

**Mitigation:**
1. Document linker choice in build metadata
2. Use same linker in CI/CD
3. Add `--linker` flag for explicit control

### Risk 4: Debugging Experience

**Issue:** mold is optimized for speed, not debuggability

**Impact:** Debug builds may be harder to debug

**Mitigation:**
1. Use `-g` flag for debug symbols (works with mold)
2. Test debugging with gdb/lldb
3. Document any known issues

---

## 11. Conclusion

### Summary

**mold linker is HIGHLY RECOMMENDED for:**
- ✅ Native executable generation (4x faster)
- ✅ Development builds (faster iteration)
- ✅ CI/CD pipelines (reduced build times)

**mold linker is LIMITED for:**
- ⚠️ Symbol analysis (basic capabilities only)
- ⚠️ Compiler diagnostics (link-time only)

**mold linker is NOT SUITABLE for:**
- ❌ SMF binary format (incompatible)
- ❌ Runtime symbol tracking (link-time tool)
- ❌ HIR/MIR analysis (operates on object files)

### Recommended Action

**Implement Phase 1** (optional mold integration for native builds):
1. Add `--linker=mold` CLI flag
2. Auto-detect mold availability
3. Fall back to lld if unavailable
4. Measure build time improvements

**Expected Benefits:**
- 35% faster native builds
- Better developer experience
- Faster CI/CD pipelines

**Effort:** 1-2 days (low risk, high reward)

---

## 12. References

### Primary Sources

1. **mold GitHub Repository**
   https://github.com/rui314/mold
   Main repository with source code and documentation

2. **mold README**
   https://github.com/rui314/mold/blob/main/README.md
   Performance benchmarks and usage examples

3. **mold Design Document**
   https://github.com/rui314/mold/blob/main/docs/design.md
   Internal architecture and parallelization strategy

4. **mold Man Page**
   https://github.com/rui314/mold/blob/main/docs/mold.md
   Complete reference of all flags and options

### Secondary Sources

5. **Analysis and Introspection Options in Linkers**
   https://maskray.me/blog/2022-02-27-analysis-and-introspection-options-in-linkers
   Comparison of linker analysis capabilities

6. **mold v2.37.0 Release Notes**
   https://github.com/rui314/mold/releases/tag/v2.37.0
   Latest release with Intel APX support (March 2025)

### Related Tools

7. **LLVM lld Documentation**
   https://lld.llvm.org/
   Alternative linker (current fallback)

8. **GNU ld Documentation**
   https://sourceware.org/binutils/docs/ld/
   Traditional Unix linker (baseline)

---

## Appendix A: mold Flag Reference

### Symbol Analysis Flags

| Flag | Description | Output |
|------|-------------|--------|
| `-M` / `--print-map` | Print map file to stdout | Text to stdout |
| `--Map=file` | Write map file to file | Text file |
| `-y sym` / `--trace-symbol=sym` | Trace symbol references | Text to stderr |
| `--cref` | Generate cross-reference table | Text in map file |
| `--print-dependencies` | Print dependency graph | Text to stdout |
| `--emit-relocs` | Keep relocation sections | ELF sections |
| `--trace` | Print input file names | Text to stderr |
| `--stats` | Print input statistics | Text to stdout |

### Performance Flags

| Flag | Description | Impact |
|------|-------------|--------|
| `--threads=N` | Use N threads | Control parallelism |
| `--thread-count=N` | Alias for --threads | Same as above |
| `--no-threads` | Disable threading | Debug mode |
| `--stats` | Print performance stats | Shows timing |

### Compatibility Flags

| Flag | Description | Purpose |
|------|-------------|---------|
| `--gc-sections` | Remove unused sections | Reduce size |
| `--print-gc-sections` | Print removed sections | Debug GC |
| `--as-needed` | Link shared libs only if needed | Reduce deps |
| `--no-as-needed` | Always link shared libs | Force deps |

---

## Appendix B: Integration Code Example

### Complete Implementation (Proof of Concept)

```rust
// src/compiler/src/linker/mod.rs
pub mod native;

// src/compiler/src/linker/native.rs
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeLinker {
    Mold,
    Lld,
    Ld,
}

impl NativeLinker {
    /// Detect best available linker on the system
    pub fn detect() -> Self {
        if cfg!(target_os = "linux") {
            if Command::new("mold").arg("--version").status().is_ok() {
                return Self::Mold;
            }
        }

        if Command::new("ld.lld").arg("--version").status().is_ok() {
            Self::Lld
        } else {
            Self::Ld
        }
    }

    /// Get linker name for display
    pub fn name(&self) -> &str {
        match self {
            Self::Mold => "mold",
            Self::Lld => "lld",
            Self::Ld => "ld",
        }
    }

    /// Link object files into executable
    pub fn link(
        &self,
        objects: &[PathBuf],
        output: &Path,
        generate_map: bool,
    ) -> Result<(), String> {
        let mut cmd = match self {
            Self::Mold => {
                let mut c = Command::new("mold");
                c.arg("-o").arg(output);
                if generate_map {
                    c.arg("--Map").arg(output.with_extension("map"));
                }
                c
            }
            Self::Lld => {
                let mut c = Command::new("ld.lld");
                c.arg("-o").arg(output);
                if generate_map {
                    c.arg("--Map").arg(output.with_extension("map"));
                }
                c
            }
            Self::Ld => {
                let mut c = Command::new("ld");
                c.arg("-o").arg(output);
                if generate_map {
                    c.arg("-Map").arg(output.with_extension("map"));
                }
                c
            }
        };

        for obj in objects {
            cmd.arg(obj);
        }

        let status = cmd.status()
            .map_err(|e| format!("Failed to run {}: {}", self.name(), e))?;

        if !status.success() {
            return Err(format!("{} failed with exit code {}",
                self.name(),
                status.code().unwrap_or(-1)
            ));
        }

        Ok(())
    }

    /// Analyze symbols in object files
    pub fn analyze_symbols(
        &self,
        objects: &[PathBuf],
        trace_symbol: Option<&str>,
    ) -> Result<String, String> {
        let mut cmd = match self {
            Self::Mold => Command::new("mold"),
            Self::Lld => Command::new("ld.lld"),
            Self::Ld => Command::new("ld"),
        };

        cmd.arg("-o").arg("/dev/null"); // Don't create output
        cmd.arg("--print-map");

        if let Some(sym) = trace_symbol {
            cmd.arg("-y").arg(sym);
        }

        for obj in objects {
            cmd.arg(obj);
        }

        let output = cmd.output()
            .map_err(|e| format!("Failed to run {}: {}", self.name(), e))?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_linker() {
        let linker = NativeLinker::detect();
        println!("Detected linker: {}", linker.name());
        assert!(matches!(linker, NativeLinker::Mold | NativeLinker::Lld | NativeLinker::Ld));
    }
}
```

### CLI Integration

```rust
// src/driver/src/main.rs

// Add to help text:
eprintln!("  --linker <type>         Native linker: mold, lld, ld (auto-detect)");

// In compile_file function:
fn compile_file(
    source: &PathBuf,
    output: Option<PathBuf>,
    target: Option<Target>,
    snapshot: bool,
    linker: Option<&str>,
) -> i32 {
    // ... existing code ...

    let native_linker = match linker {
        Some("mold") => NativeLinker::Mold,
        Some("lld") => NativeLinker::Lld,
        Some("ld") => NativeLinker::Ld,
        _ => NativeLinker::detect(),
    };

    println!("Using linker: {}", native_linker.name());

    // ... link with native_linker ...
}
```

---

## Appendix C: Design Patterns for Resource Management

### Overview

When integrating mold linker into Simple's compilation pipeline, proper resource management is critical. This section documents design patterns for handling linker processes, temporary files, and system resources.

### Pattern 1: RAII Process Handle

**Purpose:** Ensure linker processes are properly terminated even on error paths.

```rust
/// RAII wrapper for linker process
pub struct LinkerProcess {
    child: Option<std::process::Child>,
    temp_files: Vec<PathBuf>,
}

impl LinkerProcess {
    pub fn spawn(linker: NativeLinker, args: &[&str]) -> Result<Self, LinkerError> {
        let child = Command::new(linker.executable())
            .args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(LinkerError::SpawnFailed)?;

        Ok(Self {
            child: Some(child),
            temp_files: Vec::new(),
        })
    }

    pub fn add_temp_file(&mut self, path: PathBuf) {
        self.temp_files.push(path);
    }

    pub fn wait(mut self) -> Result<LinkerOutput, LinkerError> {
        let child = self.child.take().expect("process already consumed");
        let output = child.wait_with_output()
            .map_err(LinkerError::WaitFailed)?;

        Ok(LinkerOutput {
            success: output.status.success(),
            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
            exit_code: output.status.code(),
        })
    }
}

impl Drop for LinkerProcess {
    fn drop(&mut self) {
        // Kill process if still running
        if let Some(mut child) = self.child.take() {
            let _ = child.kill();
            let _ = child.wait();
        }

        // Clean up temporary files
        for path in &self.temp_files {
            let _ = std::fs::remove_file(path);
        }
    }
}
```

### Pattern 2: Builder Pattern for Linker Configuration

**Purpose:** Provide a fluent API for configuring linker invocations with many optional parameters.

```rust
/// Builder for linker invocation
#[derive(Default)]
pub struct LinkerBuilder {
    linker: Option<NativeLinker>,
    objects: Vec<PathBuf>,
    output: Option<PathBuf>,
    libraries: Vec<String>,
    library_paths: Vec<PathBuf>,
    generate_map: bool,
    trace_symbols: Vec<String>,
    gc_sections: bool,
    emit_relocs: bool,
    threads: Option<usize>,
    sysroot: Option<PathBuf>,
    target: Option<String>,
}

impl LinkerBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn linker(mut self, linker: NativeLinker) -> Self {
        self.linker = Some(linker);
        self
    }

    pub fn object(mut self, path: impl Into<PathBuf>) -> Self {
        self.objects.push(path.into());
        self
    }

    pub fn objects(mut self, paths: impl IntoIterator<Item = PathBuf>) -> Self {
        self.objects.extend(paths);
        self
    }

    pub fn output(mut self, path: impl Into<PathBuf>) -> Self {
        self.output = Some(path.into());
        self
    }

    pub fn library(mut self, name: impl Into<String>) -> Self {
        self.libraries.push(name.into());
        self
    }

    pub fn library_path(mut self, path: impl Into<PathBuf>) -> Self {
        self.library_paths.push(path.into());
        self
    }

    pub fn generate_map(mut self, enable: bool) -> Self {
        self.generate_map = enable;
        self
    }

    pub fn trace_symbol(mut self, symbol: impl Into<String>) -> Self {
        self.trace_symbols.push(symbol.into());
        self
    }

    pub fn gc_sections(mut self, enable: bool) -> Self {
        self.gc_sections = enable;
        self
    }

    pub fn emit_relocs(mut self, enable: bool) -> Self {
        self.emit_relocs = enable;
        self
    }

    pub fn threads(mut self, count: usize) -> Self {
        self.threads = Some(count);
        self
    }

    pub fn sysroot(mut self, path: impl Into<PathBuf>) -> Self {
        self.sysroot = Some(path.into());
        self
    }

    pub fn target(mut self, target: impl Into<String>) -> Self {
        self.target = Some(target.into());
        self
    }

    pub fn build(self) -> Result<LinkerInvocation, LinkerError> {
        let linker = self.linker.unwrap_or_else(NativeLinker::detect);
        let output = self.output.ok_or(LinkerError::MissingOutput)?;

        if self.objects.is_empty() {
            return Err(LinkerError::NoInputFiles);
        }

        Ok(LinkerInvocation {
            linker,
            objects: self.objects,
            output,
            libraries: self.libraries,
            library_paths: self.library_paths,
            generate_map: self.generate_map,
            trace_symbols: self.trace_symbols,
            gc_sections: self.gc_sections,
            emit_relocs: self.emit_relocs,
            threads: self.threads,
            sysroot: self.sysroot,
            target: self.target,
        })
    }
}

// Usage example:
// let result = LinkerBuilder::new()
//     .linker(NativeLinker::Mold)
//     .objects(object_files)
//     .output("app")
//     .library("c")
//     .gc_sections(true)
//     .generate_map(true)
//     .build()?
//     .run()?;
```

### Pattern 3: Strategy Pattern for Linker Selection

**Purpose:** Allow runtime selection of linker implementation with consistent interface.

```rust
/// Trait for linker implementations
pub trait Linker: Send + Sync {
    fn name(&self) -> &str;
    fn executable(&self) -> &str;
    fn supports_feature(&self, feature: LinkerFeature) -> bool;
    fn build_args(&self, invocation: &LinkerInvocation) -> Vec<String>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkerFeature {
    MapFile,
    CrossReference,
    DependencyGraph,
    RelocationPreserve,
    GcSections,
    Lto,
    ThreadControl,
    SymbolVersioning,
}

pub struct MoldLinker;

impl Linker for MoldLinker {
    fn name(&self) -> &str { "mold" }
    fn executable(&self) -> &str { "mold" }

    fn supports_feature(&self, feature: LinkerFeature) -> bool {
        match feature {
            LinkerFeature::MapFile => true,
            LinkerFeature::CrossReference => true,
            LinkerFeature::DependencyGraph => true,
            LinkerFeature::RelocationPreserve => true,
            LinkerFeature::GcSections => true,
            LinkerFeature::Lto => true,
            LinkerFeature::ThreadControl => true,
            LinkerFeature::SymbolVersioning => true,
        }
    }

    fn build_args(&self, invocation: &LinkerInvocation) -> Vec<String> {
        let mut args = Vec::new();

        args.push("-o".to_string());
        args.push(invocation.output.display().to_string());

        if invocation.generate_map {
            args.push("--Map".to_string());
            args.push(invocation.output.with_extension("map").display().to_string());
        }

        for sym in &invocation.trace_symbols {
            args.push("-y".to_string());
            args.push(sym.clone());
        }

        if invocation.gc_sections {
            args.push("--gc-sections".to_string());
        }

        if invocation.emit_relocs {
            args.push("--emit-relocs".to_string());
        }

        if let Some(threads) = invocation.threads {
            args.push(format!("--threads={}", threads));
        }

        for path in &invocation.library_paths {
            args.push("-L".to_string());
            args.push(path.display().to_string());
        }

        for lib in &invocation.libraries {
            args.push("-l".to_string());
            args.push(lib.clone());
        }

        for obj in &invocation.objects {
            args.push(obj.display().to_string());
        }

        args
    }
}

pub struct LldLinker;
pub struct GnuLdLinker;

// Similar implementations for LldLinker and GnuLdLinker...

/// Factory for creating linkers
pub struct LinkerFactory;

impl LinkerFactory {
    pub fn create(kind: NativeLinker) -> Box<dyn Linker> {
        match kind {
            NativeLinker::Mold => Box::new(MoldLinker),
            NativeLinker::Lld => Box::new(LldLinker),
            NativeLinker::Ld => Box::new(GnuLdLinker),
        }
    }

    pub fn detect_best() -> Box<dyn Linker> {
        Self::create(NativeLinker::detect())
    }
}
```

### Pattern 4: Result Type with Rich Error Context

**Purpose:** Provide detailed error information for debugging linker failures.

```rust
/// Linker error with context
#[derive(Debug)]
pub enum LinkerError {
    SpawnFailed {
        linker: String,
        source: std::io::Error,
    },
    WaitFailed {
        linker: String,
        source: std::io::Error,
    },
    LinkFailed {
        linker: String,
        exit_code: Option<i32>,
        stderr: String,
        objects: Vec<PathBuf>,
    },
    MissingOutput,
    NoInputFiles,
    LinkerNotFound {
        linker: String,
    },
    UnsupportedFeature {
        linker: String,
        feature: LinkerFeature,
    },
    UnsupportedTarget {
        linker: String,
        target: String,
    },
}

impl std::fmt::Display for LinkerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SpawnFailed { linker, source } =>
                write!(f, "Failed to spawn {}: {}", linker, source),
            Self::WaitFailed { linker, source } =>
                write!(f, "Failed to wait for {}: {}", linker, source),
            Self::LinkFailed { linker, exit_code, stderr, objects } => {
                writeln!(f, "Linking failed with {}", linker)?;
                if let Some(code) = exit_code {
                    writeln!(f, "  Exit code: {}", code)?;
                }
                writeln!(f, "  Input files: {}", objects.len())?;
                if !stderr.is_empty() {
                    writeln!(f, "  Error output:\n{}", stderr)?;
                }
                Ok(())
            }
            Self::MissingOutput =>
                write!(f, "Output path not specified"),
            Self::NoInputFiles =>
                write!(f, "No input files provided"),
            Self::LinkerNotFound { linker } =>
                write!(f, "Linker '{}' not found in PATH", linker),
            Self::UnsupportedFeature { linker, feature } =>
                write!(f, "Linker '{}' does not support {:?}", linker, feature),
            Self::UnsupportedTarget { linker, target } =>
                write!(f, "Linker '{}' does not support target '{}'", linker, target),
        }
    }
}

impl std::error::Error for LinkerError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::SpawnFailed { source, .. } => Some(source),
            Self::WaitFailed { source, .. } => Some(source),
            _ => None,
        }
    }
}
```

### Pattern 5: Temporary File Guard

**Purpose:** Automatically clean up intermediate object files and artifacts.

```rust
/// Guard for temporary files that cleans up on drop
pub struct TempFileGuard {
    paths: Vec<PathBuf>,
    keep_on_error: bool,
}

impl TempFileGuard {
    pub fn new() -> Self {
        Self {
            paths: Vec::new(),
            keep_on_error: false,
        }
    }

    pub fn keep_on_error(mut self, keep: bool) -> Self {
        self.keep_on_error = keep;
        self
    }

    pub fn add(&mut self, path: impl Into<PathBuf>) -> &PathBuf {
        self.paths.push(path.into());
        self.paths.last().unwrap()
    }

    pub fn create_temp_object(&mut self, prefix: &str) -> std::io::Result<PathBuf> {
        let dir = std::env::temp_dir();
        let name = format!("{}-{}.o", prefix, std::process::id());
        let path = dir.join(name);
        self.paths.push(path.clone());
        Ok(path)
    }

    /// Take ownership of paths, preventing cleanup
    pub fn take(mut self) -> Vec<PathBuf> {
        std::mem::take(&mut self.paths)
    }

    /// Explicitly clean up all files
    pub fn cleanup(&mut self) {
        for path in self.paths.drain(..) {
            let _ = std::fs::remove_file(&path);
        }
    }
}

impl Drop for TempFileGuard {
    fn drop(&mut self) {
        if !self.keep_on_error || !std::thread::panicking() {
            self.cleanup();
        }
    }
}

// Usage:
// let mut temp = TempFileGuard::new().keep_on_error(true);
// let obj1 = temp.create_temp_object("module1")?;
// compile_to_object(source1, &obj1)?;
// let obj2 = temp.create_temp_object("module2")?;
// compile_to_object(source2, &obj2)?;
// link(&[obj1, obj2], output)?;
// temp.cleanup(); // Or let it drop
```

---

## Appendix D: Coding and Design Style Guidelines

### Overview

This section establishes coding conventions for integrating mold linker support into the Simple compiler codebase. These guidelines ensure consistency with existing code and maintainability.

### 1. Module Organization

**File Structure:**
```
src/compiler/src/linker/
├── mod.rs              # Public exports and LinkerKind enum
├── native.rs           # NativeLinker implementation
├── builder.rs          # LinkerBuilder fluent API
├── error.rs            # LinkerError types
├── process.rs          # LinkerProcess RAII wrapper
└── analysis.rs         # Symbol analysis utilities
```

**Module Visibility:**
```rust
// src/compiler/src/linker/mod.rs
mod builder;
mod error;
mod native;
mod process;
mod analysis;

// Public API
pub use builder::LinkerBuilder;
pub use error::LinkerError;
pub use native::{NativeLinker, LinkerOutput};

// Internal use only
pub(crate) use process::LinkerProcess;
pub(crate) use analysis::SymbolAnalyzer;
```

### 2. Naming Conventions

**Types:**
- Use descriptive names: `NativeLinker`, not `NL` or `Linker`
- Suffix error types with `Error`: `LinkerError`
- Suffix builder types with `Builder`: `LinkerBuilder`
- Use `Kind` suffix for enums: `LinkerKind`, `LinkerFeature`

**Functions:**
- Verbs for actions: `link()`, `spawn()`, `detect()`
- Nouns for getters: `name()`, `executable()`, `output()`
- `is_` prefix for boolean checks: `is_available()`, `is_supported()`
- `try_` prefix for fallible operations that return Option: `try_detect()`
- `with_` prefix for builder setters: `with_output()`, `with_threads()`

**Constants:**
- SCREAMING_SNAKE_CASE: `DEFAULT_THREAD_COUNT`, `MAX_RETRIES`

```rust
// Good
pub fn detect_linker() -> NativeLinker { ... }
pub fn is_mold_available() -> bool { ... }
pub fn link_objects(objects: &[PathBuf], output: &Path) -> Result<(), LinkerError> { ... }

// Avoid
pub fn det() -> NativeLinker { ... }  // Too abbreviated
pub fn check_mold() -> bool { ... }   // Not clear what "check" means
pub fn do_link(...) { ... }           // "do_" prefix is redundant
```

### 3. Error Handling Style

**Prefer `Result` over panics:**
```rust
// Good
pub fn link(&self, objects: &[PathBuf], output: &Path) -> Result<(), LinkerError> {
    if objects.is_empty() {
        return Err(LinkerError::NoInputFiles);
    }
    // ...
}

// Avoid panics in library code
pub fn link(&self, objects: &[PathBuf], output: &Path) {
    assert!(!objects.is_empty()); // Only for invariants, not validation
    // ...
}
```

**Use `?` operator with context:**
```rust
use anyhow::{Context, Result};

pub fn link_with_context(invocation: &LinkerInvocation) -> Result<()> {
    let output = Command::new(invocation.linker.executable())
        .args(&invocation.build_args())
        .output()
        .with_context(|| format!(
            "Failed to execute {} linker",
            invocation.linker.name()
        ))?;

    if !output.status.success() {
        anyhow::bail!(
            "Linking failed (exit code {}): {}",
            output.status.code().unwrap_or(-1),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    Ok(())
}
```

### 4. Documentation Style

**Module documentation:**
```rust
//! Native linker integration for Simple compiler.
//!
//! This module provides support for using mold, lld, or GNU ld
//! to produce native executables from compiled object files.
//!
//! # Examples
//!
//! ```rust
//! use simple_compiler::linker::{LinkerBuilder, NativeLinker};
//!
//! let result = LinkerBuilder::new()
//!     .linker(NativeLinker::Mold)
//!     .objects(vec!["main.o".into(), "lib.o".into()])
//!     .output("app")
//!     .build()?
//!     .run()?;
//! ```
//!
//! # Feature Flags
//!
//! - `mold`: Enable mold linker support (default on Linux)
//! - `lld`: Enable LLVM lld linker support
```

**Function documentation:**
```rust
/// Detect the best available linker on the system.
///
/// Linker preference order:
/// 1. mold (if on Linux and available)
/// 2. lld (LLVM linker)
/// 3. ld (GNU linker, fallback)
///
/// # Returns
///
/// The detected linker variant. Never returns an error; always
/// falls back to GNU ld if no other linker is found.
///
/// # Example
///
/// ```rust
/// let linker = NativeLinker::detect();
/// println!("Using linker: {}", linker.name());
/// ```
pub fn detect() -> Self {
    // ...
}
```

### 5. Testing Conventions

**Test organization:**
```rust
#[cfg(test)]
mod tests {
    use super::*;

    // Unit tests for individual functions
    mod detect {
        use super::*;

        #[test]
        fn returns_valid_linker() {
            let linker = NativeLinker::detect();
            assert!(matches!(
                linker,
                NativeLinker::Mold | NativeLinker::Lld | NativeLinker::Ld
            ));
        }

        #[test]
        fn respects_platform() {
            let linker = NativeLinker::detect();
            if cfg!(not(target_os = "linux")) {
                assert_ne!(linker, NativeLinker::Mold);
            }
        }
    }

    // Integration tests with real linker
    mod integration {
        use super::*;
        use tempfile::TempDir;

        #[test]
        #[ignore] // Requires linker installed
        fn links_simple_object() {
            let temp = TempDir::new().unwrap();
            // ... create test object file ...
        }
    }
}
```

**Test helpers:**
```rust
#[cfg(test)]
mod test_helpers {
    use super::*;

    /// Create a minimal ELF object file for testing
    pub fn create_test_object(path: &Path, symbol: &str) -> std::io::Result<()> {
        // Use LLVM or assembler to create test object
        todo!()
    }

    /// Assert linker is available, skip test if not
    pub fn require_linker(linker: NativeLinker) {
        if !linker.is_available() {
            eprintln!("Skipping: {} not available", linker.name());
            return;
        }
    }
}
```

### 6. Configuration Style

**Environment variables:**
```rust
/// Configuration keys for linker selection
pub mod config {
    /// Environment variable to override linker selection
    /// Example: SIMPLE_LINKER=mold
    pub const LINKER_ENV: &str = "SIMPLE_LINKER";

    /// Environment variable to set linker thread count
    /// Example: SIMPLE_LINKER_THREADS=4
    pub const THREADS_ENV: &str = "SIMPLE_LINKER_THREADS";

    /// Environment variable to enable linker debug output
    /// Example: SIMPLE_LINKER_DEBUG=1
    pub const DEBUG_ENV: &str = "SIMPLE_LINKER_DEBUG";
}

impl NativeLinker {
    /// Create linker from environment configuration
    pub fn from_env() -> Self {
        if let Ok(linker) = std::env::var(config::LINKER_ENV) {
            match linker.to_lowercase().as_str() {
                "mold" => return Self::Mold,
                "lld" => return Self::Lld,
                "ld" | "gnu" => return Self::Ld,
                _ => eprintln!("Unknown linker '{}', using auto-detect", linker),
            }
        }
        Self::detect()
    }
}
```

### 7. Logging Style

**Use tracing for structured logging:**
```rust
use tracing::{debug, info, warn, error, instrument, span, Level};

impl NativeLinker {
    #[instrument(skip(objects), fields(linker = %self.name(), object_count = objects.len()))]
    pub fn link(&self, objects: &[PathBuf], output: &Path) -> Result<(), LinkerError> {
        info!(output = %output.display(), "Starting link");

        let start = std::time::Instant::now();

        let result = self.execute_link(objects, output);

        let elapsed = start.elapsed();
        match &result {
            Ok(_) => info!(elapsed_ms = elapsed.as_millis(), "Link completed"),
            Err(e) => error!(error = %e, elapsed_ms = elapsed.as_millis(), "Link failed"),
        }

        result
    }
}
```

### 8. Performance Considerations

**Avoid unnecessary allocations:**
```rust
// Good: Reuse buffer
pub fn build_args(&self, invocation: &LinkerInvocation, buf: &mut Vec<String>) {
    buf.clear();
    buf.push("-o".to_string());
    buf.push(invocation.output.display().to_string());
    // ...
}

// Avoid: Allocate new vec each time
pub fn build_args(&self, invocation: &LinkerInvocation) -> Vec<String> {
    let mut args = Vec::new();
    // ...
    args
}
```

**Lazy detection:**
```rust
use std::sync::OnceLock;

static DETECTED_LINKER: OnceLock<NativeLinker> = OnceLock::new();

impl NativeLinker {
    /// Get cached detected linker (lazy initialization)
    pub fn cached() -> Self {
        *DETECTED_LINKER.get_or_init(Self::detect)
    }
}
```

### 9. Cross-Platform Compatibility

**Platform-specific code:**
```rust
impl NativeLinker {
    pub fn executable(&self) -> &str {
        match self {
            Self::Mold => "mold",
            Self::Lld => {
                #[cfg(target_os = "windows")]
                { "lld-link.exe" }
                #[cfg(not(target_os = "windows"))]
                { "ld.lld" }
            }
            Self::Ld => {
                #[cfg(target_os = "windows")]
                { "ld.exe" }
                #[cfg(not(target_os = "windows"))]
                { "ld" }
            }
        }
    }

    pub fn is_available(&self) -> bool {
        // mold is Linux-only for production use
        if *self == Self::Mold && !cfg!(target_os = "linux") {
            return false;
        }

        which::which(self.executable()).is_ok()
    }
}
```

### 10. API Stability

**Version feature gates:**
```rust
/// Features requiring specific mold version
#[derive(Debug, Clone, Copy)]
pub enum MoldFeature {
    /// Basic linking (all versions)
    Basic,
    /// RISC-V 32-bit support (v1.5.0+)
    Riscv32,
    /// Intel APX support (v2.37.0+)
    IntelApx,
}

impl MoldFeature {
    pub fn min_version(&self) -> (u32, u32, u32) {
        match self {
            Self::Basic => (1, 0, 0),
            Self::Riscv32 => (1, 5, 0),
            Self::IntelApx => (2, 37, 0),
        }
    }
}
```

---

**END OF ANALYSIS**

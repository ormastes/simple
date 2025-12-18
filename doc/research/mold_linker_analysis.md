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

**Architectures:** x86-64, i386, ARM64, ARM32, RISC-V, PowerPC (32/64), s390x, LoongArch, SPARC64, m68k, SH-4

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

**END OF ANALYSIS**

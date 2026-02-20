# Multi-Phase Bootstrap Pipeline

## Overview

The multi-phase bootstrap pipeline builds the Simple compiler using **Pure Simple** compilation paths (C codegen → GCC/LLVM) to avoid Cranelift hang bugs during bootstrap, while keeping Cranelift available in the final product for users.

## Problem Statement

### The Hang Bug

The original bootstrap process uses `SIMPLE_COMPILE_RUST=1` which activates the Cranelift JIT backend. This causes intermittent hang bugs during self-compilation, making the bootstrap process unreliable.

### Solution Strategy

**Separation of Concerns:**
- **Build Process**: Use reliable Pure Simple paths (C → GCC/LLVM) with no Cranelift
- **Product Features**: Include all backends (Cranelift, LLVM, C codegen, interpreter)

This ensures:
1. Bootstrap is reliable and completes successfully
2. End users get all features including Cranelift JIT when it works properly
3. Hang bug is isolated to bootstrap, not general product usage

## C Backend Bootstrap (Alternative)

For a simpler bootstrap path, the C backend can generate C++20 directly:

```bash
bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl
cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
ninja -C build
mkdir -p bin/bootstrap/cpp && cp build/simple bin/bootstrap/cpp/simple
```

Output: `bin/bootstrap/cpp/simple`. See `scripts/bootstrap/bootstrap-c.sh`.

## Architecture

### 5-Phase Pipeline

```
Phase 0: Pre-built Bootstrap Binary
         ↓
Phase 1: Minimal Compiler (C → GCC, fast)
         ↓
Phase 2: Full Compiler (C → GCC, all features)
         ↓
Phase 3: Self-Compiled (reproducibility check)
         ↓
Phase 4: LLVM Optimized (production binary)
```

### Compilation Backends

| Backend | Usage | Description |
|---------|-------|-------------|
| **Native** | Bootstrap (Phase 1-3) | C codegen → GCC (reliable, used for building) |
| **LLVM** | Production (Phase 4) | C codegen → LLVM IR → optimized native |
| **Cranelift** | End User | Direct JIT (fast but may hang, kept in product) |
| **Interpreter** | Always | Runtime-only mode (no compilation) |

## Phase Details

### Phase 0: Pre-built Bootstrap Binary

**Purpose:** Verify that the starting point exists

**Input:** `bin/release/simple` (pre-built runtime)

**Output:** Validated bootstrap binary

**Validation:**
- File exists check
- Size and hash computation
- Quick smoke test

### Phase 1: Minimal Compiler

**Purpose:** Build a minimal compiler quickly to enable self-hosting

**Method:** `native.spl` (C codegen → GCC)

**Command:**
```bash
bin/release/simple src/app/compile/native.spl src/app/cli/main.spl build/bootstrap/simple_phase1
```

**Features:**
- Basic compilation support
- Fast build (no optimization)
- Sufficient to compile full compiler

**Duration:** ~10-30 seconds

### Phase 2: Full Compiler

**Purpose:** Build complete compiler with all features

**Method:** Phase1 compiles via `native.spl`

**Command:**
```bash
build/bootstrap/simple_phase1 src/app/compile/native.spl src/app/cli/main.spl build/bootstrap/simple_phase2
```

**Features:**
- All stdlib modules
- Full CLI commands
- All compilation backends (code included, not used for bootstrap)
- Complete feature set

**Duration:** ~30-90 seconds

### Phase 3: Reproducibility Check

**Purpose:** Verify compiler can rebuild itself identically

**Method:** Phase2 recompiles itself via `native.spl`

**Command:**
```bash
build/bootstrap/simple_phase2 src/app/compile/native.spl src/app/cli/main.spl build/bootstrap/simple_phase3
```

**Verification:**
- SHA256 hash: `Phase2 == Phase3`
- Binary size: `Phase2 == Phase3`
- If mismatch: Warning (not fatal)

**Duration:** ~30-90 seconds

### Phase 4: LLVM Optimized Production (Optional)

**Purpose:** Create optimized production binary using LLVM

**Method:** Phase3 compiles via `llvm_direct.spl` with `-O3`

**Command:**
```bash
build/bootstrap/simple_phase3 src/app/compile/llvm_direct.spl src/app/cli/main.spl build/bootstrap/simple_phase4 -O3
```

**Optimizations:**
- LLVM IR optimization passes
- Link-time optimization (if available)
- Mold linker for faster linking

**Duration:** ~60-180 seconds

**Note:** If LLVM is not available or fails, Phase3 is used as final binary.

## Usage

### Command Line

```bash
# Full multi-phase bootstrap (recommended)
bin/simple build bootstrap-multiphase

# Quick bootstrap without LLVM optimization
./scripts/bootstrap/bootstrap-from-scratch.sh --no-llvm

# Debug mode with artifacts kept
./scripts/bootstrap/bootstrap-from-scratch.sh --keep-artifacts

# Skip reproducibility check (faster)
./scripts/bootstrap/bootstrap-from-scratch.sh --no-verify
```

### Programmatic API

```simple
use app.build.bootstrap_multiphase (
    MultiphaseBootstrap,
    MultiphaseConfig,
    CompilationBackend,
    BuildProfile
)

fn main():
    val config = MultiphaseConfig(
        profile: BuildProfile.Bootstrap,
        verify_reproducibility: true,
        use_llvm_for_final: true,
        keep_artifacts: false,
        workspace_root: ".",
        output_dir: "build/bootstrap",
        bootstrap_backend: CompilationBackend.Native,
        production_backend: CompilationBackend.LLVM
    )

    val result = MultiphaseBootstrap.run(config)

    if result.overall_success:
        print "Bootstrap successful!"
    else:
        print "Bootstrap failed!"
```

## Configuration Options

### MultiphaseConfig Fields

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `profile` | `BuildProfile` | `Bootstrap` | Build profile (Bootstrap/Debug/Release) |
| `verify_reproducibility` | `bool` | `true` | Check Phase2 == Phase3 |
| `use_llvm_for_final` | `bool` | `true` | Build Phase4 with LLVM optimization |
| `keep_artifacts` | `bool` | `false` | Keep intermediate binaries |
| `workspace_root` | `text` | `"."` | Workspace directory |
| `output_dir` | `text` | `"build/bootstrap"` | Output directory for phases |
| `bootstrap_backend` | `CompilationBackend` | `Native` | Backend for Phase1-3 |
| `production_backend` | `CompilationBackend` | `LLVM` | Backend for Phase4 |

### Command Line Flags

| Flag | Effect |
|------|--------|
| `--no-verify` | Skip Phase2/Phase3 reproducibility check |
| `--no-llvm` | Skip Phase4 LLVM optimization |
| `--keep-artifacts` | Keep all intermediate binaries after build |
| `--help` | Show usage information |

## Output Artifacts

### Build Directory Structure

```
build/bootstrap/
├── simple_phase1          # Phase 1: Minimal compiler (C→GCC)
├── simple_phase2          # Phase 2: Full compiler (C→GCC)
├── simple_phase3          # Phase 3: Self-compiled (reproducibility)
└── simple_phase4          # Phase 4: LLVM optimized (production)
```

### Final Binary

After successful bootstrap:
- **Location:** `bin/simple`
- **Source:** `build/bootstrap/simple_phase4` (or `simple_phase3` if LLVM unavailable)
- **Features:**
  - ✓ Interpreter (always available)
  - ✓ C codegen → GCC (`native.spl`)
  - ✓ C codegen → LLVM (`llvm_direct.spl`)
  - ✓ Cranelift JIT (available but not used during bootstrap)

## Performance Metrics

### Typical Duration (Intel i7, 16GB RAM, SSD)

| Phase | Duration | Cumulative |
|-------|----------|------------|
| Phase 0 | ~1s | 1s |
| Phase 1 | ~20s | 21s |
| Phase 2 | ~60s | 81s |
| Phase 3 | ~60s | 141s |
| Phase 4 | ~120s | 261s |
| **Total** | **~4-5 minutes** | |

### Binary Sizes

| Phase | Size | Notes |
|-------|------|-------|
| Phase 0 | ~33 MB | Pre-built runtime |
| Phase 1 | ~8-12 MB | Minimal compiler |
| Phase 2 | ~25-35 MB | Full compiler |
| Phase 3 | ~25-35 MB | Should match Phase2 |
| Phase 4 | ~20-30 MB | LLVM optimized (smaller due to optimization) |

## Comparison: Old vs New Bootstrap

### Old 3-Stage Bootstrap (with Cranelift)

```
Stage 1: Pre-built → simple_new1 (copy)
Stage 2: simple_new1 + CRANELIFT → simple_new2.smf
Stage 3: simple_new2.smf + CRANELIFT → simple_new3.smf
Verify: Stage2 == Stage3
```

**Problems:**
- ❌ Uses Cranelift during bootstrap (hang bugs)
- ❌ Unreliable (intermittent failures)
- ⚠️  Fast when it works (~2 minutes)

### New Multi-Phase Bootstrap (Pure Simple)

```
Phase 0: Pre-built bootstrap binary (verify)
Phase 1: Phase0 + Native → simple_phase1
Phase 2: Phase1 + Native → simple_phase2
Phase 3: Phase2 + Native → simple_phase3
Phase 4: Phase3 + LLVM → simple_phase4 (production)
```

**Benefits:**
- ✅ No Cranelift during bootstrap (reliable)
- ✅ Pure Simple compilation paths
- ✅ Reproducible builds
- ✅ Cranelift still available in final product
- ⚠️  Slower (~4-5 minutes) but reliable

## Troubleshooting

### Phase 1 Fails

**Symptom:** "Error: Phase 1 compilation failed"

**Causes:**
- Pre-built bootstrap binary is corrupted or wrong architecture
- GCC not installed or not in PATH
- Source files missing or corrupted

**Solutions:**
```bash
# Verify bootstrap binary
file bin/release/simple
bin/release/simple --version

# Check GCC
gcc --version

# Reinstall bootstrap binary
./scripts/bootstrap-build.yml
```

### Phase 2/3 Size Mismatch

**Symptom:** "Verification failed: Phase2 != Phase3"

**Causes:**
- Non-deterministic codegen (timestamps, random seeds)
- Different build environments
- Race conditions in parallel compilation

**Solutions:**
- Check stderr for warnings
- Try with `--no-verify` flag
- Report issue with hash values for investigation

### Phase 4 LLVM Missing

**Symptom:** "Phase 4 LLVM optimization failed"

**Causes:**
- LLVM tools not installed (`clang`, `opt`, `llc`)
- Wrong LLVM version
- Incompatible C code

**Solutions:**
```bash
# Install LLVM
sudo apt-get install clang llvm

# Check versions
clang --version
llc --version

# Skip LLVM optimization
./scripts/bootstrap/bootstrap-from-scratch.sh --no-llvm
```

### Out of Memory

**Symptom:** Process killed during compilation

**Causes:**
- System has < 4GB RAM
- Other processes consuming memory
- Swap disabled

**Solutions:**
```bash
# Enable swap
sudo swapon -a

# Close other applications

# Use --no-llvm to reduce memory usage
./scripts/bootstrap/bootstrap-from-scratch.sh --no-llvm
```

## Design Rationale

### Why Not Fix Cranelift Hang Bug?

**Short Answer:** Cranelift is complex and maintained upstream. Fixing the bug requires:
1. Reproducing the hang consistently
2. Bisecting Cranelift's large codebase
3. Understanding internals of JIT compiler
4. Upstreaming fix to Cranelift project

**Alternative:** Use reliable Pure Simple paths for bootstrap, keep Cranelift for end users who want JIT speed.

### Why 5 Phases Instead of 3?

**Rationale:**
- **Phase 0:** Explicit verification step (was implicit)
- **Phase 1:** Fast minimal compiler (new, enables quick iteration)
- **Phase 2-3:** Standard reproducibility check (same as old)
- **Phase 4:** LLVM optimization (new, produces smaller/faster binary)

**Benefits:**
- Faster iteration during development (Phase 1 is quick)
- Better error isolation (know which phase failed)
- Optional optimization (can skip Phase 4 if LLVM unavailable)

### Why Keep Cranelift in Product?

**Rationale:**
- Cranelift is **fast** when it works (JIT compilation)
- Many users never hit the hang bug
- Useful for REPL and quick experimentation
- Optional: Users can avoid it by using `--backend=native` or `--backend=llvm`

**Strategy:**
- Make Cranelift opt-in rather than default
- Document limitations
- Provide fallback backends

## Future Work

### Phase 0: Reproducible Bootstrap Binary

**Goal:** Ensure `bin/release/simple` is built deterministically

**Approach:**
- Document exact build process
- Pin all dependencies (GCC version, LLVM version, libc)
- Use Docker for reproducible builds
- Publish checksums

### Phase 1 Optimization

**Goal:** Make Phase 1 even faster

**Approach:**
- Implement incremental compilation
- Cache intermediate artifacts
- Parallel compilation of independent modules
- Minimal stdlib (only what's needed for Phase 2)

### Parallel Phase Execution

**Goal:** Run independent phases in parallel

**Approach:**
- Phase 2 and Phase 3 are independent after Phase 1
- Phase 4 can start while Phase 3 verification runs
- Use job scheduler to maximize CPU utilization

### Cross-Platform Bootstrap

**Goal:** Bootstrap on all supported platforms

**Status:**
- ✅ Linux x86_64 (working)
- ✅ macOS ARM64 (working with local LLVM)
- ✅ Windows x86_64 (working with MSVC or MinGW)
- ⚠️  Other platforms (needs testing)

### Formal Verification

**Goal:** Prove bootstrap correctness

**Approach:**
- Use Lean 4 to verify Phase 2 == Phase 3
- Prove compiler preserves semantics
- Model Cranelift JIT for bug analysis

## References

- **Implementation:** `src/app/build/bootstrap_multiphase.spl`
- **CLI Entry:** `src/app/build/cli_entry.spl`
- **Standalone Script:** `scripts/bootstrap/bootstrap-from-scratch.sh`
- **Old Bootstrap:** `src/app/build/bootstrap.spl` (3-stage with Cranelift)
- **Native Compiler:** `src/app/compile/native.spl` (C codegen)
- **LLVM Compiler:** `src/app/compile/llvm_direct.spl` (LLVM IR codegen)

## Related Documentation

- [Build System Guide](getting_started.md)
- [Bootstrap Process (old)](../architecture/bootstrap.md)
- [Compilation Backends](../architecture/backends.md)
- [Self-Hosting Status](../report/self_hosting.md)

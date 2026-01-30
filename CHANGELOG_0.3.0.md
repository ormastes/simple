# Simple Language v0.3.0 Release Notes

**Release Date:** 2026-01-30

## Overview

Version 0.3.0 marks a major milestone: **the Simple compiler can now compile itself** (bootstrap complete) and the default CLI is now the Simple-language implementation. This release establishes the foundation for v0.4.0, which will move most modules from Rust to Simple.

---

## 🎯 What Was Accomplished

### 1. **Bootstrap Complete** — Compiler Self-Compilation ✅
- Fixed critical Gen2 bootstrap bug (dictionary mutation in compiled mode)
- 3-stage verified bootstrap pipeline working: `simple_runtime → simple_new1 → simple_new2 → simple_new3`
- Deterministic compilation verified: `simple_new2` and `simple_new3` are bitwise identical
- Added `make bootstrap-promote` to establish stable compiler releases
- Added `bootstrap.sdn` metadata tracking for verified compilers

**Technical Details:**
- **Root cause:** Interpreter used value semantics (clone-on-write), compiled mode used reference semantics (pointer aliasing)
- **Fix:** Rewrote copy-modify-reassign patterns to direct nested field mutation in `driver.spl` and `hir.spl`
- **Impact:** Eliminates 5+ redundant dict allocations per compilation phase

### 2. **Binary Architecture Refactoring** ✅
- Renamed `simple_old` → `simple_runtime` (canonical name)
- `simple` (default CLI) now runs Simple implementation (`src/app/cli/main.spl`)
- Backward compatibility: `SIMPLE_OLD_PATH` still works, `simple_old` as legacy alias
- New env var: `SIMPLE_RUNTIME_PATH` (preferred)
- Wrappers updated: `simple`, `simple_runtime`, `simple_new` (deprecated)

**New Binary Layout:**
| Binary | Purpose |
|--------|---------|
| `simple_runtime` | Rust runtime (bootstraps Simple code) |
| `simple` | Default CLI (Simple implementation) |
| `simple_runtime` (wrapper) | Direct Rust runtime access |

### 3. **Stable Release Workflow** ✅
- `make bootstrap-promote` — Promote verified compiler to `target/stable/`
- `bootstrap.sdn` — Track bootstrap metadata (hashes, revisions)
- `make bootstrap-from-stable` — Verify stable compiler reproducibility

### 4. **Documentation Updates** ✅
- Updated `CLAUDE.md` executable architecture table
- Renamed all `simple_old` references to `simple_runtime`
- Added bootstrap workflow documentation

---

## 📋 What Was Planned But Not Done

These features are **deferred to v0.4.0**:

### 1. **Port More Modules to Simple** (v0.4.0)
- Loader subsystem (currently Rust)
- Compiler subsystem (partially in Simple, needs completion)
- Interpreter subsystem (currently Rust)
- Goal: 80%+ of codebase in Simple language

### 2. **Performance Optimization** (v0.4.0)
- Loader/compiler/interpreter performance tuning
- Memory usage optimization (GC tuning, allocation reduction)
- JIT compilation optimizations
- Profile-guided optimization (PGO)

### 3. **LLM Training/Inference Examples** (v0.4.0)
- Example: Train small transformer model in Simple
- Example: Run inference on pre-trained models
- Demonstrate dimension checking with `~>` operator
- Tensor operation performance benchmarks

### 4. **Architecture Refactoring** (v0.4.0)
- Remove code duplication (detected by `make duplication`)
- Refactor oversized files (>1000 lines)
- Layer separation enforcement (arch_test improvements)
- Dependency graph cleanup

### 5. **Test Infrastructure** (Not Done)
- Fix pre-existing test compilation errors:
  - `simple-tests-new`: `TokenKind::DoubleSlash` doesn't exist
  - `simple-compiler`: `FunctionDef` missing `is_static` field
- 7 failing lib tests in `simple-compiler`
- These are pre-0.3.0 issues, not introduced in this release

---

## 🔢 Statistics

**Code Changes (v0.3.0):**
- Files modified: 11
- Lines changed: ~200
- Key fixes: 8 copy-modify-reassign patterns eliminated
- Tests: 2254 passed (lib tests), pre-existing failures unaffected

**Bootstrap Verification:**
- Stage 1: `simple_runtime` → `simple_new1` ✅
- Stage 2: `simple_new1` → `simple_new2` ✅
- Stage 3: `simple_new2` → `simple_new3` ✅
- Verification: `SHA256(simple_new2) == SHA256(simple_new3)` ✅

---

## 🚀 Roadmap to v0.4.0

**Primary Goals:**
1. **80%+ Simple Codebase** — Move loader, compiler, interpreter to Simple
2. **Performance** — 2-3x faster compilation, 30% less memory
3. **Examples** — LLM training/inference demonstrations
4. **Architecture** — Refactor duplication, enforce layer boundaries
5. **Stability** — Fix pre-existing test failures, 100% pass rate

**Target Timeline:** Q2 2026

---

## 🛠️ Migration Guide

### For Users

**Before (v0.2.0):**
```bash
./target/debug/simple_old script.spl
SIMPLE_OLD_PATH=/custom/path simple_old test
```

**After (v0.3.0):**
```bash
./target/debug/simple_runtime script.spl  # Direct runtime
./bin/wrappers/simple script.spl          # Simple CLI (recommended)
SIMPLE_RUNTIME_PATH=/custom/path simple test
```

**Backward Compatibility:**
- `simple_old` binary name still works (for now)
- `SIMPLE_OLD_PATH` env var still works
- `simple_new` wrapper redirects to `simple`

### For Developers

**Bootstrap Workflow:**
```bash
# Build and verify bootstrap
make bootstrap

# Promote to stable
make bootstrap-promote

# Verify stable reproducibility
make bootstrap-from-stable
```

**Binary Discovery Order:**
1. `SIMPLE_RUNTIME_PATH` env var (new)
2. `SIMPLE_OLD_PATH` env var (legacy)
3. `target/debug/simple_runtime`
4. `target/debug/simple_old` (fallback)

---

## 🐛 Known Issues

1. **Pre-existing test failures** (not caused by v0.3.0):
   - 7 lib test failures in `simple-compiler`
   - Test compilation errors in `simple-tests-new` and `simple-compiler`
   - These will be fixed in v0.4.0

2. **Performance** (deferred to v0.4.0):
   - Bootstrap is ~3x slower than direct Rust compilation
   - Memory usage during compilation is higher than optimal
   - Loader/interpreter not yet optimized

---

## 📦 Installation

```bash
# Build from source
git clone https://github.com/anthropics/simple.git
cd simple
cargo build --workspace

# Run bootstrap
make bootstrap

# Verify
./target/debug/simple_runtime --version
./bin/wrappers/simple --version
```

---

## 🙏 Acknowledgments

- Bootstrap bug diagnosis and fix
- Binary architecture redesign
- Documentation improvements
- Stable release workflow design

---

## 📄 License

MIT License (see LICENSE file)

---

**Next Release:** v0.4.0 (Target: Q2 2026)
- Focus: Port to Simple, performance, examples, architecture refactoring

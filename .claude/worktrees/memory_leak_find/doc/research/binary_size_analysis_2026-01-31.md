# Binary Size Analysis - Simple Compiler

**Date:** 2026-01-31
**Status:** Critical - Debug binary is 423MB, Release is 40MB

## Executive Summary

The Simple compiler binary is critically oversized:
- **Debug build:** 423 MB (unacceptable for development)
- **Release build:** 40 MB (10x too large for a compiler runtime)
- **Target:** 15-20 MB release binary (60-75% reduction needed)

**Estimated savings with proposed changes:** 15-20 MB (37-50% reduction to 20-25 MB)

---

## Current Binary Analysis

### Size Breakdown (cargo-bloat results)

**Top 10 Crates by .text section size:**

| Rank | Crate | Size | % of .text | Issue |
|------|-------|------|-----------|-------|
| 1 | simple_compiler | 4.6 MB | 24.2% | Core interpreter + codegen |
| 2 | cranelift_codegen | 4.0 MB | 21.2% | **ALL architectures included** |
| 3 | simple_parser | 1.7 MB | 8.7% | Lexer/parser (necessary) |
| 4 | simple_driver | 1.5 MB | 7.8% | CLI main binary |
| 5 | std | 1.4 MB | 7.2% | Rust standard library |
| 6 | reqwest | 503 KB | 2.6% | **Heavy HTTP client** |
| 7 | simple_runtime | 468 KB | 2.4% | Runtime FFI |
| 8 | rustls | 460 KB | 2.4% | TLS stack (from reqwest) |
| 9 | regex_automata | 447 KB | 2.3% | Regex engine |
| 10 | ring | 283 KB | 1.5% | Crypto (from reqwest/rustls) |

**Total .text section:** 18.9 MB
**Total file size:** 39.3 MB
**Other sections:** 20.4 MB (data, rodata, bss, relocation tables)

### Cranelift Architecture Bloat (CRITICAL)

**Problem:** Line 41 in `rust/compiler/Cargo.toml`:
```toml
cranelift-codegen = { version = "0.116", features = ["std", "unwind", "all-arch"] }
```

The `all-arch` feature compiles support for **ALL** architectures:
- x86_64 (needed for this build)
- aarch64 (ARM64)
- riscv64 (RISC-V)
- s390x (IBM mainframe)
- pulley32/pulley64 (interpreter backends)

**Evidence from cargo-bloat:**
- `cranelift_codegen::isa::riscv64::lower` - 83.8 KB
- `cranelift_codegen::isa::x64::lower` - 81.9 KB
- `cranelift_codegen::isa::s390x::lower` - 65.6 KB
- `cranelift_codegen::isa::aarch64::lower` - 51.1 KB
- Multiple register allocator instances per architecture (31 KB each)

**Estimated waste:** 2-3 MB of unused architecture backends

---

## Major Issues

### 1. Cranelift All-Arch Feature (2-3 MB waste)

**Current:** `features = ["std", "unwind", "all-arch"]`
**Problem:** Includes x86_64, aarch64, riscv64, s390x, pulley32, pulley64 all at once
**Solution:** Remove `all-arch`, use host architecture only

**Impact:** 2-3 MB reduction (5-7.5% of total binary)

**File:** `rust/compiler/Cargo.toml:41`

### 2. Reqwest HTTP Client (2-3 MB waste)

**Problem:** Heavy async HTTP client with full TLS stack
- reqwest: 503 KB
- rustls: 460 KB
- ring (crypto): 283 KB
- h2 (HTTP/2): 205 KB
- hyper: 138 KB
- Plus tokio async runtime overhead

**Alternative:** Project already has lightweight `ureq` client (149 KB)

**Impact:** 1.5-2 MB reduction by replacing reqwest with ureq

**Files to check:**
- `rust/driver/Cargo.toml` - likely imports reqwest
- Search for `use reqwest::` in driver code

### 3. Build Profile Not Optimized (3-5 MB waste)

**Current default:** `[profile.release]`
```toml
strip = false          # Preserves symbols/debug info
lto = false            # No link-time optimization
codegen-units = 16     # Faster builds, worse optimization
```

**Available optimized profile:** `[profile.release-opt]`
```toml
strip = "symbols"      # Remove debug symbols
lto = "fat"            # Full link-time optimization
codegen-units = 1      # Better function placement/inlining
panic = "abort"        # Smaller panic handling
```

**Impact:** 3-5 MB reduction (already proven by existing profile)

**Action:** Make `release-opt` the default or use `cargo build --profile release-opt`

### 4. Ratatui TUI in Default Features (1-2 MB waste)

**Problem:** `rust/runtime/Cargo.toml:18`
```toml
default = ["cpu-simd", "ratatui-tui"]
```

The terminal UI framework (ratatui + crossterm) is always linked even if not used.

**Impact:** 1-2 MB reduction by making it opt-in

**Solution:** Change to `default = ["cpu-simd"]`

### 5. Proc-Macro/Syn Ecosystem (Analysis needed)

**Observation:** `libsyn.rlib` is 13 MB in build artifacts

These are compile-time macros but get linked into the binary:
- serde_derive
- thiserror_impl
- strum_macros

**Status:** Difficult to optimize without major refactoring, low priority

---

## Build Profile Comparison

| Profile | opt-level | LTO | codegen-units | strip | panic | Expected Size |
|---------|-----------|-----|---------------|-------|-------|---------------|
| dev | 0 | false | 256 | false | unwind | 423 MB |
| release | 3 | false | 16 | false | unwind | 40 MB |
| release-opt | 3 | fat | 1 | symbols | abort | **25-30 MB** |

---

## Reduction Plan

### Phase 1: Quick Wins (5-8 MB reduction)

**Priority:** P0 - Immediate
**Effort:** 15 minutes
**Risk:** Low

1. **Use release-opt profile**
   - Command: `cargo build --profile release-opt -p simple-driver`
   - Expected: 3-5 MB reduction

2. **Remove Cranelift all-arch**
   - Edit: `rust/compiler/Cargo.toml:41`
   - Change: `features = ["std", "unwind", "all-arch"]` → `features = ["std", "unwind"]`
   - Expected: 2-3 MB reduction

**Total Phase 1:** 5-8 MB reduction → **32-35 MB binary**

### Phase 2: Feature Optimization (2-3 MB reduction)

**Priority:** P1 - High
**Effort:** 30 minutes
**Risk:** Low (needs testing)

3. **Make ratatui-tui optional**
   - Edit: `rust/runtime/Cargo.toml:18`
   - Change: `default = ["cpu-simd", "ratatui-tui"]` → `default = ["cpu-simd"]`
   - Add build flag if TUI is needed: `--features ratatui-tui`
   - Expected: 1-2 MB reduction

4. **Replace reqwest with ureq**
   - Find all `use reqwest::` in driver code
   - Replace with ureq API calls
   - Remove reqwest from dependencies
   - Expected: 1.5-2 MB reduction

**Total Phase 2:** 2.5-4 MB reduction → **27-30 MB binary**

### Phase 3: Advanced Optimization (3-5 MB reduction)

**Priority:** P2 - Medium
**Effort:** 2-4 hours
**Risk:** Medium (needs careful testing)

5. **Make Cranelift optional at runtime**
   - Add feature flag: `cranelift-jit`
   - Default to interpreter-only runtime
   - Only include Cranelift for compiler binary
   - Expected: 4-5 MB reduction

6. **Split runtime vs compiler binaries**
   - Create `simple_runtime` (interpreter only): ~15 MB
   - Create `simple_compiler` (full tooling): ~35 MB
   - Most users only need runtime binary
   - Expected: Effective 50% reduction for end-users

**Total Phase 3:** 3-5 MB reduction → **20-25 MB binary**

### Phase 4: Long-term Architecture (Months)

7. **Evaluate LLVM backend vs Cranelift**
   - LLVM might be smaller for production builds
   - Cranelift faster for development

8. **Reduce proc-macro usage**
   - Evaluate manual implementations vs derive macros
   - Low priority - marginal gains

---

## Validation Commands

### Before Changes
```bash
# Current release size
cargo build --release -p simple-driver
ls -lh rust/target/release/simple_runtime
# Expected: 40 MB

# Analyze by crate
cargo bloat --release -p simple-driver --crates

# Analyze by symbol
cargo bloat --release -p simple-driver -n 50
```

### After Phase 1
```bash
# Test release-opt profile
cargo build --profile release-opt -p simple-driver
ls -lh rust/target/release-opt/simple_runtime
# Expected: 32-35 MB

# Remove all-arch and rebuild
# Edit rust/compiler/Cargo.toml first
cargo clean -p simple-compiler
cargo build --profile release-opt -p simple-driver
# Expected: 28-32 MB
```

### After Phase 2
```bash
# Test without ratatui
# Edit rust/runtime/Cargo.toml first
cargo clean -p simple-runtime
cargo build --profile release-opt -p simple-driver --no-default-features --features cpu-simd
# Expected: 27-30 MB

# Test with ureq instead of reqwest
# After code changes
cargo build --profile release-opt -p simple-driver
# Expected: 25-28 MB
```

---

## Key File Paths

### Configuration Files
- `rust/Cargo.toml` - Workspace config with build profiles
- `rust/compiler/Cargo.toml` - **Line 41: all-arch feature**
- `rust/runtime/Cargo.toml` - **Line 18: default features**
- `rust/driver/Cargo.toml` - Main binary dependencies

### Build Artifacts
- `rust/target/release/simple_runtime` - Current 40 MB binary
- `rust/target/release-opt/` - Optimized profile output (not yet built)
- `rust/target/release/deps/` - Individual crate .rlib files

### Source Code
- `rust/driver/src/` - CLI implementation (check for reqwest usage)
- `rust/compiler/src/` - Compiler implementation (uses Cranelift)
- `rust/runtime/src/` - Runtime FFI (includes ratatui)

---

## Success Criteria

### Phase 1 Target (Immediate)
- [x] Debug build analyzed
- [x] Release build analyzed
- [ ] release-opt profile tested
- [ ] all-arch removed from Cranelift
- [ ] Binary size: **32-35 MB** (12-20% reduction)

### Phase 2 Target (1 week)
- [ ] ratatui made optional
- [ ] reqwest replaced with ureq
- [ ] Binary size: **27-30 MB** (25-32% reduction)

### Phase 3 Target (1 month)
- [ ] Cranelift made optional
- [ ] Runtime/compiler split evaluated
- [ ] Binary size: **20-25 MB** (37-50% reduction)

### Final Target (Long-term)
- [ ] Runtime-only binary: **15-20 MB**
- [ ] Compiler binary: **25-35 MB**
- [ ] 50%+ reduction from baseline

---

## Notes

### Why is debug build 423 MB?
- No LTO, no optimization, full debug symbols
- codegen-units = 256 (massive parallelism, no cross-crate optimization)
- Each crate compiled separately with full metadata
- Not stripped, includes DWARF debug info

### Why is Cranelift so large?
- ISLE (Instruction Selection/Lowering Engine) generates massive pattern matchers
- Each architecture backend has thousands of lowering rules
- Register allocator duplicated per architecture
- This is intentional for Cranelift's design (fast compilation)

### Can we use smaller features?
- Yes! Cranelift supports per-architecture features
- Default should be host architecture only
- Cross-compilation can enable specific targets as needed

### Is LTO worth it?
- Yes, "fat" LTO with codegen-units=1 reduces binary by 3-5 MB
- Compilation time increases from 1m to 3-5m
- Worth it for release builds, not for development

---

## References

- Cranelift architecture support: https://docs.rs/cranelift-codegen/latest/cranelift_codegen/isa/
- Cargo profiles: https://doc.rust-lang.org/cargo/reference/profiles.html
- cargo-bloat: https://github.com/RazrFalcon/cargo-bloat
- Size optimization guide: https://github.com/johnthagen/min-sized-rust

---

## Appendix: cargo-bloat Output

### By Crate (.text section)
```
 File  .text     Size Crate
11.7%  24.2%   4.6MiB simple_compiler
10.2%  21.2%   4.0MiB cranelift_codegen
 4.2%   8.7%   1.7MiB simple_parser
 3.7%   7.8%   1.5MiB simple_driver
 3.4%   7.2%   1.4MiB std
 1.3%   2.6% 503.4KiB reqwest
 1.2%   2.4% 468.5KiB simple_runtime
 1.1%   2.4% 460.1KiB rustls
 1.1%   2.3% 447.4KiB regex_automata
 0.7%   1.5% 283.2KiB ring
```

### Top Symbols (functions)
```
 0.4%   0.8% 156.1KiB cranelift_codegen::opts::generated_code::constructor_simplify
 0.2%   0.4%  83.8KiB cranelift_codegen::isa::riscv64::lower::isle::generated_code::constructor_lower
 0.2%   0.4%  81.9KiB cranelift_codegen::isa::x64::lower::isle::generated_code::constructor_lower
 0.2%   0.3%  65.6KiB cranelift_codegen::isa::s390x::lower::isle::generated_code::constructor_lower
 0.2%   0.3%  63.9KiB simple_compiler::interpreter::interpreter_method::evaluate_method_call
```

Note: Multiple architecture backends (riscv64, x64, s390x, aarch64) are all present in the binary.

# Bootstrap Compiler Size Optimization Research

**Date:** 2026-01-31
**Current Status:** 9.4 MB (bootstrap profile, stripped)
**Research Goal:** Identify additional optimization opportunities for minimal bootstrap compiler

---

## Current Binary Analysis

### Section Breakdown (9.4 MB total)

```
   text     data      bss      total
9,309,870  461,072  17,244  9,788,186 bytes (9.33 MB)
```

**Breakdown:**
- `.text` (code): 9.3 MB (95.1%)
- `.data` (initialized): 461 KB (4.7%)
- `.bss` (uninitialized): 17 KB (0.2%)

**Analysis:** 95% of binary is executable code - further optimization must focus on reducing compiled code size.

---

## Additional Optimization Techniques

### 1. Build-std (Stdlib from Source) ⭐⭐⭐

**Potential Savings:** 15-25% (1.4-2.4 MB)

**Description:** Compile Rust standard library from source with size optimizations applied.

**Implementation:**
```toml
# .cargo/config.toml
[unstable]
build-std = ["std", "panic_abort"]
build-std-features = ["panic_immediate_abort"]

[build]
target = "x86_64-unknown-linux-gnu"
```

**Build command:**
```bash
cargo +nightly build --profile bootstrap -p simple-driver \
  -Z build-std=std,panic_abort \
  -Z build-std-features=panic_immediate_abort
```

**Trade-offs:**
- ✅ Can reduce stdlib overhead by 15-25%
- ✅ Applies size optimizations to stdlib itself
- ❌ Requires nightly Rust
- ❌ Slower compilation
- ❌ May break on stdlib updates

**Expected final size:** ~7-8 MB

**Sources:**
- [Making Rust binaries smaller by default](https://kobzol.github.io/rust/cargo/2024/01/23/making-rust-binaries-smaller-by-default.html)
- [Optimizing bitdrift's Rust mobile SDK for binary size](https://blog.bitdrift.io/post/optimizing-rust-mobile-sdk-binary-size)

---

### 2. UPX Compression ⭐⭐⭐

**Potential Savings:** 50-70% (4.7-6.6 MB)

**Description:** Post-build executable compression that decompresses on startup.

**Implementation:**
```bash
# Install UPX
sudo apt-get install upx

# Compress with maximum settings
upx --best --lzma target/bootstrap/simple_runtime

# Alternative: Ultra-brute (slower but smaller)
upx --ultra-brute target/bootstrap/simple_runtime
```

**Expected sizes:**
- `--best`: ~4.5-5 MB (52% reduction)
- `--ultra-brute`: ~3.5-4 MB (62% reduction)

**Trade-offs:**
- ✅ Dramatic size reduction (50-70%)
- ✅ No code changes required
- ✅ Self-extracting (no runtime dependencies)
- ❌ Slower startup time (+10-50ms)
- ❌ Cannot mmap compressed binaries
- ❌ Some antivirus software flags UPX binaries
- ❌ Incompatible with code signing on some platforms

**Sources:**
- [Cross compilation for Rust and how to reduce binary sizes by 88%](https://codepitbull.medium.com/cross-compilation-for-rust-and-how-to-reduce-binary-sizes-by-88-269deea50c1b)
- [6 Proven Techniques to Reduce Rust Binary Size](https://elitedev.in/rust/6-proven-techniques-to-reduce-rust-binary-size/)
- [GitHub - johnthagen/min-sized-rust](https://github.com/johnthagen/min-sized-rust)

---

### 3. Opt-level "s" vs "z" ⭐

**Potential Savings:** 0-5% (0-470 KB)

**Description:** Try `opt-level = "s"` instead of `"z"` - sometimes produces smaller binaries.

**Implementation:**
```toml
[profile.bootstrap-s]
inherits = "bootstrap"
opt-level = "s"  # Size optimization (less aggressive than "z")
```

**Test:**
```bash
cargo build --profile bootstrap-s -p simple-driver
```

**Trade-offs:**
- ✅ Easy to test
- ✅ May produce smaller binary than "z"
- ❌ Results vary by codebase
- ❌ Requires benchmarking both

**Sources:**
- [Optimizing Rust Compilation: Smaller, Faster, or Both?](https://leapcell.medium.com/optimizing-rust-compilation-smaller-faster-or-both-1cdac7bfd93c)
- [Binary Size Optimization - Rust Project Primer](https://rustprojectprimer.com/building/size.html)

---

### 4. Remove Unused Dependencies ⭐⭐

**Potential Savings:** 5-10% (470-940 KB)

**Description:** Audit and remove unused crate features.

**Tools:**
```bash
# Find unused dependencies
cargo install cargo-udeps
cargo +nightly udeps

# Find unused features
cargo install cargo-unused-features
cargo unused-features analyze
cargo unused-features prune
```

**Current candidates from bloat analysis:**
- `regex_automata`: 394 KB (could make regex optional)
- `rustyline`: 130 KB (could use simpler readline)
- `serde_yaml`: 89 KB (already using SDN, could remove YAML)
- `serde_json`: 120 KB (could minimize JSON usage)

**Trade-offs:**
- ✅ Reduces bloat
- ✅ Faster compile times
- ❌ May remove functionality
- ❌ Requires careful testing

**Sources:**
- [Rust Project Primer - Binary Size](https://rustprojectprimer.com/building/size.html)
- [How to Reduce Rust Binary Size by 43%](https://markaicode.com/binary-size-optimization-techniques/)

---

### 5. Alternative Allocator ⭐

**Potential Savings:** 0-200 KB

**Description:** Use system allocator instead of default (currently system is default in recent Rust).

**Implementation:**
```rust
// src/main.rs or lib.rs
use std::alloc::System;

#[global_allocator]
static GLOBAL: System = System;
```

**Trade-offs:**
- ✅ Smaller binary (no custom allocator)
- ✅ Already default in Rust 1.32+
- ❌ May be slower than jemalloc/mimalloc
- ❌ Minimal benefit if already using system allocator

**Note:** Simple currently uses mimalloc/jemalloc in runtime - check if removing saves space.

**Sources:**
- [System Allocator - Rust Docs](https://doc.rust-lang.org/std/alloc/struct.System.html)
- [Binary size reduction after overriding allocator](https://github.com/rust-lang/rust/issues/55910)

---

### 6. Abort on Panic (Everywhere) ⭐

**Potential Savings:** 100-300 KB

**Description:** Ensure panic=abort is used in all dependencies.

**Current:** Already using `panic = "abort"` in bootstrap profile.

**Additional:**
```toml
[profile.bootstrap]
panic = "abort"

[profile.bootstrap.package."*"]
panic = "abort"  # Apply to all dependencies
```

**Trade-offs:**
- ✅ Removes unwinding code
- ✅ Smaller binary
- ❌ Cannot catch panics
- ❌ Less useful error messages

**Sources:**
- [Embedded Rust Book - Speed vs Size](https://docs.rust-embedded.org/book/unsorted/speed-vs-size.html)

---

### 7. Strip More Aggressively ⭐⭐

**Potential Savings:** 50-200 KB

**Description:** Use external strip tools for more aggressive stripping.

**Implementation:**
```bash
# After build, strip with maximum settings
strip --strip-all target/bootstrap/simple_runtime

# Alternative: Use sstrip (even more aggressive)
sstrip target/bootstrap/simple_runtime

# Or use objcopy to remove all sections except essentials
objcopy --only-section=.text --only-section=.rodata \
  target/bootstrap/simple_runtime \
  target/bootstrap/simple_runtime_minimal
```

**Trade-offs:**
- ✅ Removes all non-essential data
- ❌ Breaks debuggers completely
- ❌ May break some introspection

**Sources:**
- [Minimizing Rust Binary Size](https://github.com/johnthagen/min-sized-rust)

---

### 8. Feature-Gate Heavy Dependencies ⭐⭐

**Potential Savings:** 500 KB - 1 MB

**Description:** Make more features optional.

**Current candidates:**
- Regex support (394 KB)
- YAML support (89 KB)
- Advanced CLI features

**Implementation:**
```toml
[features]
default = []
regex = ["dep:regex", "dep:regex_automata"]
yaml = ["dep:serde_yaml"]
cli-full = ["regex", "yaml", "rustyline"]
```

**Trade-offs:**
- ✅ Users can build minimal binary
- ❌ More complex build matrix
- ❌ Some features become opt-in

---

### 9. Profile-Guided Optimization (PGO) ⭐

**Potential Savings:** 5-10% (470-940 KB)

**Description:** Use runtime profiling data to optimize code layout.

**Implementation:**
```bash
# 1. Build with instrumentation
RUSTFLAGS="-Cprofile-generate=/tmp/pgo-data" \
  cargo build --profile bootstrap -p simple-driver

# 2. Run typical workloads
./target/bootstrap/simple_runtime test
./target/bootstrap/simple_runtime examples/*.spl

# 3. Rebuild with PGO data
llvm-profdata merge -o /tmp/pgo-data/merged.profdata /tmp/pgo-data

RUSTFLAGS="-Cprofile-use=/tmp/pgo-data/merged.profdata -Cllvm-args=-pgo-warn-missing-function" \
  cargo build --profile bootstrap -p simple-driver
```

**Trade-offs:**
- ✅ Better code layout
- ✅ Can reduce size and improve speed
- ❌ Complex build process
- ❌ Requires representative workload

**Sources:**
- [Rust Cargo.toml workspace comment](https://github.com/johnthagen/min-sized-rust)

---

### 10. Link with mold/lld ⭐

**Potential Savings:** 0-2% (0-190 KB) + faster linking

**Description:** Use modern linker for better optimization.

**Implementation:**
```toml
# .cargo/config.toml
[target.x86_64-unknown-linux-gnu]
linker = "clang"
rustflags = ["-C", "link-arg=-fuse-ld=mold"]
```

**Trade-offs:**
- ✅ Faster linking
- ✅ May produce smaller binaries
- ❌ Requires mold/lld installed
- ❌ Minimal size benefit

---

## Optimization Strategy Tiers

### Tier 1: Low-Hanging Fruit (Easy Wins)

**Effort:** Low | **Savings:** 15-20% | **Recommended:** ✅

1. UPX compression (`--best`): ~4.5 MB final size
2. Test `opt-level = "s"`: May save 5%
3. Strip with external tools: +50-200 KB savings

**Expected:** 9.4 MB → **~4.5-5 MB** (with UPX)

---

### Tier 2: Moderate Effort (High Impact)

**Effort:** Medium | **Savings:** 20-30% | **Recommended:** ✅ (for minimal builds)

1. build-std with nightly: 15-25% savings
2. Feature-gate heavy dependencies: 500 KB - 1 MB
3. Audit and remove unused features: 5-10%

**Expected:** 9.4 MB → **~6-7 MB** (without UPX)

---

### Tier 3: Advanced (Diminishing Returns)

**Effort:** High | **Savings:** 5-10% | **Recommended:** ⚠️ (case-by-case)

1. Profile-Guided Optimization: 5-10%
2. Custom minimal allocator: 100-200 KB
3. Replace heavy dependencies with lighter alternatives

**Expected:** Additional 5-10% reduction

---

## Recommended Implementation Plan

### Phase 7a: Quick Wins (15 minutes)

```bash
# 1. Test opt-level "s"
# Add to Cargo.toml:
[profile.bootstrap-s]
inherits = "bootstrap"
opt-level = "s"

# Build and compare
cargo build --profile bootstrap-s -p simple-driver
ls -lh target/bootstrap*/simple_runtime

# 2. Apply UPX compression
upx --best --lzma target/bootstrap/simple_runtime
# Expected: 9.4 MB → 4.5 MB
```

**Expected result:** 9.4 MB → **4.5 MB** (52% additional reduction)

---

### Phase 7b: Build-std (45 minutes, nightly required)

```bash
# 1. Install nightly and rust-src
rustup toolchain install nightly
rustup component add rust-src --toolchain nightly

# 2. Create .cargo/config.toml
mkdir -p .cargo
cat > .cargo/config.toml << 'EOF'
[unstable]
build-std = ["std", "panic_abort"]
build-std-features = ["panic_immediate_abort"]
EOF

# 3. Build with build-std
cargo +nightly build --profile bootstrap -p simple-driver \
  -Z build-std=std,panic_abort \
  -Z build-std-features=panic_immediate_abort \
  --target x86_64-unknown-linux-gnu

# 4. Strip and compress
strip --strip-all target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime
upx --best target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime
```

**Expected result:** 9.4 MB → **3.5-4 MB** (58-62% additional reduction)

---

### Phase 7c: Feature Audit (2 hours)

```bash
# 1. Install analysis tools
cargo install cargo-udeps cargo-unused-features

# 2. Find unused dependencies
cargo +nightly udeps --all-targets

# 3. Find unused features
cargo unused-features analyze
cargo unused-features prune

# 4. Make heavy dependencies optional
# Edit Cargo.toml to add feature flags for:
# - regex (394 KB)
# - serde_yaml (89 KB)
# - rustyline (130 KB)

# 5. Build minimal variant
cargo build --profile bootstrap -p simple-driver --no-default-features
```

**Expected result:** 9.4 MB → **8-8.5 MB** (10-15% reduction)

---

## Final Size Projections

| Approach | Current | Final Size | Reduction | Effort |
|----------|---------|-----------|-----------|--------|
| **Current baseline** | 9.4 MB | 9.4 MB | - | - |
| **+ UPX (--best)** | 9.4 MB | **4.5 MB** | 52% | Low |
| **+ build-std** | 9.4 MB | 7-8 MB | 15-25% | Medium |
| **+ build-std + UPX** | 9.4 MB | **3.5-4 MB** | 58-62% | Medium |
| **+ All optimizations** | 9.4 MB | **2.5-3 MB** | 68-73% | High |

---

## Recommendations by Use Case

### For General Distribution
**Recommended:** UPX compression only
```bash
cargo build --profile bootstrap -p simple-driver
upx --best target/bootstrap/simple_runtime
# Result: ~4.5 MB
```

**Pros:** Simple, portable, dramatic size reduction
**Cons:** Slight startup delay (~10-20ms)

---

### For Embedded/Constrained Environments
**Recommended:** build-std + UPX + feature pruning
```bash
cargo +nightly build --profile bootstrap -p simple-driver \
  -Z build-std=std,panic_abort \
  --no-default-features --features minimal
strip --strip-all target/.../simple_runtime
upx --ultra-brute target/.../simple_runtime
# Result: ~2.5-3 MB
```

**Pros:** Absolute minimum size
**Cons:** Nightly required, longer build, limited features

---

### For CI/CD Pipelines
**Recommended:** Current bootstrap profile (no UPX)
```bash
cargo build --profile bootstrap -p simple-driver
# Result: 9.4 MB
```

**Pros:** Fast startup, no decompression overhead
**Cons:** Larger download size

---

## Tools for Analysis

```bash
# Size analysis
cargo install cargo-bloat
cargo bloat --profile bootstrap --crates

# Dependency analysis
cargo install cargo-tree
cargo tree -p simple-driver

# Unused dependencies
cargo install cargo-udeps
cargo +nightly udeps

# Unused features
cargo install cargo-unused-features
cargo unused-features analyze

# Binary inspection
size target/bootstrap/simple_runtime
readelf -S target/bootstrap/simple_runtime
objdump -h target/bootstrap/simple_runtime
```

---

## Conclusion

**Current:** 9.4 MB (76.5% reduction from 40 MB original)

**Recommended next step:** UPX compression for **4.5 MB** (additional 52% reduction)

**Maximum possible:** ~2.5-3 MB with all optimizations (93% total reduction)

**Best balance:** build-std + UPX = **3.5-4 MB** (90% total reduction)

For most use cases, **applying UPX compression to the current 9.4 MB binary is the best ROI** - it takes 30 seconds, requires no code changes, and cuts the size in half.

---

## Sources

- [GitHub - min-sized-rust](https://github.com/johnthagen/min-sized-rust)
- [Making Rust binaries smaller by default](https://kobzol.github.io/rust/cargo/2024/01/23/making-rust-binaries-smaller-by-default.html)
- [Binary Size Optimization - Rust Project Primer](https://rustprojectprimer.com/building/size.html)
- [Optimizing Rust Compilation](https://leapcell.medium.com/optimizing-rust-compilation-smaller-faster-or-both-1cdac7bfd93c)
- [Embedded Rust Book - Speed vs Size](https://docs.rust-embedded.org/book/unsorted/speed-vs-size.html)
- [How to Reduce Rust Binary Size by 43%](https://markaicode.com/binary-size-optimization-techniques/)
- [Cross compilation and binary size reduction](https://codepitbull.medium.com/cross-compilation-for-rust-and-how-to-reduce-binary-sizes-by-88-269deea50c1b)
- [6 Proven Techniques to Reduce Rust Binary Size](https://elitedev.in/rust/6-proven-techniques-to-reduce-rust-binary-size/)
- [Optimizing bitdrift's Rust mobile SDK](https://blog.bitdrift.io/post/optimizing-rust-mobile-sdk-binary-size)
- [Rust System Allocator Docs](https://doc.rust-lang.org/std/alloc/struct.System.html)

**Research Date:** 2026-01-31

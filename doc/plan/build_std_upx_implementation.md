# Build-std + UPX Implementation Plan

**Date:** 2026-01-31
**Goal:** Apply build-std optimization + create UPX library for Simple programs
**Expected:** 9.4 MB → 3.5-4 MB bootstrap binary + UPX library for Simple code

---

## Phase 1: Build-std Setup (30 minutes)

### 1.1 Prerequisites
- Install nightly toolchain
- Install rust-src component
- Configure build-std

### 1.2 Configuration Files

**Create `.cargo/config.toml`:**
```toml
[unstable]
build-std = ["std", "panic_abort"]
build-std-features = ["panic_immediate_abort"]

[build]
target = "x86_64-unknown-linux-gnu"
```

**Update `rust/Cargo.toml`:**
- Add build-std profile
- Document nightly requirement

### 1.3 Build & Verify
```bash
cargo +nightly build --profile bootstrap -p simple-driver \
  -Z build-std=std,panic_abort \
  -Z build-std-features=panic_immediate_abort \
  --target x86_64-unknown-linux-gnu

# Expected: 7-8 MB (15-25% smaller than 9.4 MB)
```

---

## Phase 2: UPX Library Integration (45 minutes)

### 2.1 Rust UPX Wrapper

**Options:**
1. Use `upx` crate (if exists)
2. Call UPX binary via `std::process::Command`
3. Use `compress` crate + custom ELF manipulation

**Chosen:** Call UPX binary (most reliable, matches CLI behavior)

**Location:** `rust/runtime/src/compress/upx.rs`

### 2.2 Implementation

**Create UPX module:**
```rust
// rust/runtime/src/compress/upx.rs
pub fn compress_file(input: &str, output: &str, level: CompressionLevel) -> Result<(), String>
pub fn decompress_file(input: &str, output: &str) -> Result<(), String>
pub fn is_compressed(file: &str) -> Result<bool, String>
pub fn get_compressed_ratio(file: &str) -> Result<f64, String>

pub enum CompressionLevel {
    Fast,      // --fast
    Best,      // --best
    UltraBrute // --ultra-brute
}
```

**Create FFI bindings:**
```rust
// rust/runtime/src/compress/upx.rs (FFI section)
#[no_mangle]
pub extern "C" fn upx_compress_file(input: *const c_char, output: *const c_char, level: i32) -> i32
#[no_mangle]
pub extern "C" fn upx_decompress_file(input: *const c_char, output: *const c_char) -> i32
#[no_mangle]
pub extern "C" fn upx_is_compressed(file: *const c_char) -> i32
```

### 2.3 Simple API Wrapper

**Location:** `src/std/compress/upx.spl`

```simple
# src/std/compress/upx.spl

## Compress a binary file using UPX
##
## Examples:
##   upx.compress("myapp", "myapp.upx", level: "best")
##   upx.compress("myapp", level: "ultra-brute")  # In-place
fn compress(input: text, output: text? = None, level: text = "best") -> Result<text, text>:
    extern fn upx_compress_file(input: text, output: text, level: i32) -> i32

    val actual_output = output ?? input
    val level_code = match level:
        "fast": 1
        "best": 2
        "ultra-brute": 3
        _: 2  # default to best

    val result = upx_compress_file(input, actual_output, level_code)
    if result == 0:
        Ok(actual_output)
    else:
        Err("UPX compression failed")

## Decompress a UPX-compressed file
fn decompress(input: text, output: text) -> Result<text, text>:
    extern fn upx_decompress_file(input: text, output: text) -> i32

    val result = upx_decompress_file(input, output)
    if result == 0:
        Ok(output)
    else:
        Err("UPX decompression failed")

## Check if a file is UPX-compressed
fn is_compressed(file: text) -> bool:
    extern fn upx_is_compressed(file: text) -> i32
    upx_is_compressed(file) == 1

## Get compression ratio
fn get_ratio(file: text) -> f64:
    extern fn upx_get_ratio(file: text) -> f64
    upx_get_ratio(file)
```

### 2.4 Module Structure

```
rust/runtime/src/compress/
├── mod.rs           # Module exports
└── upx.rs           # UPX implementation + FFI

src/std/compress/
├── mod.spl          # Module exports
└── upx.spl          # Simple API wrapper
```

---

## Phase 3: Apply to Bootstrap Binary (15 minutes)

### 3.1 Build with build-std
```bash
cargo +nightly build --profile bootstrap -p simple-driver \
  -Z build-std=std,panic_abort \
  -Z build-std-features=panic_immediate_abort \
  --target x86_64-unknown-linux-gnu
```

### 3.2 Apply UPX
```bash
# Install UPX if not present
command -v upx || sudo apt-get install upx

# Compress bootstrap binary
upx --best --lzma \
  target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime

# Backup uncompressed
cp target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime \
   target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime.uncompressed
```

### 3.3 Verify
```bash
# Check size
ls -lh target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime*

# Test functionality
./target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime --version
./target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime -c 'print "test"'
```

---

## Phase 4: Create Build Script (15 minutes)

### 4.1 Makefile Target

**Add to `Makefile`:**
```makefile
# Build minimal bootstrap compiler (build-std + UPX)
.PHONY: bootstrap-minimal
bootstrap-minimal:
	@echo "Building minimal bootstrap compiler..."
	@command -v upx >/dev/null || (echo "Error: UPX not installed. Run: sudo apt-get install upx" && exit 1)
	rustup component add rust-src --toolchain nightly 2>/dev/null || true
	cd rust && cargo +nightly build --profile bootstrap -p simple-driver \
		-Z build-std=std,panic_abort \
		-Z build-std-features=panic_immediate_abort \
		--target x86_64-unknown-linux-gnu
	@echo "Compressing with UPX..."
	cp target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime \
	   target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime.uncompressed
	upx --best --lzma target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime
	@echo "Done! Binary size:"
	@ls -lh target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime
```

### 4.2 Shell Script

**Create `bin/build-minimal-bootstrap.sh`:**
```bash
#!/bin/bash
set -e

echo "Building minimal bootstrap compiler..."

# Check for UPX
if ! command -v upx &> /dev/null; then
    echo "Error: UPX not installed"
    echo "Install with: sudo apt-get install upx"
    exit 1
fi

# Check for nightly + rust-src
if ! rustup toolchain list | grep -q nightly; then
    echo "Installing nightly toolchain..."
    rustup toolchain install nightly
fi

rustup component add rust-src --toolchain nightly 2>/dev/null || true

# Build with build-std
echo "Building with build-std optimizations..."
cd rust
cargo +nightly build --profile bootstrap -p simple-driver \
    -Z build-std=std,panic_abort \
    -Z build-std-features=panic_immediate_abort \
    --target x86_64-unknown-linux-gnu

# Backup uncompressed
BINARY="target/x86_64-unknown-linux-gnu/bootstrap/simple_runtime"
echo "Backing up uncompressed binary..."
cp "$BINARY" "$BINARY.uncompressed"

# Compress with UPX
echo "Compressing with UPX..."
upx --best --lzma "$BINARY"

# Report
echo ""
echo "Build complete!"
echo "Uncompressed: $(du -h "$BINARY.uncompressed" | cut -f1)"
echo "Compressed:   $(du -h "$BINARY" | cut -f1)"
echo ""
echo "Binary location: $BINARY"
```

---

## Phase 5: Documentation & Testing (15 minutes)

### 5.1 Update Documentation

**Files to update:**
- `doc/report/binary_size_reduction_completion_2026-01-31.md`
- `doc/research/bootstrap_size_optimization_research_2026-01-31.md`
- `CLAUDE.md` - Add build-std + UPX instructions
- `README.md` - Update build commands

### 5.2 Test Suite

**Create `tests/compress_spec.spl`:**
```simple
# Test UPX compression library

describe "upx module":
    it "compresses binary files":
        val result = upx.compress("test_binary", "test_binary.upx", level: "best")
        assert result.is_ok()

    it "decompresses files":
        val result = upx.decompress("test_binary.upx", "test_binary.restored")
        assert result.is_ok()

    it "detects compressed files":
        assert upx.is_compressed("test_binary.upx")
        assert not upx.is_compressed("test_binary")

    it "reports compression ratio":
        val ratio = upx.get_ratio("test_binary.upx")
        assert ratio > 1.3  # At least 30% compression
```

---

## Implementation Checklist

### Phase 1: Build-std Setup
- [ ] Install nightly toolchain
- [ ] Install rust-src component
- [ ] Create `.cargo/config.toml`
- [ ] Update `rust/Cargo.toml` with documentation
- [ ] Build with build-std
- [ ] Verify size reduction (7-8 MB)

### Phase 2: UPX Library
- [ ] Create `rust/runtime/src/compress/` module
- [ ] Implement `upx.rs` with Rust API
- [ ] Add FFI bindings for Simple
- [ ] Create `src/std/compress/upx.spl`
- [ ] Add module exports
- [ ] Test UPX library functionality

### Phase 3: Apply to Bootstrap
- [ ] Install UPX if needed
- [ ] Build with build-std
- [ ] Compress with UPX
- [ ] Verify final size (~3.5-4 MB)
- [ ] Test functionality

### Phase 4: Build Scripts
- [ ] Add Makefile target
- [ ] Create shell script
- [ ] Make script executable
- [ ] Test build script

### Phase 5: Documentation
- [ ] Update completion report
- [ ] Update CLAUDE.md
- [ ] Create test spec
- [ ] Run tests

---

## Expected Results

| Stage | Size | Method |
|-------|------|--------|
| Current bootstrap | 9.4 MB | opt-level="z" |
| + build-std | 7-8 MB | Stdlib optimization |
| + UPX | **3.5-4 MB** | Compression |

**Total reduction:** 40 MB → 3.5 MB (91.3% reduction)

---

## Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| Nightly instability | Medium | Pin nightly version in docs |
| UPX not available | Low | Check in build script, provide install instructions |
| build-std breaks | Medium | Keep fallback to stable bootstrap profile |
| UPX detection as malware | Low | Document, provide uncompressed option |
| Startup delay | Low | Acceptable trade-off for size |

---

## Rollback Plan

If issues arise:

1. **build-std issues:** Use regular `cargo build --profile bootstrap`
2. **UPX issues:** Use uncompressed binary (`.uncompressed` backup)
3. **Both fail:** Revert to `release-opt` profile (15 MB)

---

## Timeline

- Phase 1: 30 minutes (build-std setup)
- Phase 2: 45 minutes (UPX library)
- Phase 3: 15 minutes (apply optimizations)
- Phase 4: 15 minutes (build scripts)
- Phase 5: 15 minutes (documentation)

**Total:** ~2 hours

---

## Success Criteria

- ✅ Bootstrap binary is 3.5-4 MB (91% reduction from 40 MB)
- ✅ Binary works correctly (version, run code, tests)
- ✅ UPX library available in Simple (`upx.compress()`)
- ✅ Build scripts work end-to-end
- ✅ Documentation updated
- ✅ Tests pass

# FreeBSD Testing in QEMU — Quick Guide

Run basic Simple language tests in FreeBSD QEMU VM to verify cross-platform compatibility.

## Quick Start

```bash
# Option 1: Full test (build + test)
./scripts/test-freebsd-qemu-basic.sh

# Option 2: Core tests only (faster)
./scripts/test-freebsd-qemu-basic.sh --core-only

# Option 3: Skip rebuild (if already built)
./scripts/test-freebsd-qemu-basic.sh --skip-build

# Option 4: Verbose output
./scripts/test-freebsd-qemu-basic.sh --verbose
```

## What Gets Tested

### Default Mode (Basic Test Suite)

Tests core functionality + essential stdlib:

**Core Tests (~50 tests):**
- `test/unit/core/tokens_spec.spl` - Token recognition
- `test/unit/core/types_spec.spl` - Type system
- `test/unit/core/lexer_spec.spl` - Lexical analysis
- `test/unit/core/parser_spec.spl` - Syntax parsing
- `test/unit/core/ast_spec.spl` - AST operations

**Stdlib Tests (~30 tests):**
- `test/unit/std/string_spec.spl` - String operations
- `test/unit/std/array_spec.spl` - Array operations
- `test/unit/std/math_spec.spl` - Math functions
- `test/unit/std/path_spec.spl` - Path utilities

**Total: ~80-100 tests** (runs in 30-60 seconds)

### Core-Only Mode (--core-only)

Tests only core compiler functionality:
- Lexer, parser, AST, types, tokens

**Total: ~50 tests** (runs in 15-30 seconds)

## Expected Results

### Successful Test Run

```
[test-freebsd-basic] ================================================================
[test-freebsd-basic] Test Results Summary
[test-freebsd-basic] ================================================================
[test-freebsd-basic] Total:  87 tests
[test-freebsd-basic] Passed: 87 tests (100%)
[test-freebsd-basic] Failed: 0 tests

✓ All tests passed! ✓
```

### Partial Failure

```
[test-freebsd-basic] Total:  87 tests
[test-freebsd-basic] Passed: 85 tests (97%)
[test-freebsd-basic] Failed: 2 tests

⚠ Some tests failed
Run with --verbose to see detailed output
```

## Timing Breakdown

**First run (with build):**
1. VM start: 30-60 seconds
2. Project sync: 10-20 seconds
3. Bootstrap: 3-6 minutes (KVM) or 30-60 minutes (TCG)
4. Test run: 30-60 seconds
5. **Total: 5-8 minutes (KVM)** or 35-65 minutes (TCG)

**Subsequent runs (--skip-build):**
1. VM check: 1-2 seconds (if running)
2. Project sync: 10-20 seconds
3. Test run: 30-60 seconds
4. **Total: 45-90 seconds**

## Step-by-Step Process

### Step 1: VM Check

Script checks if FreeBSD VM is running:
- If running: Connect via SSH
- If not: Start QEMU VM, wait for SSH (60s timeout)

### Step 2: Project Sync

Rsync project files to VM:
- Excludes: `.git`, `build/`, `.jj/`, `target/`, `*.o`, `*.a`
- Syncs all `.spl` source files
- Typical transfer: 10-20 seconds

### Step 3: Build Compiler

Bootstrap Simple compiler in FreeBSD:
- Uses `scripts/bootstrap-from-scratch-freebsd.sh`
- CMake + Clang 19+ + C++20
- Skipped if `--skip-build` flag used
- Verifies binary is FreeBSD ELF

### Step 4: Run Tests

Execute test suite in VM:
- Runs `bin/simple test <path>` for each test file
- Parses output to count passed/failed
- Shows progress per test file
- Summarizes results

### Step 5: Retrieve Binary

Download compiled binary from VM:
- Saves as `bin/simple.freebsd` (to avoid overwriting Linux binary)
- Can be tested in QEMU with SSH commands

## Usage Examples

### Example 1: First Time Test

```bash
# Download FreeBSD VM first (if not already done)
./scripts/test-freebsd-qemu-setup.sh --download

# Run full test suite
./scripts/test-freebsd-qemu-basic.sh

# Expected output:
# [test-freebsd-basic] Step 1: Checking FreeBSD VM
# ✓ FreeBSD VM is running on port 2222
# ✓ FreeBSD version: 14.3-RELEASE
#
# [test-freebsd-basic] Step 2: Syncing project files to VM
# ✓ Project files synced to VM
# ✓ Found 604 .spl files in VM
#
# [test-freebsd-basic] Step 3: Building Simple compiler
# [bootstrap] Step 1: Building seed C++ transpiler
# [bootstrap] Step 2: Transpiling compiler_core to C++
# ... (3-6 minutes of build output)
# ✓ Bootstrap completed successfully
# ✓ Binary verified: FreeBSD ELF
#
# [test-freebsd-basic] Step 4: Running basic test suite
# Found 87 tests to run
# Testing: test/unit/core/
#   ✓ 50 tests passed
# Testing: test/unit/std/string_spec.spl
#   ✓ 12 tests passed
# ... (more test output)
#
# Total:  87 tests
# Passed: 87 tests (100%)
# Failed: 0 tests
# ✓ All tests passed! ✓
```

### Example 2: Quick Retest (Skip Build)

```bash
# VM already running, compiler already built
./scripts/test-freebsd-qemu-basic.sh --skip-build

# Takes 45-90 seconds instead of 5-8 minutes
```

### Example 3: Core Tests Only

```bash
# Test just the core compiler components
./scripts/test-freebsd-qemu-basic.sh --core-only

# Runs ~50 tests in 15-30 seconds
```

### Example 4: Debug Test Failures

```bash
# Show detailed output for each test
./scripts/test-freebsd-qemu-basic.sh --verbose --core-only

# Output shows individual test cases:
# describe "Token recognition":
#   it "recognizes identifiers" ✓
#   it "recognizes integers" ✓
#   it "recognizes strings" ✓
#   ...
```

### Example 5: Manual Testing in VM

```bash
# Start VM (if not running)
./scripts/test-freebsd-qemu-basic.sh --skip-build --core-only

# SSH into VM for manual testing
ssh -p 2222 freebsd@localhost

# Inside VM:
cd ~/simple
bin/simple --version
bin/simple test test/unit/core/lexer_spec.spl
bin/simple test test/unit/std/
exit
```

## Troubleshooting

### Issue: VM Not Starting

**Symptom:** `SSH connection timeout after 60 seconds`

**Solution:**
```bash
# Check VM image exists
ls -lh build/freebsd/vm/FreeBSD-14.3-RELEASE-amd64.qcow2

# If missing, download
./scripts/test-freebsd-qemu-setup.sh --download

# Check KVM availability
ls -l /dev/kvm

# Enable KVM module
sudo modprobe kvm-intel  # Intel CPUs
sudo modprobe kvm-amd    # AMD CPUs
```

### Issue: Build Fails in VM

**Symptom:** `Bootstrap failed`

**Solution:**
```bash
# SSH into VM to debug
ssh -p 2222 freebsd@localhost

# Check disk space
df -h
# If low, see freebsd_qemu_bootstrap.md for resize instructions

# Check toolchain
clang++ --version  # Should be Clang 19+
cmake --version    # Should be 3.20+

# Run bootstrap manually with verbose output
cd ~/simple
./scripts/bootstrap-from-scratch-freebsd.sh --verbose
```

### Issue: Tests Fail

**Symptom:** `Some tests failed`

**Solution:**
```bash
# Run with verbose output to see which tests
./scripts/test-freebsd-qemu-basic.sh --skip-build --verbose

# Run specific failing test manually
ssh -p 2222 freebsd@localhost "cd ~/simple && bin/simple test test/unit/core/parser_spec.spl"

# Compare with Linux results
bin/simple test test/unit/core/parser_spec.spl
```

### Issue: Binary Not FreeBSD ELF

**Symptom:** `Binary verification failed: not FreeBSD ELF`

**Solution:**
```bash
# Check binary in VM
ssh -p 2222 freebsd@localhost "file ~/simple/bin/simple"
# Should show: ELF 64-bit LSB executable, x86-64, version 1 (FreeBSD)

# If it's Linux ELF, the bootstrap didn't run correctly
# Clean and rebuild
ssh -p 2222 freebsd@localhost "cd ~/simple && rm -rf build/bootstrap bin/simple"
./scripts/test-freebsd-qemu-basic.sh
```

### Issue: Project Sync Slow

**Symptom:** Project sync takes > 1 minute

**Solution:**
```bash
# Sync only changed files (incremental)
rsync -avz --delete -e "ssh -p 2222 -o StrictHostKeyChecking=no" \
    --exclude='.git' --exclude='build' \
    . freebsd@localhost:~/simple/

# Or clean VM workspace first
ssh -p 2222 freebsd@localhost "rm -rf ~/simple"
./scripts/test-freebsd-qemu-basic.sh
```

## Advanced Testing

### Custom Test Paths

Edit the script or run tests manually in VM:

```bash
# SSH into VM
ssh -p 2222 freebsd@localhost

# Run custom test paths
cd ~/simple
bin/simple test test/unit/app/
bin/simple test test/unit/lib/
bin/simple test test/integration/

# Run all tests (may take 15-30 minutes)
bin/simple test test/
```

### Performance Testing

```bash
# Time the test suite
time ./scripts/test-freebsd-qemu-basic.sh --skip-build --core-only

# Typical results:
# real    0m35.123s  (KVM)
# real    5m12.456s  (TCG without KVM)
```

### Parallel Testing

FreeBSD VM can run tests in parallel if Simple supports it:

```bash
ssh -p 2222 freebsd@localhost "cd ~/simple && bin/simple test --parallel=4 test/unit/core/"
```

## Integration with CI/CD

### GitHub Actions Example

```yaml
name: FreeBSD Basic Tests

on: [push, pull_request]

jobs:
  freebsd-tests:
    runs-on: ubuntu-latest
    timeout-minutes: 20

    steps:
      - uses: actions/checkout@v4

      - name: Cache FreeBSD VM
        uses: actions/cache@v4
        with:
          path: build/freebsd/vm
          key: freebsd-14.3-vm

      - name: Install QEMU
        run: sudo apt install -y qemu-system-x86 rsync

      - name: Download FreeBSD VM
        run: ./scripts/test-freebsd-qemu-setup.sh --download

      - name: Run Basic Tests
        run: ./scripts/test-freebsd-qemu-basic.sh --core-only

      - name: Upload Test Results
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: freebsd-test-results
          path: |
            bin/simple.freebsd
            test-results.txt
```

### Local CI Testing

```bash
# Simulate CI environment
docker run --rm -it --device=/dev/kvm -v $(pwd):/workspace ubuntu:22.04

# Inside container
apt update
apt install -y qemu-system-x86 rsync openssh-client wget xz-utils
cd /workspace
./scripts/test-freebsd-qemu-setup.sh --download
./scripts/test-freebsd-qemu-basic.sh --core-only
```

## Test Coverage

### What This Tests

✅ **Verified:**
- Compiler builds successfully on FreeBSD
- Binary is valid FreeBSD ELF executable
- Core compiler functionality (lexer, parser, AST, types)
- Essential stdlib functions (string, array, math, path)
- FreeBSD-specific toolchain (Clang 19+, CMake, C++20)
- Cross-platform compatibility (Linux → FreeBSD via QEMU)

### What This Doesn't Test

❌ **Not Covered:**
- Full test suite (4,000+ tests) - use `bin/simple test test/` in VM
- Performance benchmarks
- Multi-threaded execution
- Network operations
- GPU/CUDA functionality
- Package management
- Editor integrations

## Summary

**Quick Commands:**
```bash
# Full test (first time)
./scripts/test-freebsd-qemu-basic.sh

# Quick retest
./scripts/test-freebsd-qemu-basic.sh --skip-build --core-only

# Debug failures
./scripts/test-freebsd-qemu-basic.sh --verbose

# Manual testing
ssh -p 2222 freebsd@localhost "cd ~/simple && bin/simple test <path>"
```

**Expected Results:**
- 80-100 tests (default) or 50 tests (--core-only)
- 100% pass rate on FreeBSD 14.3+ with Clang 19+
- 30-60 seconds runtime (excluding build)
- FreeBSD ELF binary verified

**Next Steps:**
- Full test suite: `ssh -p 2222 freebsd@localhost "cd ~/simple && bin/simple test test/"`
- Performance testing: Compare FreeBSD vs Linux benchmarks
- CI integration: Add to GitHub Actions workflow

## References

- **Full QEMU Guide:** `doc/guide/freebsd_qemu_bootstrap.md`
- **Quick Start:** `README_FREEBSD_QEMU.md`
- **Bootstrap Script:** `scripts/bootstrap-from-scratch-freebsd.sh`
- **Setup Test:** `scripts/test-freebsd-qemu-setup.sh`
- **Basic Test:** `scripts/test-freebsd-qemu-basic.sh`

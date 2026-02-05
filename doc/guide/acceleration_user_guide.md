# Pure Simple DL Acceleration User Guide

## Overview

Pure Simple Deep Learning provides **optional PyTorch FFI acceleration** while maintaining 100% functionality without any external dependencies. This guide explains how to enable, configure, and optimize acceleration.

## Table of Contents

1. [Quick Start](#quick-start)
2. [Acceleration Modes](#acceleration-modes)
3. [Configuration](#configuration)
4. [Performance Tuning](#performance-tuning)
5. [Troubleshooting](#troubleshooting)

---

## Quick Start

### Using Pure Simple Only (Zero Dependencies)

```simple
use lib.pure.tensor (PureTensor)
use lib.pure.tensor_ops (matmul, add, relu)
use lib.pure.nn (Linear, ReLU)

# Works out of the box - no FFI needed
val model = Linear(784, 256)
val x = PureTensor.randn([32, 784])
val output = model.forward(x)
```

**No installation required!** Pure Simple DL works immediately with zero external dependencies.

### Enabling FFI Acceleration (Optional)

```simple
use lib.pure.accel (set_acceleration, AccelMode, get_stats)
use lib.pure.torch_ffi (torch_available)

# Check if PyTorch FFI is available
if torch_available():
    print "✅ PyTorch FFI available - enabling Auto acceleration"
    set_acceleration(AccelMode.Auto)
else:
    print "ℹ️  Using Pure Simple only (no FFI)"
    set_acceleration(AccelMode.PureSimple)
```

---

## Acceleration Modes

Pure Simple DL supports three acceleration modes:

### 1. PureSimple (Default)

```simple
set_acceleration(AccelMode.PureSimple)
```

**Characteristics:**
- ✅ Zero dependencies (works everywhere)
- ✅ 100% Simple language implementation
- ✅ Portable across all platforms
- ⚠️ Slower for large operations (>1M elements)

**When to use:**
- Prototyping and experimentation
- Small models (<10M parameters)
- Educational purposes
- Systems without PyTorch

### 2. PyTorchFFI (Always Use FFI)

```simple
set_acceleration(AccelMode.PyTorchFFI)
```

**Characteristics:**
- ✅ Maximum performance for all operations
- ⚠️ Requires PyTorch/LibTorch installed
- ⚠️ Overhead for small operations

**When to use:**
- Production training with large models
- GPU acceleration needed
- All operations are large (>1M elements)

### 3. Auto (Recommended for Production)

```simple
set_acceleration(AccelMode.Auto)
```

**Characteristics:**
- ✅ Automatically selects best backend per operation
- ✅ Uses Pure Simple for small operations (low overhead)
- ✅ Uses FFI for large operations (high performance)
- ✅ Transparent fallback if FFI fails

**When to use:**
- Production deployments (recommended)
- Mixed workloads (small + large operations)
- Maximum flexibility

---

## Configuration

### Setting Thresholds

Customize when Auto mode switches to FFI:

```simple
use lib.pure.accel (set_threshold)

# Default thresholds (in elements):
# - matmul: 1,000,000 (1M)
# - elementwise: 10,000,000 (10M)
# - activations: never use FFI

# Custom thresholds:
set_threshold("matmul", 500_000)      # Use FFI for matmul >500k elements
set_threshold("elementwise", 5_000_000)  # Use FFI for add/mul >5M elements
```

### Threshold Tuning Guidelines

| Operation | Default | Low-end CPU | High-end CPU | GPU Available |
|-----------|---------|-------------|--------------|---------------|
| matmul | 1M | 500k | 2M | 100k |
| elementwise | 10M | 5M | 20M | 1M |
| activations | Never | Never | Never | 10M |

**Rule of thumb:**
- Lower thresholds = more FFI usage = faster for large ops, overhead for small
- Higher thresholds = more Pure Simple = better for mixed workloads

### Checking Current Configuration

```simple
use lib.pure.accel (get_stats, get_current_mode, get_threshold)

# Current mode
val mode = get_current_mode()
print "Mode: {mode}"

# Current thresholds
val mm_threshold = get_threshold("matmul")
val ew_threshold = get_threshold("elementwise")
print "Matmul threshold: {mm_threshold}"
print "Elementwise threshold: {ew_threshold}"

# Statistics
val stats = get_stats()
print "Pure Simple calls: {stats.pure_count}"
print "FFI calls: {stats.ffi_count}"
print "Fallbacks: {stats.fallback_count}"
```

---

## Performance Tuning

### Profiling Your Workload

```simple
use lib.pure.accel (reset_stats, get_stats)

# Reset counters
reset_stats()

# Run your workload
train_model(data, epochs: 10)

# Check what was used
val stats = get_stats()
val total = stats.pure_count + stats.ffi_count
val ffi_percentage = (stats.ffi_count / total) * 100.0

print "FFI usage: {ffi_percentage:.1f}%"
print "Fallbacks: {stats.fallback_count}"

if ffi_percentage < 20:
    print "💡 Tip: Mostly using Pure Simple - this is expected for small models"
elif ffi_percentage > 80:
    print "💡 Tip: Mostly using FFI - ensure PyTorch is optimized"
else:
    print "💡 Tip: Good balance - Auto mode is working well"
```

### Optimization Checklist

**1. Operation Size Analysis**

```simple
# Log operation sizes to find bottlenecks
use lib.pure.accel (enable_logging)

enable_logging(true)  # Prints decisions: "[ACCEL] matmul 1000×1000 → FFI"

# Run workload and observe logs
train_step(batch)

enable_logging(false)
```

**2. Batch Size Tuning**

```simple
# Small batches (1-8): Pure Simple competitive
val small_batch = data[0:4]  # 4 samples
model.forward(small_batch)   # Uses Pure Simple in Auto mode

# Large batches (32+): FFI dominates
val large_batch = data[0:64]  # 64 samples
model.forward(large_batch)    # Uses FFI in Auto mode
```

**3. Model Architecture**

| Layer Type | Pure Simple Fast | FFI Fast |
|------------|------------------|----------|
| Linear (small) | ✅ Yes (<256 units) | ⚠️ Overhead |
| Linear (large) | ❌ No (>1024 units) | ✅ Yes |
| ReLU | ✅ Yes (always) | ⚠️ Overhead |
| Sigmoid | ✅ Yes (small) | ✅ Yes (large) |
| Softmax | ⚠️ OK | ✅ Yes |

**Design tip:** Use smaller hidden layers for Pure Simple, larger for FFI.

---

## Troubleshooting

### Problem: FFI Not Available

**Symptoms:**
```
⚠️  PyTorch FFI not available
Using Pure Simple only
```

**Solution:**

1. **Install PyTorch/LibTorch:**
   ```bash
   # Download LibTorch from https://pytorch.org/
   wget https://download.pytorch.org/libtorch/cpu/libtorch-cxx11-abi-shared-with-deps-2.0.0%2Bcpu.zip
   unzip libtorch-*.zip -d /usr/local/
   export LIBTORCH=/usr/local/libtorch
   ```

2. **Build FFI library:**
   ```bash
   cd build/rust/ffi_gen
   cargo build --release --features torch
   ```

3. **Copy library to path:**
   ```bash
   # Linux
   sudo cp target/release/libsimple_torch_ffi.so /usr/local/lib/
   sudo ldconfig

   # macOS
   cp target/release/libsimple_torch_ffi.dylib /usr/local/lib/

   # Windows
   copy target\release\simple_torch_ffi.dll C:\Windows\System32\
   ```

4. **Verify:**
   ```simple
   use lib.pure.torch_ffi (torch_available, torch_version)

   if torch_available():
       print "✅ FFI working: {torch_version()}"
   else:
       print "❌ FFI still not available"
   ```

### Problem: FFI Slower Than Expected

**Symptoms:**
```
FFI taking longer than Pure Simple for operations
```

**Diagnosis:**

1. **Check operation size:**
   ```simple
   val a = PureTensor.randn([10, 10])  # Only 100 elements!
   val result = matmul(a, a)  # FFI overhead >> computation time
   ```

   **Fix:** Use PureSimple mode or increase threshold:
   ```simple
   set_threshold("matmul", 10_000)  # Require 10k+ elements for FFI
   ```

2. **Check CPU vs GPU:**
   ```simple
   use lib.pure.torch_ffi (torch_cuda_available)

   if not torch_cuda_available():
       print "⚠️  Using CPU PyTorch - may be slower"
       # Consider using Pure Simple for small models
   ```

3. **Profile with stats:**
   ```simple
   reset_stats()
   train_epoch(data)
   val stats = get_stats()

   if stats.fallback_count > 0:
       print "⚠️  {stats.fallback_count} FFI fallbacks to Pure Simple"
       print "This indicates FFI errors - check logs"
   ```

### Problem: Memory Leaks with FFI

**Symptoms:**
```
Memory usage grows over time when using PyTorchFFI mode
```

**Diagnosis:**

FFI wrappers should automatically free handles, but check:

```simple
use lib.pure.torch_ffi (matmul_torch_ffi)

# ✅ CORRECT - wrapper frees handles
val result = matmul_torch_ffi(a, b)

# ❌ WRONG - direct rt_torch_* calls leak handles
val a_handle = rt_torch_from_data(a.data, a.shape)
val b_handle = rt_torch_from_data(b.data, b.shape)
val r_handle = rt_torch_matmul(a_handle, b_handle)
# Leak! Need to call rt_torch_free() for all handles
```

**Fix:** Always use high-level wrappers (matmul_torch_ffi), not raw extern functions.

### Problem: FFI Crashes

**Symptoms:**
```
Segmentation fault or "simple_runtime crashed"
```

**Common Causes:**

1. **Mismatched LibTorch version:**
   ```bash
   # Check tch crate version in Cargo.toml
   cat build/rust/ffi_gen/Cargo.toml | grep tch
   # Should match your LibTorch version (2.0, 2.1, etc.)
   ```

2. **Wrong tensor dimensions:**
   ```simple
   # ❌ Shape mismatch causes crash
   val a = PureTensor.randn([10, 20])
   val b = PureTensor.randn([30, 40])
   matmul_torch_ffi(a, b)  # CRASH: 20 != 30
   ```

   **Fix:** Enable shape checking in debug builds.

3. **FFI library not found:**
   ```bash
   # Check if library is in LD_LIBRARY_PATH
   ldd bin/simple_runtime | grep torch
   # Should show: libsimple_torch_ffi.so => /usr/local/lib/...
   ```

---

## Best Practices

### 1. Start with Pure Simple, Optimize Later

```simple
# Development: Pure Simple only (fast iteration)
set_acceleration(AccelMode.PureSimple)

# Quick prototype
val model = train_model(data, epochs: 5)

# Production: Enable Auto acceleration
set_acceleration(AccelMode.Auto)
val optimized_model = train_model(data, epochs: 100)
```

### 2. Use Auto Mode in Production

```simple
# ✅ RECOMMENDED
set_acceleration(AccelMode.Auto)

# ❌ AVOID (unless you have specific reasons)
set_acceleration(AccelMode.PyTorchFFI)  # Forces FFI for all ops
```

### 3. Profile Before Tuning

```simple
# Measure first
reset_stats()
run_workload()
val stats = get_stats()

# Only tune if needed
if stats.ffi_count == 0 and workload_is_slow:
    # Lower thresholds to use more FFI
    set_threshold("matmul", 500_000)
```

### 4. Handle FFI Unavailability Gracefully

```simple
use lib.pure.torch_ffi (torch_available)
use lib.pure.accel (set_acceleration, AccelMode)

# ✅ GOOD - works everywhere
if torch_available():
    set_acceleration(AccelMode.Auto)
else:
    set_acceleration(AccelMode.PureSimple)
    print "ℹ️  FFI not available, using Pure Simple"

# ❌ BAD - crashes if FFI unavailable
set_acceleration(AccelMode.PyTorchFFI)  # May fail
```

---

## Performance Expectations

### Pure Simple Performance Profile

| Operation | Size | Pure Simple | PyTorch FFI | Verdict |
|-----------|------|-------------|-------------|---------|
| matmul | 50×50 | ~5 ms | ~1 ms | ✅ Both fast |
| matmul | 100×100 | ~40 ms | ~2 ms | ⚠️ FFI better |
| matmul | 500×500 | ~5 sec | ~20 ms | ✅ FFI essential |
| matmul | 1000×1000 | ~40 sec | ~50 ms | ✅ FFI essential |
| add | 1000×1000 | ~2 ms | ~1 ms | ✅ Both fast |
| relu | 1000×1000 | ~1 ms | ~2 ms | ✅ Pure Simple better |

### When Pure Simple is Competitive

- ✅ Operations with <100k elements
- ✅ Element-wise ops (add, mul, relu)
- ✅ Small batch sizes (<16)
- ✅ Simple models (<1M parameters)

### When FFI is Essential

- ✅ Matrix multiplication >100×100
- ✅ Large batch sizes (>32)
- ✅ Models with >10M parameters
- ✅ GPU acceleration available

---

## Example: Complete Training Pipeline

```simple
use lib.pure.tensor (PureTensor)
use lib.pure.nn (Linear, ReLU)
use lib.pure.training (Trainer, SGD, mse_loss)
use lib.pure.accel (set_acceleration, AccelMode, get_stats, reset_stats)
use lib.pure.torch_ffi (torch_available)

# Configure acceleration
if torch_available():
    print "✅ PyTorch FFI available"
    set_acceleration(AccelMode.Auto)
else:
    print "ℹ️  Pure Simple only"
    set_acceleration(AccelMode.PureSimple)

# Build model
val model = Sequential(layers: [
    Linear(784, 256),
    ReLU(),
    Linear(256, 10)
])

# Train with automatic acceleration
reset_stats()
val optimizer = SGD(model.parameters(), lr: 0.01)
val trainer = Trainer(model, optimizer, mse_loss)
trainer.fit(train_data, epochs: 10)

# Report statistics
val stats = get_stats()
print ""
print "Acceleration Statistics:"
print "  Pure Simple: {stats.pure_count} ops"
print "  FFI: {stats.ffi_count} ops"
print "  Fallbacks: {stats.fallback_count}"
```

---

## Summary

**Key Takeaways:**

1. **Pure Simple works everywhere** - zero dependencies, 100% functionality
2. **FFI is optional** - only enable for large-scale training
3. **Auto mode is smart** - automatically picks best backend
4. **Profile first** - measure before tuning
5. **Start simple** - optimize only when needed

**Recommended Workflow:**

```
Prototype (Pure Simple) → Profile → Enable Auto → Tune Thresholds → Production
```

**Questions?** See `doc/api/pure_dl_api_reference.md` for complete API documentation.

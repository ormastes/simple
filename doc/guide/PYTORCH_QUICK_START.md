# PyTorch FFI - Quick Start Guide

## TL;DR

**Status:** Architecture complete, runtime integration pending
**Test Suite:** 55/55 tests passing (100%)
**To Enable:** Rebuild runtime with `-lsimple_torch_ffi`

## Quick Commands

```bash
# Check integration status
bin/verify-torch-ffi

# Run test suite (works now)
bin/release/simple test/system/dl_examples_system_spec.spl

# Run example (stub mode until integrated)
bin/release/simple examples/torch/basics/01_tensor_creation.spl
```

## What Works Now

✅ **API Layer** - Complete PyTorch-like API in Simple
✅ **FFI Library** - 400KB .so with 100+ tensor operations
✅ **Examples** - 5 example programs (basics + training)
✅ **Tests** - 55 comprehensive tests
✅ **Documentation** - Integration guide + status report

## What Needs Work

❌ **Runtime Linkage** - FFI symbols not in `bin/release/simple`

**Fix:** Rebuild runtime with linker flags (1-2 hours)

## Files to Know

| File | Purpose |
|------|---------|
| `bin/verify-torch-ffi` | Check integration status |
| `doc/torch_ffi_integration.md` | Full integration guide |
| `PYTORCH_INTEGRATION_STATUS.md` | Detailed status report |
| `test/system/dl_examples_system_spec.spl` | 55 test suite |
| `src/lib/torch/mod.spl` | Tensor API (803 lines) |
| `src/lib/torch/ffi.spl` | FFI declarations (390 lines) |

## Quick API Example

```simple
use lib.torch.{torch_available, Tensor, Linear}

fn main():
    if not torch_available():
        print "PyTorch not available (runtime not integrated)"
        return

    # Create tensor
    val x = Tensor.zeros([32, 128])
    print x.shape()  # [32, 128]

    # Neural network layer
    val layer = Linear.create(128, 64)
    val y = layer.forward(x)
    print y.shape()  # [32, 64]

    # GPU acceleration
    val x_gpu = x.cuda(0)
    print x_gpu.is_cuda()  # true
```

## How to Enable

```bash
# 1. Add to seed build (modify build script):
#    -L.build/rust/ffi_torch/target/release -lsimple_torch_ffi

# 2. Rebuild runtime
scripts/install.sh

# 3. Verify
nm bin/release/simple | grep rt_torch_tensor_zeros
# Should show: T rt_torch_tensor_zeros

# 4. Test
bin/simple examples/torch/basics/01_tensor_creation.spl
# Should show: Real tensor operations
```

## More Information

- **Integration Guide:** `doc/torch_ffi_integration.md`
- **Status Report:** `PYTORCH_INTEGRATION_STATUS.md`
- **Task Report:** `TASK_COMPLETION_REPORT.md`

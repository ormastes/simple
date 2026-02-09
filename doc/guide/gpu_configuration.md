# GPU Configuration Guide

## Overview

Simple supports configuring GPU devices for deep learning through a flexible configuration system. You can set the default device **locally** (per-project) or **globally** (per-user).

## Quick Start: Use 2nd GPU (CUDA:1)

### Method 1: Local Config File (Recommended)

**1. Create `dl.config.sdn` in your project directory:**

```sdn
# Deep Learning Local Configuration
dl:
  device: "cuda:1"          # 2nd GPU (0-indexed)
  dtype: "f32"              # Default data type
  backend: "torch"          # PyTorch backend
  autograd: true            # Enable gradient tracking
```

**2. Load config in your code:**

```simple
use std.src.dl.config_loader.{load_local_config}

fn main():
    load_local_config()  # Auto-loads dl.config.sdn if present
    # Your code here - will use GPU 1 by default
```

### Method 2: Programmatic Configuration

```simple
use std.src.dl.config.{dl, Device}

fn main():
    # Set 2nd GPU explicitly
    dl.device(Device.CUDA(1))

    # Your code here - will use GPU 1
```

### Method 3: Using Helper Functions

```simple
use std.src.dl.config.{cuda, dl}

fn main():
    dl.device(cuda(1))  # Set 2nd GPU
    # Your code here
```

---

## Config File Locations

Simple checks for config files in this order:

1. **Local** (highest priority): `./dl.config.sdn`
2. **User**: `~/.simple/dl.config.sdn`
3. **Defaults**: CPU, f32, PyTorch backend

This allows you to:
- Set project-specific GPU in `./dl.config.sdn` (not committed to git)
- Set user-wide default in `~/.simple/dl.config.sdn`

---

## Complete Config File Format

```sdn
# Deep Learning Configuration (SDN format)

dl:
  device: "cuda:1"          # Device: "cpu", "gpu", "cuda:0", "cuda:1", etc.
  dtype: "f32"              # Data type: "f16", "f32", "f64", "bf16"
  backend: "torch"          # Backend: "native", "torch", "cuda"
  autograd: true            # Enable automatic differentiation
  amp: false                # Automatic mixed precision
  seed: 42                  # Random seed for reproducibility

# Optional: Training-specific overrides
training:
  device: "cuda:1"
  dtype: "f32"
  batch_size: 32
  gradient_checkpointing: true

# Optional: Inference-specific overrides
inference:
  device: "cuda:1"
  dtype: "f16"              # Use half precision for faster inference
  autograd: false           # Disable gradients during inference
```

---

## Available Devices

| Device String | Description | Example Usage |
|---------------|-------------|---------------|
| `"cpu"` | CPU execution | General development, debugging |
| `"gpu"` | Default GPU (CUDA:0) | Single GPU systems |
| `"cuda:0"` | First GPU | Multi-GPU: primary GPU |
| `"cuda:1"` | Second GPU | Multi-GPU: secondary GPU |
| `"cuda:N"` | Nth GPU | Multi-GPU: specific GPU |

---

## Data Types

| DType | Size | Use Case |
|-------|------|----------|
| `"f16"` | 16-bit | Memory-constrained, inference |
| `"f32"` | 32-bit | **Default**, general training |
| `"f64"` | 64-bit | High precision, debugging |
| `"bf16"` | 16-bit | Mixed precision training |

---

## Backends

| Backend | Description | Status |
|---------|-------------|--------|
| `"native"` | Pure Simple implementation | ✅ Working (CPU-only) |
| `"torch"` | PyTorch via FFI | ⚠️ Planned (stubs exist) |
| `"cuda"` | Direct CUDA | ⚠️ Planned |

**Note:** GPU acceleration requires PyTorch FFI implementation (currently in development).

---

## Testing Your Configuration

Run the test script:

```bash
./test_gpu_config.spl
```

Or with explicit runtime:

```bash
bin/simple test_gpu_config.spl
```

Output shows:
- Loaded configuration
- Current device/dtype/backend
- Neural network test on configured device

---

## Example: Multi-GPU Training

**Project: Train on GPU 1, Validate on GPU 0**

```simple
use std.src.dl.config.{dl, cuda}
use lib.pure.nn.{Sequential, Linear, ReLU}

fn main():
    # Load base config (sets GPU 1 as default)
    load_local_config()

    # Create model (on GPU 1)
    val model = Sequential.create([
        Linear.create(784, 256, bias: true),
        ReLU.create(),
        Linear.create(256, 10, bias: true)
    ])

    # Training on GPU 1
    train(model, train_data)

    # Switch to GPU 0 for validation
    dl.device(cuda(0))
    validate(model, val_data)
```

---

## Environment Variables

You can also use environment variables (checked before config files):

```bash
export SIMPLE_DL_DEVICE="cuda:1"
export SIMPLE_DL_DTYPE="f32"
export SIMPLE_DL_BACKEND="torch"

./your_script.spl
```

---

## Common Use Cases

### Development (CPU)
```sdn
dl:
  device: "cpu"
  dtype: "f64"
  backend: "native"
```

### Single GPU Training
```sdn
dl:
  device: "cuda:0"
  dtype: "f32"
  backend: "torch"
  autograd: true
```

### Multi-GPU with 2nd GPU Default
```sdn
dl:
  device: "cuda:1"      # Use 2nd GPU
  dtype: "f32"
  backend: "torch"
  autograd: true
```

### Inference (Half Precision)
```sdn
dl:
  device: "cuda:0"
  dtype: "f16"
  backend: "torch"
  autograd: false       # No gradients needed
```

---

## API Reference

### Config Loader Functions

```simple
use std.src.dl.config_loader.{
    load_local_config,      # Auto-load from standard locations
    load_and_apply,         # Load specific file
    load_config_from_file   # Load and return config (don't apply)
}

# Auto-load (checks ./dl.config.sdn, then ~/.simple/dl.config.sdn)
load_local_config()

# Load specific file
load_and_apply("my_config.sdn")

# Load without applying
val config = load_config_from_file("my_config.sdn")
```

### DL Config API

```simple
use std.src.dl.config.{dl, Device, DType, Backend, cuda}

# Access global config
val current_device = dl.default_device
val current_dtype = dl.default_dtype

# Modify config
dl.device(Device.CUDA(1))
dl.dtype(DType.F32)
dl.backend(Backend.PyTorch)

# Helper constructors
val dev = cuda(1)           # Device.CUDA(1)
val dev = cpu()             # Device.CPU
val dev = gpu()             # Device.GPU
```

### Preset Configurations

```simple
use std.src.dl.config.{
    config_training,            # GPU + f32 + autograd
    config_inference,           # GPU + f32 + no autograd
    config_development,         # CPU + f64 + native
    config_mixed_precision,     # GPU + f16 + AMP
    config_cpu_training         # CPU + f32 + autograd
}

# Quick setup for training
config_training()

# Override device after preset
config_training()
dl.device(cuda(1))  # Use 2nd GPU instead of default
```

---

## Troubleshooting

### Config file not found
```
Failed to load config: Config file not found: dl.config.sdn
```
**Solution:** Create `dl.config.sdn` in current directory or `~/.simple/dl.config.sdn`

### GPU not available
```
Current backend: Pure Simple (CPU-only)
```
**Solution:** PyTorch FFI is not yet fully implemented. Current version uses Pure Simple backend (CPU-only). GPU support requires PyTorch FFI integration.

### Wrong GPU used
```
Expected CUDA:1, got CUDA:0
```
**Solution:**
1. Check config file has `device: "cuda:1"`
2. Ensure `load_local_config()` is called before creating models
3. Verify environment variables don't override config

---

## Implementation Status

| Feature | Status | Notes |
|---------|--------|-------|
| Device API (CPU/CUDA) | ✅ Complete | Device enum with CUDA(id) |
| Config file loading | ✅ Complete | SDN format loader |
| Local config (`./dl.config.sdn`) | ✅ Complete | Per-project config |
| User config (`~/.simple/dl.config.sdn`) | ✅ Complete | Per-user defaults |
| Pure Simple backend | ✅ Working | CPU-only (no FFI) |
| PyTorch FFI | ⚠️ Stubs only | GPU requires implementation |
| CUDA backend | ⚠️ Planned | Direct CUDA support |

---

## Next Steps

1. **Create local config:** `echo 'dl:\n  device: "cuda:1"' > dl.config.sdn`
2. **Test configuration:** `./test_gpu_config.spl`
3. **Use in your code:** Add `load_local_config()` at start of `main()`

**Files created:**
- `/home/ormastes/dev/pub/simple/dl.config.sdn` - Example config
- `/home/ormastes/dev/pub/simple/src/std/src/dl/config_loader.spl` - Config loader
- `/home/ormastes/dev/pub/simple/test_gpu_config.spl` - Test script
- `/home/ormastes/dev/pub/simple/doc/guide/gpu_configuration.md` - This guide

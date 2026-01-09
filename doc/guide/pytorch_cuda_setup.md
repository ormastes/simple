# PyTorch CUDA Setup Guide

## Current Status

✅ **CPU Mode**: Fully functional (all tests passing)
⚠️ **CUDA Mode**: Requires proper LibTorch build

## Issue Summary

Despite having:
- NVIDIA GPUs (RTX A6000, TITAN RTX) - working
- CUDA 13.0 installed - working
- Python PyTorch 2.9.1+cu130 - reports CUDA available
- Standalone LibTorch 2.5.1+cu121 - has CUDA libraries

The tch-rs Rust bindings **cannot detect CUDA**. Root cause: LibTorch builds (both Python and standalone) appear to be missing CUDA backend registration at the dispatcher level.

## Environment Switching

### CPU Mode (Default - Working)
```bash
source .envrc  # Defaults to CPU
# or explicitly:
export SIMPLE_PYTORCH_DEVICE=cpu
source .envrc
```

### CUDA Mode (Requires proper LibTorch)
```bash
export SIMPLE_PYTORCH_DEVICE=cuda
source .envrc
```

## How to Enable CUDA (Future)

### Option 1: Build LibTorch from Source with CUDA

1. Clone PyTorch repository:
```bash
git clone --recursive https://github.com/pytorch/pytorch
cd pytorch
git checkout v2.5.1
git submodule sync
git submodule update --init --recursive
```

2. Build with CUDA enabled:
```bash
export USE_CUDA=1
export CUDA_HOME=/usr/local/cuda-13.0
export TORCH_CUDA_ARCH_LIST="8.6;8.9"  # RTX A6000=8.6, TITAN RTX=7.5
python setup.py build
python setup.py install
```

3. Install to /opt/libtorch:
```bash
mkdir -p /opt/libtorch
cp -r build/lib.linux-x86_64-3.12/torch /opt/libtorch/
```

4. Update .envrc:
```bash
export LIBTORCH=/opt/libtorch
export LD_LIBRARY_PATH="$LIBTORCH/lib:$LD_LIBRARY_PATH"
```

### Option 2: Use Pre-built CUDA LibTorch (If Available)

1. Download official CUDA build:
```bash
wget https://download.pytorch.org/libtorch/cu121/libtorch-cxx11-abi-shared-with-deps-2.5.1%2Bcu121.zip
unzip libtorch-cxx11-abi-shared-with-deps-2.5.1+cu121.zip -d /opt/
```

2. Verify CUDA backend is registered:
```bash
# Should list CUDA in available backends
python3 -c "import torch; print(torch._C._dispatch_keys())"
```

3. If CUDA backend is missing, use Option 1 (build from source).

### Option 3: Conda Environment with CUDA

```bash
conda create -n pytorch-cuda python=3.12
conda activate pytorch-cuda
conda install pytorch torchvision torchaudio pytorch-cuda=12.1 -c pytorch -c nvidia
```

Then point LIBTORCH to conda's torch installation.

## Testing CUDA

After setup, rebuild and test:

```bash
# Clean rebuild
cargo clean
cargo build --features pytorch

# Test CUDA availability
cargo test -p simple-driver --test pytorch_cuda_test test_cuda_availability --features pytorch -- --nocapture
```

Expected output when working:
```
CUDA available: true
CUDA device count: 2
```

## Troubleshooting

### CUDA not detected despite installation

**Symptom**: `tch::Cuda::is_available()` returns false

**Cause**: LibTorch built without CUDA backend registration

**Solution**: Build LibTorch from source with `USE_CUDA=1` (Option 1 above)

### Version mismatch errors

**Symptom**: CUDA version mismatch warnings

**Solution**: Set `export LIBTORCH_BYPASS_VERSION_CHECK=1`

### Missing CUDA libraries

**Symptom**: `libcuda.so.1: cannot open shared object file`

**Solution**:
```bash
export LD_LIBRARY_PATH="/usr/local/cuda-13.0/lib64:$LD_LIBRARY_PATH"
ldconfig -p | grep libcuda  # Verify
```

## Current Workaround

Until CUDA is properly configured, the Simple language PyTorch integration operates in **CPU-only mode**:

- ✅ All tensor operations work
- ✅ Neural network layers work
- ✅ Training/inference work
- ⚠️ Slower than CUDA for large models
- ⚠️ Limited by CPU memory

## Device Selection in Simple Code

Once CUDA is enabled, Simple code can select devices:

```simple
import ml.torch

fn main():
    # Check CUDA availability
    if Tensor::cuda_available():
        let device = Device::CUDA(0)  # Use GPU 0
    else:
        let device = Device::CPU

    # Create tensor on selected device
    let tensor = Tensor::zeros([1000, 1000], device=device)
```

## References

- [PyTorch from source](https://github.com/pytorch/pytorch#from-source)
- [tch-rs CUDA setup](https://github.com/LaurentMazare/tch-rs#cuda-support)
- [LibTorch C++ download](https://pytorch.org/get-started/locally/)

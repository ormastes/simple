# Simple Math Quick Start Guide

**Version:** 1.0
**Prerequisites:** Simple Language, PyTorch integration
**Time:** 10 minutes

## Introduction

Simple Math brings math-first tensor programming to Simple language with intuitive syntax for matrices, tensors, and mathematical operations. This quick start guide will get you up and running with Simple Math in 10 minutes.

### What You'll Learn

- Creating matrices with grid literals
- Matrix multiplication with the @ operator
- Using math methods (clamp, where, one_hot)
- Linear algebra operations (det, inv, solve)
- FFT for signal processing

---

## Installation

Simple Math is included in Simple language (features #1910-#1969). Ensure you have PyTorch enabled:

```bash
# Build with PyTorch support
cargo build --features pytorch

# Or use the Simple interpreter
./target/debug/simple your_program.spl
```

---

## Your First Matrix

### Grid Literals

Create a 2D matrix using grid literal syntax:

```simple
import ml.torch as torch
import io

fn main():
    # Create a 2x3 matrix
    matrix = torch.tensor([[1.0, 2.0, 3.0],
                           [4.0, 5.0, 6.0]])

    io.println(f"Matrix shape: {matrix.shape()}")
    io.println(f"Matrix: {matrix}")
```

**Output:**
```
Matrix shape: [2, 3]
Matrix: [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]]
```

### With CUDA (Optional)

```simple
# Move to CUDA device
cuda_matrix = matrix.to("cuda")
io.println(f"Device: {cuda_matrix.device()}")
```

---

## Matrix Multiplication with @

The `@` operator provides intuitive matrix multiplication:

```simple
import ml.torch as torch
import io

fn main():
    # Define two 2x2 matrices
    A = torch.tensor([[1.0, 2.0],
                      [3.0, 4.0]])

    B = torch.tensor([[5.0, 6.0],
                      [7.0, 8.0]])

    # Matrix multiplication
    C = A @ B

    io.println(f"A @ B = {C}")
    # Output: [[19.0, 22.0], [43.0, 50.0]]
```

### Chaining Operations

```simple
    # Chain multiplications
    D = torch.eye(2)  # Identity matrix
    result = A @ B @ D

    # Combine with element-wise operations
    scaled = (A @ B) * 2.0
```

---

## Math Methods

### Clamp: Range Limiting

```simple
import ml.torch as torch

fn clamp_example():
    # Values outside [0, 10]
    data = torch.tensor([[-5.0, 3.0, 15.0],
                         [2.0, 20.0, 8.0]])

    # Clamp to [0, 10]
    clamped = data.clamp(0.0, 10.0)

    io.println(f"Original: {data}")
    io.println(f"Clamped:  {clamped}")
    # Output: [[0.0, 3.0, 10.0], [2.0, 10.0, 8.0]]
```

### Where: Conditional Selection

```simple
import ml.torch as torch

fn where_example():
    # Condition: select based on threshold
    values = torch.tensor([[10.0, 50.0, 30.0],
                           [70.0, 20.0, 90.0]])

    threshold = torch.tensor([[40.0]])
    cond = values.gt(threshold)

    # If > 40, use 100; otherwise use 0
    result = torch.where(cond,
                        torch.tensor([[100.0]]),
                        torch.tensor([[0.0]]))

    io.println(f"Result: {result}")
    # Output: [[0.0, 100.0, 0.0], [100.0, 0.0, 100.0]]
```

### One-Hot Encoding

```simple
import ml.torch as torch

fn one_hot_example():
    # Class indices: 0, 2, 1
    classes = torch.tensor([0, 2, 1], dtype="int64")

    # Convert to one-hot (3 classes)
    one_hot = classes.one_hot(3)

    io.println(f"Classes: {classes}")
    io.println(f"One-hot: {one_hot}")
    # Output: [[1,0,0], [0,0,1], [0,1,0]]
```

---

## Linear Algebra

### Solving a Linear System

```simple
import ml.torch as torch

fn solve_system():
    # System: 2x + y = 5
    #         x + 2y = 4

    A = torch.tensor([[2.0, 1.0],
                      [1.0, 2.0]])

    b = torch.tensor([[5.0],
                      [4.0]])

    # Solve Ax = b
    x = torch.linalg.solve(A, b)

    io.println(f"Solution: {x}")
    # Output: [[2.0], [1.0]]

    # Verify: A @ x should equal b
    check = A @ x
    io.println(f"Verification: {check}")
```

### Matrix Determinant & Inverse

```simple
import ml.torch as torch

fn matrix_properties():
    A = torch.tensor([[1.0, 2.0],
                      [3.0, 4.0]])

    # Determinant
    det = torch.linalg.det(A)
    io.println(f"det(A) = {det.item()}")  # -2.0

    # Inverse
    A_inv = torch.linalg.inv(A)
    io.println(f"A^-1 = {A_inv}")

    # Verify: A @ A^-1 = I
    I = A @ A_inv
    io.println(f"A @ A^-1 = {I}")
```

---

## FFT: Signal Processing

### Basic FFT Example

```simple
import ml.torch as torch

fn fft_example():
    # Create a signal (8 samples)
    signal = torch.tensor([[1.0, 2.0, 3.0, 4.0, 3.0, 2.0, 1.0, 0.0]])

    # Forward FFT
    freq = torch.fft.fft(signal, n=-1, dim=1, norm=0)

    io.println(f"Signal: {signal}")
    io.println(f"Frequency domain: {freq}")

    # Inverse FFT (reconstruct)
    reconstructed = torch.fft.ifft(freq, n=-1, dim=1, norm=0)

    io.println(f"Reconstructed: {reconstructed.real()}")
```

### Real FFT for Real Signals

```simple
import ml.torch as torch

fn rfft_example():
    # Real-valued signal
    signal = torch.tensor([[1.0, 2.0, 3.0, 4.0]])

    # Real FFT (half spectrum)
    freq = torch.fft.rfft(signal, n=-1, dim=1, norm=0)

    io.println(f"Signal length: {signal.shape()[1]}")
    io.println(f"Frequency bins: {freq.shape()[1]}")  # floor(4/2) + 1 = 3

    # Inverse Real FFT
    reconstructed = torch.fft.irfft(freq, n=4, dim=1, norm=0)
    io.println(f"Reconstructed: {reconstructed}")
```

---

## Complete Example: Image Processing

Here's a complete example combining multiple Simple Math features:

```simple
import ml.torch as torch
import io

fn process_image():
    io.println("=== Image Processing Pipeline ===")

    # 1. Create 4x4 image
    image = torch.tensor([[100.0, 200.0, 150.0, 180.0],
                          [120.0, 220.0, 160.0, 190.0],
                          [110.0, 210.0, 155.0, 185.0],
                          [115.0, 215.0, 165.0, 195.0]])

    io.println(f"Original image: {image.shape()}")

    # 2. Clamp bright pixels
    image_clamped = image.clamp(0.0, 180.0)
    io.println(f"After clamp: max = {image_clamped.max().item()}")

    # 3. Threshold: bright pixels → 255, dark → 0
    threshold = torch.tensor([[150.0]])
    cond = image_clamped.gt(threshold)
    binary = torch.where(cond,
                         torch.tensor([[255.0]]),
                         torch.tensor([[0.0]]))

    io.println(f"Binary image: {binary}")

    # 4. Apply 2D FFT for frequency analysis
    freq_2d = torch.fft.fftn(image, [0, 1], 2, norm=0)
    io.println(f"2D FFT complete: {freq_2d.shape()}")

    # 5. Shift zero-frequency to center
    freq_shifted = torch.fft.fftshift(freq_2d, dim=-1)
    io.println(f"Frequency spectrum centered")

    io.println("=== Processing Complete ===")

fn main():
    process_image()
```

---

## Best Practices

### 1. **Use @ for Matrix Multiplication**

```simple
# ✅ Good: Clear and concise
C = A @ B

# ❌ Avoid: Verbose
C = torch.matmul(A, B)
```

### 2. **Clamp for Range Limiting**

```simple
# ✅ Good: Explicit range
data = data.clamp(0.0, 1.0)

# ❌ Avoid: Manual clamping
data = torch.where(data.lt(0.0), torch.tensor([[0.0]]), data)
data = torch.where(data.gt(1.0), torch.tensor([[1.0]]), data)
```

### 3. **Use linalg.solve Instead of Explicit Inverse**

```simple
# ✅ Good: Numerically stable
x = torch.linalg.solve(A, b)

# ❌ Avoid: Less stable
A_inv = torch.linalg.inv(A)
x = A_inv @ b
```

### 4. **Verify Mathematical Properties**

```simple
# Always verify linear system solutions
x = torch.linalg.solve(A, b)
check = A @ x
assert check.allclose(b, rtol=1e-5)
```

---

## Common Patterns

### Pattern 1: Conditional Processing

```simple
# Threshold image
threshold = 128.0
cond = image.gt(torch.tensor([[threshold]]))
processed = torch.where(cond, image, torch.zeros_like(image))
```

### Pattern 2: Frequency Filtering

```simple
# Remove high frequencies
signal = torch.tensor([[...]])
freq = torch.fft.fft(signal, n=-1, dim=1, norm=0)

# Zero out high frequencies
# ... (modify freq) ...

filtered = torch.fft.ifft(freq, n=-1, dim=1, norm=0).real()
```

### Pattern 3: Batch Linear Systems

```simple
# Solve multiple systems at once
A = torch.tensor([[...]])  # (n, n)
B = torch.tensor([[...]])  # (n, m) - m right-hand sides
X = torch.linalg.solve(A, B)  # Solves m systems
```

---

## Next Steps

### Explore More Features

1. **Advanced FFT:** `fftn` for multi-dimensional transforms
2. **Tensor Literals:** Slice and flat modes for N-D tensors
3. **GPU Acceleration:** Move computations to CUDA
4. **Integration:** Combine with PyTorch neural networks

### Learn More

- **Specification:** `doc/spec/simple_math.md`
- **Examples:** `simple/examples/simple_math_demo.spl`
- **Tests:** `simple/std_lib/test/unit/ml/torch/`
- **API Reference:** `simple/std_lib/src/ml/torch/`

### Try These Examples

1. Implement PCA (Principal Component Analysis)
2. Build an image filter using FFT
3. Solve system of equations for physics simulation
4. Create a simple neural network layer with @ operator

---

## Troubleshooting

### Error: "Matrix multiplication (@) requires PyTorch runtime"

**Solution:** Use interpreter mode, not native compilation:
```bash
./target/debug/simple your_program.spl
```

### Error: Dimension mismatch in @ operator

**Check dimensions:**
```simple
io.println(f"A shape: {A.shape()}")  # (m, n)
io.println(f"B shape: {B.shape()}")  # (n, p) required
```

### Error: Singular matrix in linalg.inv

**Check determinant:**
```simple
det = torch.linalg.det(A)
if det.item() == 0.0:
    io.println("Matrix is singular!")
```

---

## Summary

You've learned:

✅ Creating matrices with grid/tensor syntax
✅ Matrix multiplication with `@` operator
✅ Math methods: clamp, where, one_hot
✅ Linear algebra: det, inv, solve
✅ FFT operations for signal processing
✅ Combining features for real applications

**You're ready to use Simple Math!** 🚀

For complete examples, see `simple/examples/simple_math_demo.spl`.

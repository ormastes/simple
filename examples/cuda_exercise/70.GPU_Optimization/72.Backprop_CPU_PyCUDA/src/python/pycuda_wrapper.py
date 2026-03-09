/**
 * @file pycuda_wrapper.py
 * @brief Python bindings for cpu_backprop
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

"""
PyCUDA wrapper for CPU Backpropagation

This module provides Python bindings for CPU-based backpropagation
implementations, enabling easy integration with NumPy and ML workflows.
"""

import ctypes
import numpy as np
from typing import Tuple, Optional
import os
import sys

# Load the compiled shared library
_lib_path = os.path.join(os.path.dirname(__file__), '..', '..', 'libcpu_backprop.so')
if not os.path.exists(_lib_path):
    _lib_path = 'libcpu_backprop.so'  # Try in current directory

try:
    _lib = ctypes.CDLL(_lib_path)
except OSError as e:
    print(f"Error loading library: {e}", file=sys.stderr)
    print(f"Searched path: {_lib_path}", file=sys.stderr)
    _lib = None

if _lib:
    # Define function signatures

    # cpu_forward
    _lib.cpu_forward.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.POINTER(ctypes.c_float),  # weights
        ctypes.POINTER(ctypes.c_float),  # bias
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # input_dim
        ctypes.c_int                      # output_dim
    ]
    _lib.cpu_forward.restype = None

    # cpu_backward
    _lib.cpu_backward.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # grad_input
        ctypes.POINTER(ctypes.c_float),  # grad_weights
        ctypes.POINTER(ctypes.c_float),  # grad_bias
        ctypes.POINTER(ctypes.c_float),  # grad_output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.POINTER(ctypes.c_float),  # weights
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # input_dim
        ctypes.c_int                      # output_dim
    ]
    _lib.cpu_backward.restype = None

    # cpu_forward_parallel
    _lib.cpu_forward_parallel.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.POINTER(ctypes.c_float),  # weights
        ctypes.POINTER(ctypes.c_float),  # bias
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # input_dim
        ctypes.c_int,                     # output_dim
        ctypes.c_int                      # num_threads
    ]
    _lib.cpu_forward_parallel.restype = None

    # cpu_backward_parallel
    _lib.cpu_backward_parallel.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # grad_input
        ctypes.POINTER(ctypes.c_float),  # grad_weights
        ctypes.POINTER(ctypes.c_float),  # grad_bias
        ctypes.POINTER(ctypes.c_float),  # grad_output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.POINTER(ctypes.c_float),  # weights
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # input_dim
        ctypes.c_int,                     # output_dim
        ctypes.c_int                      # num_threads
    ]
    _lib.cpu_backward_parallel.restype = None

    # cpu_relu_forward
    _lib.cpu_relu_forward.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.c_int                      # n
    ]
    _lib.cpu_relu_forward.restype = None

    # cpu_relu_backward
    _lib.cpu_relu_backward.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # grad_input
        ctypes.POINTER(ctypes.c_float),  # grad_output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.c_int                      # n
    ]
    _lib.cpu_relu_backward.restype = None

    # cpu_sigmoid_forward
    _lib.cpu_sigmoid_forward.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.c_int                      # n
    ]
    _lib.cpu_sigmoid_forward.restype = None

    # cpu_sigmoid_backward
    _lib.cpu_sigmoid_backward.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # grad_input
        ctypes.POINTER(ctypes.c_float),  # grad_output
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.c_int                      # n
    ]
    _lib.cpu_sigmoid_backward.restype = None

    # cpu_forward_backward_timed
    _lib.cpu_forward_backward_timed.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # grad_input
        ctypes.POINTER(ctypes.c_float),  # grad_weights
        ctypes.POINTER(ctypes.c_float),  # grad_bias
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.POINTER(ctypes.c_float),  # weights
        ctypes.POINTER(ctypes.c_float),  # bias
        ctypes.POINTER(ctypes.c_float),  # grad_output
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # input_dim
        ctypes.c_int,                     # output_dim
        ctypes.c_char_p                   # method
    ]
    _lib.cpu_forward_backward_timed.restype = ctypes.c_float


class CPUBackprop:
    """CPU Backpropagation with PyCUDA-compatible interface"""

    @staticmethod
    def forward(input: np.ndarray, weights: np.ndarray, bias: np.ndarray) -> np.ndarray:
        """
        Forward pass: output = input @ weights^T + bias

        Args:
            input: Input matrix [batch_size, input_dim], dtype=float32
            weights: Weight matrix [output_dim, input_dim], dtype=float32
            bias: Bias vector [output_dim], dtype=float32

        Returns:
            output: Output matrix [batch_size, output_dim], dtype=float32

        Raises:
            RuntimeError: If library not loaded
            ValueError: If dimensions are incompatible or dtype is not float32
        """
        if _lib is None:
            raise RuntimeError("CPU Backprop library not loaded")

        if input.dtype != np.float32 or weights.dtype != np.float32 or bias.dtype != np.float32:
            raise ValueError("All inputs must be float32")

        if input.ndim != 2 or weights.ndim != 2:
            raise ValueError("Input and weights must be 2D matrices")

        batch_size, input_dim = input.shape
        output_dim, input_dim2 = weights.shape

        if input_dim != input_dim2:
            raise ValueError(f"Incompatible dimensions: input[{batch_size}, {input_dim}] vs weights[{output_dim}, {input_dim2}]")

        if bias.shape[0] != output_dim:
            raise ValueError(f"Bias dimension mismatch: bias[{bias.shape[0]}] vs output_dim={output_dim}")

        output = np.zeros((batch_size, output_dim), dtype=np.float32)

        _lib.cpu_forward(
            output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            input.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            weights.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            bias.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            batch_size, input_dim, output_dim
        )

        return output

    @staticmethod
    def backward(grad_output: np.ndarray, input: np.ndarray,
                 weights: np.ndarray) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Backward pass: compute gradients for input, weights, and bias

        Args:
            grad_output: Gradient from upstream [batch_size, output_dim], dtype=float32
            input: Cached input from forward pass [batch_size, input_dim], dtype=float32
            weights: Weight matrix [output_dim, input_dim], dtype=float32

        Returns:
            (grad_input, grad_weights, grad_bias): Tuple of gradients

        Raises:
            RuntimeError: If library not loaded
            ValueError: If dimensions are incompatible or dtype is not float32
        """
        if _lib is None:
            raise RuntimeError("CPU Backprop library not loaded")

        if grad_output.dtype != np.float32 or input.dtype != np.float32 or weights.dtype != np.float32:
            raise ValueError("All inputs must be float32")

        batch_size, output_dim = grad_output.shape
        batch_size2, input_dim = input.shape

        if batch_size != batch_size2:
            raise ValueError(f"Batch size mismatch: grad_output[{batch_size}] vs input[{batch_size2}]")

        grad_input = np.zeros((batch_size, input_dim), dtype=np.float32)
        grad_weights = np.zeros_like(weights)
        grad_bias = np.zeros(output_dim, dtype=np.float32)

        _lib.cpu_backward(
            grad_input.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            grad_weights.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            grad_bias.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            grad_output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            input.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            weights.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            batch_size, input_dim, output_dim
        )

        return grad_input, grad_weights, grad_bias

    @staticmethod
    def relu_forward(input: np.ndarray) -> np.ndarray:
        """
        ReLU forward pass: output = max(0, input)

        Args:
            input: Input array, dtype=float32

        Returns:
            output: ReLU output, same shape as input
        """
        if _lib is None:
            raise RuntimeError("CPU Backprop library not loaded")

        if input.dtype != np.float32:
            raise ValueError("Input must be float32")

        output = np.zeros_like(input)
        n = input.size

        _lib.cpu_relu_forward(
            output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            input.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            n
        )

        return output

    @staticmethod
    def relu_backward(grad_output: np.ndarray, input: np.ndarray) -> np.ndarray:
        """
        ReLU backward pass: grad_input = (input > 0) ? grad_output : 0

        Args:
            grad_output: Gradient from upstream, dtype=float32
            input: Cached input from forward pass, dtype=float32

        Returns:
            grad_input: Gradient w.r.t. input
        """
        if _lib is None:
            raise RuntimeError("CPU Backprop library not loaded")

        if grad_output.dtype != np.float32 or input.dtype != np.float32:
            raise ValueError("All inputs must be float32")

        grad_input = np.zeros_like(input)
        n = input.size

        _lib.cpu_relu_backward(
            grad_input.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            grad_output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            input.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            n
        )

        return grad_input

    @staticmethod
    def sigmoid_forward(input: np.ndarray) -> np.ndarray:
        """
        Sigmoid forward pass: output = 1 / (1 + exp(-input))

        Args:
            input: Input array, dtype=float32

        Returns:
            output: Sigmoid output, same shape as input
        """
        if _lib is None:
            raise RuntimeError("CPU Backprop library not loaded")

        if input.dtype != np.float32:
            raise ValueError("Input must be float32")

        output = np.zeros_like(input)
        n = input.size

        _lib.cpu_sigmoid_forward(
            output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            input.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            n
        )

        return output

    @staticmethod
    def sigmoid_backward(grad_output: np.ndarray, output: np.ndarray) -> np.ndarray:
        """
        Sigmoid backward pass: grad_input = grad_output * output * (1 - output)

        Args:
            grad_output: Gradient from upstream, dtype=float32
            output: Cached sigmoid output from forward pass, dtype=float32

        Returns:
            grad_input: Gradient w.r.t. input
        """
        if _lib is None:
            raise RuntimeError("CPU Backprop library not loaded")

        if grad_output.dtype != np.float32 or output.dtype != np.float32:
            raise ValueError("All inputs must be float32")

        grad_input = np.zeros_like(output)
        n = output.size

        _lib.cpu_sigmoid_backward(
            grad_input.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            grad_output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            n
        )

        return grad_input


def validate_against_numpy(batch_size: int, input_dim: int, output_dim: int,
                           impl: str = 'naive') -> Tuple[bool, float]:
    """
    Validate CPU Backprop forward pass against NumPy

    Args:
        batch_size: Number of samples in the batch
        input_dim: Number of input features
        output_dim: Number of output features
        impl: Implementation to test ('naive' or 'parallel')

    Returns:
        (is_correct, max_error): Validation result and maximum error
    """
    np.random.seed(42)
    input_data = np.random.randn(batch_size, input_dim).astype(np.float32)
    weights = np.random.randn(output_dim, input_dim).astype(np.float32)
    bias = np.random.randn(output_dim).astype(np.float32)

    # NumPy reference: output = input @ weights^T + bias
    output_numpy = input_data @ weights.T + bias

    # Our implementation
    output_cpu = CPUBackprop.forward(input_data, weights, bias)

    max_error = np.max(np.abs(output_numpy - output_cpu))
    is_correct = max_error < 1e-4

    return is_correct, float(max_error)


def benchmark(batch_size: int, input_dim: int, output_dim: int,
              impl: str = 'naive', warmup: int = 3, runs: int = 10) -> Tuple[float, float]:
    """
    Benchmark backpropagation performance

    Args:
        batch_size, input_dim, output_dim: Layer dimensions
        impl: Implementation to benchmark ('naive' or 'parallel')
        warmup: Number of warmup runs
        runs: Number of benchmark runs

    Returns:
        (gflops, time_ms): Performance in GFLOPS and average time in ms
    """
    import time

    input_data = np.random.randn(batch_size, input_dim).astype(np.float32)
    weights = np.random.randn(output_dim, input_dim).astype(np.float32)
    bias = np.random.randn(output_dim).astype(np.float32)
    grad_output = np.random.randn(batch_size, output_dim).astype(np.float32)

    # Warmup
    for _ in range(warmup):
        _ = CPUBackprop.forward(input_data, weights, bias)
        _ = CPUBackprop.backward(grad_output, input_data, weights)

    # Benchmark
    times = []
    for _ in range(runs):
        start = time.perf_counter()

        output = CPUBackprop.forward(input_data, weights, bias)
        grads = CPUBackprop.backward(grad_output, input_data, weights)

        end = time.perf_counter()
        times.append(end - start)

    avg_time = np.mean(times)

    # Forward: 2*B*I*O (matmul) + B*O (bias add)
    # Backward: 2*B*I*O (grad_input) + 2*B*I*O (grad_weights) + B*O (grad_bias)
    total_flops = 2 * batch_size * input_dim * output_dim + batch_size * output_dim  # forward
    total_flops += 4 * batch_size * input_dim * output_dim + batch_size * output_dim  # backward
    gflops = (total_flops / avg_time) / 1e9

    return gflops, avg_time * 1000  # Return time in ms


if __name__ == "__main__":
    # Example usage
    print("CPU Backprop PyCUDA Wrapper")
    print("=" * 50)

    # Test correctness
    for impl in ['naive']:
        is_correct, max_err = validate_against_numpy(32, 128, 64, impl)
        status = "PASSED" if is_correct else "FAILED"
        print(f"{impl:10s}: {status} (max_error={max_err:.2e})")

    print()

    # Benchmark
    print("Performance Benchmark:")
    configs = [
        (32, 128, 64),
        (64, 256, 128),
        (128, 512, 256),
    ]

    for batch, in_f, out_f in configs:
        print(f"\nLayer: batch={batch}, in={in_f}, out={out_f}")
        for impl in ['naive']:
            gflops, time_ms = benchmark(batch, in_f, out_f, impl)
            print(f"  {impl:10s}: {gflops:6.2f} GFLOPS ({time_ms:7.2f} ms)")

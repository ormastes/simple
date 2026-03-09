/**
 * @file pycuda_wrapper.py
 * @brief Python bindings for CPU attention mechanisms
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

"""
PyCUDA wrapper for CPU Attention Mechanisms

This module provides Python bindings for CPU-based attention implementations,
enabling easy integration with NumPy and ML workflows for transformer models.
"""

import ctypes
import numpy as np
from typing import Tuple, Optional
import os
import sys

# Load the compiled shared library
_lib_path = os.path.join(os.path.dirname(__file__), '..', '..', 'libcpu_attention.so')
if not os.path.exists(_lib_path):
    _lib_path = 'libcpu_attention.so'  # Try in current directory

try:
    _lib = ctypes.CDLL(_lib_path)
except OSError as e:
    print(f"Error loading library: {e}", file=sys.stderr)
    print(f"Searched path: {_lib_path}", file=sys.stderr)
    _lib = None

if _lib:
    # ---- Define function signatures ----

    # cpu_sdpa_naive(output, Q, K, V, seq_len, d_model)
    _lib.cpu_sdpa_naive.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # Q
        ctypes.POINTER(ctypes.c_float),  # K
        ctypes.POINTER(ctypes.c_float),  # V
        ctypes.c_int,                     # seq_len
        ctypes.c_int                      # d_model
    ]
    _lib.cpu_sdpa_naive.restype = None

    # cpu_sdpa_causal(output, Q, K, V, seq_len, d_model)
    _lib.cpu_sdpa_causal.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # Q
        ctypes.POINTER(ctypes.c_float),  # K
        ctypes.POINTER(ctypes.c_float),  # V
        ctypes.c_int,                     # seq_len
        ctypes.c_int                      # d_model
    ]
    _lib.cpu_sdpa_causal.restype = None

    # cpu_multi_head_attention(output, Q, K, V, W_O, batch_size, seq_len, d_model, num_heads)
    _lib.cpu_multi_head_attention.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # Q
        ctypes.POINTER(ctypes.c_float),  # K
        ctypes.POINTER(ctypes.c_float),  # V
        ctypes.POINTER(ctypes.c_float),  # W_O
        ctypes.c_int,                     # batch_size
        ctypes.c_int,                     # seq_len
        ctypes.c_int,                     # d_model
        ctypes.c_int                      # num_heads
    ]
    _lib.cpu_multi_head_attention.restype = None

    # cpu_sdpa_parallel(output, Q, K, V, seq_len, d_model, num_threads)
    _lib.cpu_sdpa_parallel.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # Q
        ctypes.POINTER(ctypes.c_float),  # K
        ctypes.POINTER(ctypes.c_float),  # V
        ctypes.c_int,                     # seq_len
        ctypes.c_int,                     # d_model
        ctypes.c_int                      # num_threads
    ]
    _lib.cpu_sdpa_parallel.restype = None

    # cpu_softmax(output, input, rows, cols)
    _lib.cpu_softmax.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # input
        ctypes.c_int,                     # rows
        ctypes.c_int                      # cols
    ]
    _lib.cpu_softmax.restype = None

    # cpu_attention_timed(output, Q, K, V, seq_len, d_model, method)
    _lib.cpu_attention_timed.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # output
        ctypes.POINTER(ctypes.c_float),  # Q
        ctypes.POINTER(ctypes.c_float),  # K
        ctypes.POINTER(ctypes.c_float),  # V
        ctypes.c_int,                     # seq_len
        ctypes.c_int,                     # d_model
        ctypes.c_char_p                   # method
    ]
    _lib.cpu_attention_timed.restype = ctypes.c_float


class CPUAttention:
    """CPU Attention Mechanisms with PyCUDA-compatible interface"""

    @staticmethod
    def sdpa(Q: np.ndarray, K: np.ndarray, V: np.ndarray) -> np.ndarray:
        """
        Scaled dot-product attention: softmax(Q*K^T / sqrt(d_k)) * V

        Args:
            Q: Query matrix [seq_len, d_model], dtype=float32
            K: Key matrix [seq_len, d_model], dtype=float32
            V: Value matrix [seq_len, d_model], dtype=float32

        Returns:
            output: [seq_len, d_model], dtype=float32

        Raises:
            RuntimeError: If the shared library is not loaded
            ValueError: If dimensions are incompatible or dtype is not float32
        """
        if _lib is None:
            raise RuntimeError("CPU Attention library not loaded")

        if Q.dtype != np.float32 or K.dtype != np.float32 or V.dtype != np.float32:
            raise ValueError("Input matrices must be float32")

        if Q.ndim != 2 or K.ndim != 2 or V.ndim != 2:
            raise ValueError("Inputs must be 2D matrices [seq_len, d_model]")

        seq_len, d_model = Q.shape
        if K.shape != (seq_len, d_model) or V.shape != (seq_len, d_model):
            raise ValueError(f"Shape mismatch: Q{Q.shape}, K{K.shape}, V{V.shape}")

        output = np.zeros((seq_len, d_model), dtype=np.float32)

        _lib.cpu_sdpa_naive(
            output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            Q.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            K.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            V.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            seq_len, d_model
        )

        return output

    @staticmethod
    def sdpa_causal(Q: np.ndarray, K: np.ndarray, V: np.ndarray) -> np.ndarray:
        """
        Causal (masked) scaled dot-product attention

        Each position can only attend to current and past positions.
        Future positions are masked to -inf before softmax.

        Args:
            Q: Query matrix [seq_len, d_model], dtype=float32
            K: Key matrix [seq_len, d_model], dtype=float32
            V: Value matrix [seq_len, d_model], dtype=float32

        Returns:
            output: [seq_len, d_model], dtype=float32
        """
        if _lib is None:
            raise RuntimeError("CPU Attention library not loaded")

        if Q.dtype != np.float32 or K.dtype != np.float32 or V.dtype != np.float32:
            raise ValueError("Input matrices must be float32")

        if Q.ndim != 2 or K.ndim != 2 or V.ndim != 2:
            raise ValueError("Inputs must be 2D matrices [seq_len, d_model]")

        seq_len, d_model = Q.shape
        if K.shape != (seq_len, d_model) or V.shape != (seq_len, d_model):
            raise ValueError(f"Shape mismatch: Q{Q.shape}, K{K.shape}, V{V.shape}")

        output = np.zeros((seq_len, d_model), dtype=np.float32)

        _lib.cpu_sdpa_causal(
            output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            Q.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            K.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            V.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            seq_len, d_model
        )

        return output

    @staticmethod
    def multi_head(Q: np.ndarray, K: np.ndarray, V: np.ndarray,
                   W_O: np.ndarray, num_heads: int) -> np.ndarray:
        """
        Multi-head attention with output projection

        Splits Q, K, V into num_heads heads, runs SDPA per head,
        concatenates results, and projects with W_O.

        Args:
            Q: Query matrix [batch_size, seq_len, d_model], dtype=float32
            K: Key matrix [batch_size, seq_len, d_model], dtype=float32
            V: Value matrix [batch_size, seq_len, d_model], dtype=float32
            W_O: Output projection weight [d_model, d_model], dtype=float32
            num_heads: Number of attention heads

        Returns:
            output: [batch_size, seq_len, d_model], dtype=float32
        """
        if _lib is None:
            raise RuntimeError("CPU Attention library not loaded")

        for name, arr in [("Q", Q), ("K", K), ("V", V), ("W_O", W_O)]:
            if arr.dtype != np.float32:
                raise ValueError(f"{name} must be float32")

        if Q.ndim != 3 or K.ndim != 3 or V.ndim != 3:
            raise ValueError("Q, K, V must be 3D [batch_size, seq_len, d_model]")

        batch_size, seq_len, d_model = Q.shape
        if K.shape != Q.shape or V.shape != Q.shape:
            raise ValueError(f"Shape mismatch: Q{Q.shape}, K{K.shape}, V{V.shape}")

        if W_O.shape != (d_model, d_model):
            raise ValueError(f"W_O must be [{d_model}, {d_model}], got {W_O.shape}")

        if d_model % num_heads != 0:
            raise ValueError(f"d_model ({d_model}) must be divisible by num_heads ({num_heads})")

        output = np.zeros_like(Q)

        _lib.cpu_multi_head_attention(
            output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            Q.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            K.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            V.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            W_O.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            batch_size, seq_len, d_model, num_heads
        )

        return output

    @staticmethod
    def softmax(input: np.ndarray) -> np.ndarray:
        """
        Numerically stable softmax over rows

        Args:
            input: Input matrix [rows, cols], dtype=float32

        Returns:
            output: [rows, cols], each row sums to 1.0
        """
        if _lib is None:
            raise RuntimeError("CPU Attention library not loaded")

        if input.dtype != np.float32:
            raise ValueError("Input must be float32")

        if input.ndim != 2:
            raise ValueError("Input must be 2D matrix [rows, cols]")

        rows, cols = input.shape
        output = np.zeros_like(input)

        _lib.cpu_softmax(
            output.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            input.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            rows, cols
        )

        return output


def validate_against_numpy(Q: np.ndarray, K: np.ndarray, V: np.ndarray,
                           impl: str = 'naive') -> Tuple[bool, float]:
    """
    Validate CPU Attention against NumPy reference

    Args:
        Q: Query matrix [seq_len, d_model]
        K: Key matrix [seq_len, d_model]
        V: Value matrix [seq_len, d_model]
        impl: Implementation to test ('naive', 'causal')

    Returns:
        (is_correct, max_error): Validation result and maximum error
    """
    seq_len, d_model = Q.shape
    scale = 1.0 / np.sqrt(d_model)

    # NumPy reference: softmax(Q @ K^T * scale) @ V
    scores = (Q @ K.T) * scale

    if impl == 'causal':
        mask = np.triu(np.ones((seq_len, seq_len), dtype=np.float32) * (-np.inf), k=1)
        scores = scores + mask

    # Numerically stable softmax
    scores_max = np.max(scores, axis=-1, keepdims=True)
    scores_exp = np.exp(scores - scores_max)
    attn_weights = scores_exp / np.sum(scores_exp, axis=-1, keepdims=True)
    ref_output = attn_weights @ V

    if impl == 'naive':
        cpu_output = CPUAttention.sdpa(Q, K, V)
    elif impl == 'causal':
        cpu_output = CPUAttention.sdpa_causal(Q, K, V)
    else:
        raise ValueError(f"Unknown implementation: {impl}")

    max_error = np.max(np.abs(ref_output - cpu_output))
    is_correct = max_error < 1e-4

    return is_correct, float(max_error)


def benchmark(seq_len: int, d_model: int, impl: str = 'naive',
             warmup: int = 3, runs: int = 10) -> Tuple[float, float]:
    """
    Benchmark attention performance

    Args:
        seq_len: Sequence length
        d_model: Model dimension
        impl: Implementation to benchmark ('naive', 'causal')
        warmup: Number of warmup runs
        runs: Number of benchmark runs

    Returns:
        (gflops, time_ms): Performance in GFLOPS and average time
    """
    import time

    Q = np.random.randn(seq_len, d_model).astype(np.float32)
    K = np.random.randn(seq_len, d_model).astype(np.float32)
    V = np.random.randn(seq_len, d_model).astype(np.float32)

    # Warmup
    for _ in range(warmup):
        if impl == 'naive':
            _ = CPUAttention.sdpa(Q, K, V)
        elif impl == 'causal':
            _ = CPUAttention.sdpa_causal(Q, K, V)

    # Benchmark
    times = []
    for _ in range(runs):
        start = time.perf_counter()

        if impl == 'naive':
            _ = CPUAttention.sdpa(Q, K, V)
        elif impl == 'causal':
            _ = CPUAttention.sdpa_causal(Q, K, V)

        end = time.perf_counter()
        times.append(end - start)

    avg_time = np.mean(times)

    # FLOPS: QK^T = 2*L*L*D, softmax ~ 5*L*L, attn@V = 2*L*L*D
    # Total ~ 4*L*L*D + 5*L*L
    flops = 4 * seq_len * seq_len * d_model + 5 * seq_len * seq_len
    gflops = (flops / avg_time) / 1e9

    return gflops, avg_time * 1000  # Return time in ms


if __name__ == "__main__":
    # Example usage
    print("CPU Attention PyCUDA Wrapper")
    print("=" * 50)

    # Test correctness
    Q = np.random.randn(64, 64).astype(np.float32)
    K = np.random.randn(64, 64).astype(np.float32)
    V = np.random.randn(64, 64).astype(np.float32)

    for impl in ['naive', 'causal']:
        is_correct, max_err = validate_against_numpy(Q, K, V, impl)
        status = "PASSED" if is_correct else "FAILED"
        print(f"{impl:10s}: {status} (max_error={max_err:.2e})")

    print()

    # Benchmark
    print("Performance Benchmark:")
    sizes = [(64, 64), (128, 64), (256, 64), (512, 64)]

    for seq_len, d_model in sizes:
        print(f"\nSequence length: {seq_len}, d_model: {d_model}")
        for impl in ['naive', 'causal']:
            gflops, time_ms = benchmark(seq_len, d_model, impl)
            print(f"  {impl:10s}: {gflops:6.2f} GFLOPS ({time_ms:7.2f} ms)")

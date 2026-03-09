/**
 * @file pycuda_wrapper.py
 * @brief Python bindings for pycuda_wrapper
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

"""
PyCUDA wrapper for CPU Matrix Multiplication

This module provides Python bindings for CPU-based matrix multiplication
implementations, enabling easy integration with NumPy and ML workflows.
"""

import ctypes
import numpy as np
from typing import Tuple, Optional
import os
import sys

# Load the compiled shared library
_lib_path = os.path.join(os.path.dirname(__file__), '..', '..', 'libcpu_matmul.so')
if not os.path.exists(_lib_path):
    _lib_path = 'libcpu_matmul.so'  # Try in current directory

try:
    _lib = ctypes.CDLL(_lib_path)
except OSError as e:
    print(f"Error loading library: {e}", file=sys.stderr)
    print(f"Searched path: {_lib_path}", file=sys.stderr)
    _lib = None

if _lib:
    # Define function signatures
    _lib.cpu_matmul_naive.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # C
        ctypes.POINTER(ctypes.c_float),  # A
        ctypes.POINTER(ctypes.c_float),  # B
        ctypes.c_int,                     # M
        ctypes.c_int,                     # N
        ctypes.c_int                      # K
    ]
    _lib.cpu_matmul_naive.restype = None

    _lib.cpu_matmul_tiled.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # C
        ctypes.POINTER(ctypes.c_float),  # A
        ctypes.POINTER(ctypes.c_float),  # B
        ctypes.c_int,                     # M
        ctypes.c_int,                     # N
        ctypes.c_int,                     # K
        ctypes.c_int                      # tile_size
    ]
    _lib.cpu_matmul_tiled.restype = None

    _lib.cpu_matmul_parallel.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # C
        ctypes.POINTER(ctypes.c_float),  # A
        ctypes.POINTER(ctypes.c_float),  # B
        ctypes.c_int,                     # M
        ctypes.c_int,                     # N
        ctypes.c_int,                     # K
        ctypes.c_int                      # num_threads
    ]
    _lib.cpu_matmul_parallel.restype = None

    _lib.cpu_matmul_timed.argtypes = [
        ctypes.POINTER(ctypes.c_float),  # C
        ctypes.POINTER(ctypes.c_float),  # A
        ctypes.POINTER(ctypes.c_float),  # B
        ctypes.c_int,                     # M
        ctypes.c_int,                     # N
        ctypes.c_int,                     # K
        ctypes.c_char_p                   # method
    ]
    _lib.cpu_matmul_timed.restype = ctypes.c_float


class CPUMatMul:
    """CPU Matrix Multiplication with PyCUDA-compatible interface"""

    @staticmethod
    def naive(A: np.ndarray, B: np.ndarray) -> np.ndarray:
        """
        Naive CPU matrix multiplication: C = A @ B

        Args:
            A: Input matrix [M, K], dtype=float32
            B: Input matrix [K, N], dtype=float32

        Returns:
            C: Output matrix [M, N], dtype=float32

        Raises:
            ValueError: If dimensions are incompatible or dtype is not float32
        """
        if _lib is None:
            raise RuntimeError("CPU MatMul library not loaded")

        if A.dtype != np.float32 or B.dtype != np.float32:
            raise ValueError("Input matrices must be float32")

        if A.ndim != 2 or B.ndim != 2:
            raise ValueError("Inputs must be 2D matrices")

        M, K = A.shape
        K2, N = B.shape

        if K != K2:
            raise ValueError(f"Incompatible dimensions: A[{M}, {K}] @ B[{K2}, {N}]")

        C = np.zeros((M, N), dtype=np.float32)

        _lib.cpu_matmul_naive(
            C.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            A.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            B.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            M, N, K
        )

        return C

    @staticmethod
    def tiled(A: np.ndarray, B: np.ndarray, tile_size: int = 64) -> np.ndarray:
        """
        Cache-optimized tiled matrix multiplication: C = A @ B

        Args:
            A: Input matrix [M, K], dtype=float32
            B: Input matrix [K, N], dtype=float32
            tile_size: Block size for cache optimization (default: 64)

        Returns:
            C: Output matrix [M, N], dtype=float32
        """
        if _lib is None:
            raise RuntimeError("CPU MatMul library not loaded")

        if A.dtype != np.float32 or B.dtype != np.float32:
            raise ValueError("Input matrices must be float32")

        if A.ndim != 2 or B.ndim != 2:
            raise ValueError("Inputs must be 2D matrices")

        M, K = A.shape
        K2, N = B.shape

        if K != K2:
            raise ValueError(f"Incompatible dimensions: A[{M}, {K}] @ B[{K2}, {N}]")

        C = np.zeros((M, N), dtype=np.float32)

        _lib.cpu_matmul_tiled(
            C.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            A.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            B.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            M, N, K, tile_size
        )

        return C

    @staticmethod
    def parallel(A: np.ndarray, B: np.ndarray, num_threads: Optional[int] = None) -> np.ndarray:
        """
        Multi-threaded parallel matrix multiplication: C = A @ B

        Args:
            A: Input matrix [M, K], dtype=float32
            B: Input matrix [K, N], dtype=float32
            num_threads: Number of threads (None = use all available)

        Returns:
            C: Output matrix [M, N], dtype=float32
        """
        if _lib is None:
            raise RuntimeError("CPU MatMul library not loaded")

        if A.dtype != np.float32 or B.dtype != np.float32:
            raise ValueError("Input matrices must be float32")

        if A.ndim != 2 or B.ndim != 2:
            raise ValueError("Inputs must be 2D matrices")

        M, K = A.shape
        K2, N = B.shape

        if K != K2:
            raise ValueError(f"Incompatible dimensions: A[{M}, {K}] @ B[{K2}, {N}]")

        C = np.zeros((M, N), dtype=np.float32)

        threads = num_threads if num_threads is not None else -1

        _lib.cpu_matmul_parallel(
            C.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            A.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            B.ctypes.data_as(ctypes.POINTER(ctypes.c_float)),
            M, N, K, threads
        )

        return C


def validate_against_numpy(A: np.ndarray, B: np.ndarray, impl: str = 'naive') -> Tuple[bool, float]:
    """
    Validate CPU MatMul against NumPy

    Args:
        A: Input matrix [M, K]
        B: Input matrix [K, N]
        impl: Implementation to test ('naive', 'tiled', 'parallel')

    Returns:
        (is_correct, max_error): Validation result and maximum error
    """
    C_numpy = A @ B  # NumPy uses optimized BLAS

    if impl == 'naive':
        C_cpu = CPUMatMul.naive(A, B)
    elif impl == 'tiled':
        C_cpu = CPUMatMul.tiled(A, B)
    elif impl == 'parallel':
        C_cpu = CPUMatMul.parallel(A, B)
    else:
        raise ValueError(f"Unknown implementation: {impl}")

    max_error = np.max(np.abs(C_numpy - C_cpu))
    is_correct = max_error < 1e-4

    return is_correct, float(max_error)


def benchmark(M: int, N: int, K: int, impl: str = 'naive',
             warmup: int = 3, runs: int = 10) -> Tuple[float, float]:
    """
    Benchmark matrix multiplication performance

    Args:
        M, N, K: Matrix dimensions
        impl: Implementation to benchmark
        warmup: Number of warmup runs
        runs: Number of benchmark runs

    Returns:
        (gflops, time_ms): Performance in GFLOPS and average time
    """
    import time

    A = np.random.randn(M, K).astype(np.float32)
    B = np.random.randn(K, N).astype(np.float32)

    # Warmup
    for _ in range(warmup):
        if impl == 'naive':
            _ = CPUMatMul.naive(A, B)
        elif impl == 'tiled':
            _ = CPUMatMul.tiled(A, B)
        elif impl == 'parallel':
            _ = CPUMatMul.parallel(A, B)

    # Benchmark
    times = []
    for _ in range(runs):
        start = time.perf_counter()

        if impl == 'naive':
            C = CPUMatMul.naive(A, B)
        elif impl == 'tiled':
            C = CPUMatMul.tiled(A, B)
        elif impl == 'parallel':
            C = CPUMatMul.parallel(A, B)

        end = time.perf_counter()
        times.append(end - start)

    avg_time = np.mean(times)
    flops = 2 * M * N * K  # Matrix multiplication FLOPs
    gflops = (flops / avg_time) / 1e9

    return gflops, avg_time * 1000  # Return time in ms


if __name__ == "__main__":
    # Example usage
    print("CPU MatMul PyCUDA Wrapper")
    print("=" * 50)

    # Test correctness
    A = np.random.randn(128, 128).astype(np.float32)
    B = np.random.randn(128, 128).astype(np.float32)

    for impl in ['naive', 'tiled', 'parallel']:
        is_correct, max_err = validate_against_numpy(A, B, impl)
        status = "PASSED" if is_correct else "FAILED"
        print(f"{impl:10s}: {status} (max_error={max_err:.2e})")

    print()

    # Benchmark
    print("Performance Benchmark:")
    sizes = [(128, 128, 128), (256, 256, 256), (512, 512, 512)]

    for M, N, K in sizes:
        print(f"\nMatrix size: {M}×{N}×{K}")
        for impl in ['naive', 'tiled', 'parallel']:
            gflops, time_ms = benchmark(M, N, K, impl)
            print(f"  {impl:10s}: {gflops:6.2f} GFLOPS ({time_ms:7.2f} ms)")

#!/usr/bin/env python3
/**
 * @file benchmark.py
 * @brief Python bindings for benchmark
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

"""
Performance benchmarking for CPU Matrix Multiplication

This script benchmarks various CPU matrix multiplication implementations
and compares them against NumPy's optimized BLAS routines.
"""

import numpy as np
import time
from typing import List, Tuple
import argparse

try:
    from pycuda_wrapper import CPUMatMul, benchmark, validate_against_numpy
except ImportError:
    print("Error: Could not import pycuda_wrapper")
    print("Make sure the library is built and in the correct path")
    exit(1)


def print_table_header():
    """Print benchmark table header"""
    print(f"{'Size':>12} | {'Impl':>10} | {'Time (ms)':>12} | {'GFLOPS':>10} | {'vs NumPy':>10}")
    print("-" * 70)


def run_benchmarks(sizes: List[Tuple[int, int, int]], impls: List[str],
                   warmup: int = 3, runs: int = 10):
    """
    Run comprehensive benchmarks

    Args:
        sizes: List of (M, N, K) matrix sizes
        impls: List of implementations to test
        warmup: Number of warmup iterations
        runs: Number of benchmark iterations
    """
    print_table_header()

    for M, N, K in sizes:
        A = np.random.randn(M, K).astype(np.float32)
        B = np.random.randn(K, N).astype(np.float32)

        # Benchmark NumPy for comparison
        times = []
        for _ in range(warmup):
            _ = A @ B

        for _ in range(runs):
            start = time.perf_counter()
            C_numpy = A @ B
            end = time.perf_counter()
            times.append(end - start)

        numpy_time = np.mean(times) * 1000  # ms
        flops = 2 * M * N * K
        numpy_gflops = (flops / (numpy_time / 1000)) / 1e9

        print(f"{M:4d}×{N:4d}×{K:4d} | {'NumPy':>10} | {numpy_time:12.2f} | {numpy_gflops:10.2f} | {1.00:10.2f}x")

        # Benchmark our implementations
        for impl in impls:
            gflops, time_ms = benchmark(M, N, K, impl, warmup, runs)
            speedup = numpy_gflops / gflops

            print(f"{M:4d}×{N:4d}×{K:4d} | {impl:>10} | {time_ms:12.2f} | {gflops:10.2f} | {speedup:10.2f}x")

        print()


def validate_implementations(size: int = 128):
    """
    Validate all implementations against NumPy

    Args:
        size: Matrix size for validation
    """
    print("Validation Results")
    print("=" * 50)

    A = np.random.randn(size, size).astype(np.float32)
    B = np.random.randn(size, size).astype(np.float32)

    impls = ['naive', 'tiled', 'parallel']

    for impl in impls:
        is_correct, max_err = validate_against_numpy(A, B, impl)
        status = "✓ PASSED" if is_correct else "✗ FAILED"
        print(f"{impl:10s}: {status} (max_error={max_err:.2e})")

    print()


def main():
    parser = argparse.ArgumentParser(description='Benchmark CPU MatMul implementations')
    parser.add_argument('--validate', action='store_true',
                       help='Run validation tests')
    parser.add_argument('--small', action='store_true',
                       help='Run small benchmarks only')
    parser.add_argument('--large', action='store_true',
                       help='Run large benchmarks')
    parser.add_argument('--warmup', type=int, default=3,
                       help='Number of warmup iterations')
    parser.add_argument('--runs', type=int, default=10,
                       help='Number of benchmark iterations')

    args = parser.parse_args()

    if args.validate:
        validate_implementations()

    # Define benchmark sizes
    if args.small:
        sizes = [
            (64, 64, 64),
            (128, 128, 128),
            (256, 256, 256)
        ]
    elif args.large:
        sizes = [
            (512, 512, 512),
            (1024, 1024, 1024),
            (2048, 2048, 2048)
        ]
    else:
        sizes = [
            (128, 128, 128),
            (256, 256, 256),
            (512, 512, 512),
            (1024, 1024, 1024)
        ]

    impls = ['naive', 'tiled', 'parallel']

    print("CPU Matrix Multiplication Benchmark")
    print("=" * 70)
    print()

    run_benchmarks(sizes, impls, args.warmup, args.runs)

    print("\nNotes:")
    print("- NumPy typically uses optimized BLAS (MKL, OpenBLAS, etc.)")
    print("- Our naive implementation is expected to be slower")
    print("- Tiled implementation should show 2-3x improvement over naive")
    print("- Parallel implementation should scale with CPU cores")
    print("- GPU implementations (coming in Part 68) will be 10-100x faster")


if __name__ == "__main__":
    main()

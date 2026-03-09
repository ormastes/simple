#!/usr/bin/env python3
/**
 * @file benchmark.py
 * @brief Performance benchmarking for CPU attention mechanisms
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

"""
Performance benchmarking for CPU Attention Mechanisms

This script benchmarks various CPU attention implementations
and compares naive vs causal vs multi-head attention at different
sequence lengths.
"""

import numpy as np
import time
from typing import List, Tuple
import argparse

try:
    from pycuda_wrapper import CPUAttention, benchmark, validate_against_numpy
except ImportError:
    print("Error: Could not import pycuda_wrapper")
    print("Make sure the library is built and in the correct path")
    exit(1)


def print_table_header():
    """Print benchmark table header"""
    print(f"{'SeqLen':>8} x {'d_model':>7} | {'Impl':>10} | {'Time (ms)':>12} | {'GFLOPS':>10} | {'vs NumPy':>10}")
    print("-" * 75)


def benchmark_multi_head(batch_size: int, seq_len: int, d_model: int, num_heads: int,
                         warmup: int = 3, runs: int = 10) -> Tuple[float, float]:
    """
    Benchmark multi-head attention performance

    Args:
        batch_size: Batch size
        seq_len: Sequence length
        d_model: Model dimension
        num_heads: Number of attention heads
        warmup: Number of warmup iterations
        runs: Number of benchmark iterations

    Returns:
        (gflops, time_ms): Performance metrics
    """
    Q = np.random.randn(batch_size, seq_len, d_model).astype(np.float32)
    K = np.random.randn(batch_size, seq_len, d_model).astype(np.float32)
    V = np.random.randn(batch_size, seq_len, d_model).astype(np.float32)
    W_O = np.random.randn(d_model, d_model).astype(np.float32) * 0.02

    # Warmup
    for _ in range(warmup):
        _ = CPUAttention.multi_head(Q, K, V, W_O, num_heads)

    # Benchmark
    times = []
    for _ in range(runs):
        start = time.perf_counter()
        _ = CPUAttention.multi_head(Q, K, V, W_O, num_heads)
        end = time.perf_counter()
        times.append(end - start)

    avg_time = np.mean(times)

    # FLOPS: num_heads * (4*L*L*head_dim + 5*L*L) + batch*L*D*D (projection)
    head_dim = d_model // num_heads
    per_head_flops = 4 * seq_len * seq_len * head_dim + 5 * seq_len * seq_len
    projection_flops = 2 * batch_size * seq_len * d_model * d_model
    total_flops = batch_size * num_heads * per_head_flops + projection_flops
    gflops = (total_flops / avg_time) / 1e9

    return gflops, avg_time * 1000


def run_benchmarks(sizes: List[Tuple[int, int]], impls: List[str],
                   warmup: int = 3, runs: int = 10):
    """
    Run comprehensive benchmarks across sequence lengths and implementations

    Args:
        sizes: List of (seq_len, d_model) configurations
        impls: List of implementations to test
        warmup: Number of warmup iterations
        runs: Number of benchmark iterations
    """
    print_table_header()

    for seq_len, d_model in sizes:
        Q = np.random.randn(seq_len, d_model).astype(np.float32)
        K = np.random.randn(seq_len, d_model).astype(np.float32)
        V = np.random.randn(seq_len, d_model).astype(np.float32)

        # Benchmark NumPy for comparison
        scale = 1.0 / np.sqrt(d_model)
        times_np = []
        for _ in range(warmup):
            scores = (Q @ K.T) * scale
            scores_max = np.max(scores, axis=-1, keepdims=True)
            attn = np.exp(scores - scores_max)
            attn = attn / np.sum(attn, axis=-1, keepdims=True)
            _ = attn @ V

        for _ in range(runs):
            start = time.perf_counter()
            scores = (Q @ K.T) * scale
            scores_max = np.max(scores, axis=-1, keepdims=True)
            attn = np.exp(scores - scores_max)
            attn = attn / np.sum(attn, axis=-1, keepdims=True)
            _ = attn @ V
            end = time.perf_counter()
            times_np.append(end - start)

        numpy_time = np.mean(times_np) * 1000
        flops = 4 * seq_len * seq_len * d_model + 5 * seq_len * seq_len
        numpy_gflops = (flops / (numpy_time / 1000)) / 1e9

        print(f"{seq_len:8d} x {d_model:7d} | {'NumPy':>10} | {numpy_time:12.2f} | {numpy_gflops:10.2f} | {1.00:10.2f}x")

        # Benchmark our implementations
        for impl in impls:
            gflops, time_ms = benchmark(seq_len, d_model, impl, warmup, runs)
            ratio = numpy_time / time_ms if time_ms > 0 else 0

            print(f"{seq_len:8d} x {d_model:7d} | {impl:>10} | {time_ms:12.2f} | {gflops:10.2f} | {ratio:10.2f}x")

        print()


def run_multihead_benchmarks(warmup: int = 3, runs: int = 10):
    """
    Run multi-head attention benchmarks

    Args:
        warmup: Number of warmup iterations
        runs: Number of benchmark iterations
    """
    print("\nMulti-Head Attention Benchmarks")
    print("=" * 75)
    print(f"{'Batch':>5} x {'SeqLen':>6} x {'d_model':>7} | {'Heads':>5} | {'Time (ms)':>12} | {'GFLOPS':>10}")
    print("-" * 75)

    configs = [
        (1, 64, 64, 4),
        (1, 128, 64, 4),
        (2, 64, 64, 4),
        (2, 128, 64, 8),
        (1, 256, 128, 8),
    ]

    for batch, seq_len, d_model, num_heads in configs:
        gflops, time_ms = benchmark_multi_head(batch, seq_len, d_model, num_heads, warmup, runs)
        print(f"{batch:5d} x {seq_len:6d} x {d_model:7d} | {num_heads:5d} | {time_ms:12.2f} | {gflops:10.2f}")


def validate_implementations(size: int = 64):
    """
    Validate all implementations against NumPy reference

    Args:
        size: Sequence length for validation
    """
    print("Validation Results")
    print("=" * 50)

    Q = np.random.randn(size, size).astype(np.float32)
    K = np.random.randn(size, size).astype(np.float32)
    V = np.random.randn(size, size).astype(np.float32)

    impls = ['naive', 'causal']

    for impl in impls:
        is_correct, max_err = validate_against_numpy(Q, K, V, impl)
        status = "PASSED" if is_correct else "FAILED"
        print(f"{impl:10s}: {status} (max_error={max_err:.2e})")

    print()


def main():
    parser = argparse.ArgumentParser(description='Benchmark CPU Attention implementations')
    parser.add_argument('--validate', action='store_true',
                       help='Run validation tests')
    parser.add_argument('--small', action='store_true',
                       help='Run small benchmarks only')
    parser.add_argument('--large', action='store_true',
                       help='Run large benchmarks')
    parser.add_argument('--multihead', action='store_true',
                       help='Run multi-head attention benchmarks')
    parser.add_argument('--warmup', type=int, default=3,
                       help='Number of warmup iterations')
    parser.add_argument('--runs', type=int, default=10,
                       help='Number of benchmark iterations')

    args = parser.parse_args()

    if args.validate:
        validate_implementations()

    # Define benchmark sizes (seq_len, d_model)
    if args.small:
        sizes = [
            (32, 64),
            (64, 64),
            (128, 64)
        ]
    elif args.large:
        sizes = [
            (256, 128),
            (512, 128),
            (1024, 128)
        ]
    else:
        sizes = [
            (64, 64),
            (128, 64),
            (256, 64),
            (512, 64)
        ]

    impls = ['naive', 'causal']

    print("CPU Attention Mechanism Benchmark")
    print("=" * 75)
    print()

    run_benchmarks(sizes, impls, args.warmup, args.runs)

    if args.multihead:
        run_multihead_benchmarks(args.warmup, args.runs)

    print("\nNotes:")
    print("- Attention complexity is O(L^2 * D) where L is sequence length")
    print("- Causal attention saves ~50% compute but has same asymptotic complexity")
    print("- NumPy uses optimized BLAS for matrix operations")
    print("- GPU implementations (Part 78) will be 50-500x faster")
    print("- FlashAttention (Part 79) reduces memory from O(L^2) to O(L)")


if __name__ == "__main__":
    main()

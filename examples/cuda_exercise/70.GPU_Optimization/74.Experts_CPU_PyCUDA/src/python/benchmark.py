#!/usr/bin/env python3
/**
 * @file benchmark.py
 * @brief Performance benchmarking for CPU Mixture of Experts
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

"""
Performance benchmarking for CPU Mixture of Experts

This script benchmarks various CPU MoE configurations and compares
performance across different numbers of experts and top_k values.
"""

import numpy as np
import time
from typing import List, Tuple
import argparse

try:
    from pycuda_wrapper import CPUMoE, benchmark, validate_against_numpy
except ImportError:
    print("Error: Could not import pycuda_wrapper")
    print("Make sure the library is built and in the correct path")
    exit(1)


def print_table_header():
    """Print benchmark table header"""
    print(f"{'Config':>30} | {'Time (ms)':>12} | {'GFLOPS':>10} | {'Sparsity':>10}")
    print("-" * 75)


def run_benchmarks(configs: List[Tuple[int, int, int, int, int]],
                   warmup: int = 3, runs: int = 10):
    """
    Run comprehensive benchmarks across MoE configurations.

    Args:
        configs: List of (batch_size, d_model, d_ff, num_experts, top_k) tuples
        warmup: Number of warmup iterations
        runs: Number of benchmark iterations
    """
    print_table_header()

    for batch_size, d_model, d_ff, num_experts, top_k in configs:
        gflops, time_ms = benchmark(batch_size, d_model, d_ff,
                                    num_experts, top_k, warmup, runs)
        sparsity = 1.0 - (top_k / num_experts)

        config_str = (f"B={batch_size:3d}, D={d_model:4d}, FF={d_ff:4d}, "
                     f"E={num_experts:2d}, K={top_k}")
        print(f"{config_str:>30} | {time_ms:12.2f} | {gflops:10.2f} | {sparsity:10.1%}")

    print()


def validate_implementations(batch_size: int = 16, d_model: int = 64,
                              d_ff: int = 256, num_experts: int = 4, top_k: int = 2):
    """
    Validate MoE implementation against NumPy reference.

    Args:
        batch_size: Number of tokens
        d_model: Model dimension
        d_ff: FFN hidden dimension
        num_experts: Number of experts
        top_k: Experts per token
    """
    print("Validation Results")
    print("=" * 50)

    np.random.seed(42)
    input_data = np.random.randn(batch_size, d_model).astype(np.float32) * 0.1
    gate_weights = np.random.randn(num_experts, d_model).astype(np.float32) * 0.1
    W1 = np.random.randn(num_experts, d_ff, d_model).astype(np.float32) * 0.1
    b1 = np.random.randn(num_experts, d_ff).astype(np.float32) * 0.1
    W2 = np.random.randn(num_experts, d_model, d_ff).astype(np.float32) * 0.1
    b2 = np.random.randn(num_experts, d_model).astype(np.float32) * 0.1

    # Test various top_k values
    for tk in range(1, min(top_k + 1, num_experts + 1)):
        is_correct, max_err = validate_against_numpy(
            input_data, gate_weights, W1, b1, W2, b2, tk)
        status = "PASSED" if is_correct else "FAILED"
        print(f"top_k={tk}: {status} (max_error={max_err:.2e})")

    # Test GELU
    x = np.array([-2.0, -1.0, -0.5, 0.0, 0.5, 1.0, 2.0], dtype=np.float32)
    gelu_out = CPUMoE.gelu(x)
    # Reference GELU
    ref = 0.5 * x * (1.0 + np.tanh(0.7978845608 * (x + 0.044715 * x ** 3)))
    gelu_err = np.max(np.abs(gelu_out - ref))
    gelu_ok = gelu_err < 1e-6
    print(f"GELU:     {'PASSED' if gelu_ok else 'FAILED'} (max_error={gelu_err:.2e})")

    print()


def benchmark_scaling():
    """
    Benchmark how performance scales with number of experts.
    """
    print("Expert Scaling Benchmark")
    print("=" * 75)

    batch_size = 32
    d_model = 256
    d_ff = 1024

    # Varying num_experts with fixed top_k=2
    print("\nFixed top_k=2, varying num_experts:")
    print_table_header()

    for num_experts in [4, 8, 16]:
        gflops, time_ms = benchmark(batch_size, d_model, d_ff, num_experts, 2)
        sparsity = 1.0 - (2 / num_experts)
        config_str = (f"B={batch_size:3d}, D={d_model:4d}, FF={d_ff:4d}, "
                     f"E={num_experts:2d}, K=2")
        print(f"{config_str:>30} | {time_ms:12.2f} | {gflops:10.2f} | {sparsity:10.1%}")

    # Varying top_k with fixed num_experts=8
    print("\nFixed num_experts=8, varying top_k:")
    print_table_header()

    for top_k in [1, 2]:
        gflops, time_ms = benchmark(batch_size, d_model, d_ff, 8, top_k)
        sparsity = 1.0 - (top_k / 8)
        config_str = (f"B={batch_size:3d}, D={d_model:4d}, FF={d_ff:4d}, "
                     f"E= 8, K={top_k}")
        print(f"{config_str:>30} | {time_ms:12.2f} | {gflops:10.2f} | {sparsity:10.1%}")

    print()


def main():
    parser = argparse.ArgumentParser(
        description='Benchmark CPU MoE implementations')
    parser.add_argument('--validate', action='store_true',
                       help='Run validation tests')
    parser.add_argument('--small', action='store_true',
                       help='Run small benchmarks only')
    parser.add_argument('--large', action='store_true',
                       help='Run large benchmarks')
    parser.add_argument('--scaling', action='store_true',
                       help='Run expert scaling benchmark')
    parser.add_argument('--warmup', type=int, default=3,
                       help='Number of warmup iterations')
    parser.add_argument('--runs', type=int, default=10,
                       help='Number of benchmark iterations')

    args = parser.parse_args()

    if args.validate:
        validate_implementations()

    if args.scaling:
        benchmark_scaling()

    # Define benchmark configurations: (batch, d_model, d_ff, experts, top_k)
    if args.small:
        configs = [
            (16, 64, 256, 4, 1),
            (16, 64, 256, 4, 2),
            (16, 64, 256, 8, 2),
        ]
    elif args.large:
        configs = [
            (64, 512, 2048, 8, 2),
            (64, 512, 2048, 16, 2),
            (32, 1024, 4096, 8, 2),
        ]
    else:
        configs = [
            (32, 128, 512, 4, 1),
            (32, 128, 512, 4, 2),
            (32, 128, 512, 8, 2),
            (32, 256, 1024, 8, 2),
            (32, 256, 1024, 16, 2),
        ]

    print("CPU Mixture of Experts Benchmark")
    print("=" * 75)
    print()

    run_benchmarks(configs, args.warmup, args.runs)

    print("\nNotes:")
    print("- Sparsity = 1 - (top_k / num_experts)")
    print("- Higher sparsity means fewer FLOPs but more gating overhead")
    print("- Parallel version uses OpenMP for batch-level parallelism")
    print("- GPU implementations (Part 78) will be 10-100x faster")


if __name__ == "__main__":
    main()

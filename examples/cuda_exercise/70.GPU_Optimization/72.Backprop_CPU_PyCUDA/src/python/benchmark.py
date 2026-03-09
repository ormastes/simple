#!/usr/bin/env python3
/**
 * @file benchmark.py
 * @brief Python bindings for benchmark
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

"""
Performance benchmarking for CPU Backpropagation

This script benchmarks various CPU backpropagation implementations
and compares them against NumPy's matrix operations.
"""

import numpy as np
import time
from typing import List, Tuple
import argparse

try:
    from pycuda_wrapper import CPUBackprop, benchmark, validate_against_numpy
except ImportError:
    print("Error: Could not import pycuda_wrapper")
    print("Make sure the library is built and in the correct path")
    exit(1)


def print_table_header():
    """Print benchmark table header"""
    print(f"{'Config':>20} | {'Impl':>10} | {'Time (ms)':>12} | {'GFLOPS':>10} | {'vs NumPy':>10}")
    print("-" * 75)


def run_benchmarks(configs: List[Tuple[int, int, int]], impls: List[str],
                   warmup: int = 3, runs: int = 10):
    """
    Run comprehensive benchmarks

    Args:
        configs: List of (batch_size, input_dim, output_dim) configurations
        impls: List of implementations to test
        warmup: Number of warmup iterations
        runs: Number of benchmark iterations
    """
    print_table_header()

    for batch_size, input_dim, output_dim in configs:
        input_data = np.random.randn(batch_size, input_dim).astype(np.float32)
        weights = np.random.randn(output_dim, input_dim).astype(np.float32)
        bias = np.random.randn(output_dim).astype(np.float32)
        grad_output = np.random.randn(batch_size, output_dim).astype(np.float32)

        # Benchmark NumPy for comparison
        times = []
        for _ in range(warmup):
            _ = input_data @ weights.T + bias
            _ = grad_output @ weights
            _ = grad_output.T @ input_data
            _ = grad_output.sum(axis=0)

        for _ in range(runs):
            start = time.perf_counter()
            # Forward
            output_np = input_data @ weights.T + bias
            # Backward
            grad_input_np = grad_output @ weights
            grad_weights_np = grad_output.T @ input_data
            grad_bias_np = grad_output.sum(axis=0)
            end = time.perf_counter()
            times.append(end - start)

        numpy_time = np.mean(times) * 1000  # ms

        # FLOPs calculation
        # Forward: 2*B*I*O + B*O
        # Backward: 2*B*I*O (grad_input) + 2*B*I*O (grad_weights) + B*O (grad_bias)
        total_flops = 6 * batch_size * input_dim * output_dim + 2 * batch_size * output_dim
        numpy_gflops = (total_flops / (numpy_time / 1000)) / 1e9

        config_str = f"{batch_size:3d}x{input_dim:4d}x{output_dim:4d}"
        print(f"{config_str:>20} | {'NumPy':>10} | {numpy_time:12.2f} | {numpy_gflops:10.2f} | {1.00:10.2f}x")

        # Benchmark our implementations
        for impl in impls:
            gflops, time_ms = benchmark(batch_size, input_dim, output_dim, impl, warmup, runs)
            speedup = numpy_gflops / gflops if gflops > 0 else float('inf')

            print(f"{config_str:>20} | {impl:>10} | {time_ms:12.2f} | {gflops:10.2f} | {speedup:10.2f}x")

        print()


def validate_implementations(batch_size: int = 32, input_dim: int = 128, output_dim: int = 64):
    """
    Validate all implementations against NumPy

    Args:
        batch_size: Batch size for validation
        input_dim: Input dimension for validation
        output_dim: Output dimension for validation
    """
    print("Validation Results")
    print("=" * 50)

    impls = ['naive']

    for impl in impls:
        is_correct, max_err = validate_against_numpy(batch_size, input_dim, output_dim, impl)
        status = "PASSED" if is_correct else "FAILED"
        print(f"{impl:10s}: {status} (max_error={max_err:.2e})")

    # Also validate activation functions
    print("\nActivation Function Validation:")
    np.random.seed(42)
    test_input = np.random.randn(256).astype(np.float32)

    # ReLU
    relu_out = CPUBackprop.relu_forward(test_input)
    relu_ref = np.maximum(0, test_input)
    relu_err = np.max(np.abs(relu_out - relu_ref))
    print(f"{'ReLU fwd':10s}: {'PASSED' if relu_err < 1e-6 else 'FAILED'} (max_error={relu_err:.2e})")

    # ReLU backward
    grad_out = np.ones_like(test_input)
    relu_grad = CPUBackprop.relu_backward(grad_out, test_input)
    relu_grad_ref = (test_input > 0).astype(np.float32)
    relu_grad_err = np.max(np.abs(relu_grad - relu_grad_ref))
    print(f"{'ReLU bwd':10s}: {'PASSED' if relu_grad_err < 1e-6 else 'FAILED'} (max_error={relu_grad_err:.2e})")

    # Sigmoid
    sigmoid_out = CPUBackprop.sigmoid_forward(test_input)
    sigmoid_ref = 1.0 / (1.0 + np.exp(-test_input))
    sigmoid_err = np.max(np.abs(sigmoid_out - sigmoid_ref))
    print(f"{'Sigmoid fwd':10s}: {'PASSED' if sigmoid_err < 1e-5 else 'FAILED'} (max_error={sigmoid_err:.2e})")

    # Sigmoid backward
    sigmoid_grad = CPUBackprop.sigmoid_backward(grad_out, sigmoid_out)
    sigmoid_grad_ref = sigmoid_ref * (1.0 - sigmoid_ref)
    sigmoid_grad_err = np.max(np.abs(sigmoid_grad - sigmoid_grad_ref))
    print(f"{'Sigmoid bwd':10s}: {'PASSED' if sigmoid_grad_err < 1e-5 else 'FAILED'} (max_error={sigmoid_grad_err:.2e})")

    print()


def main():
    parser = argparse.ArgumentParser(description='Benchmark CPU Backprop implementations')
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

    # Define benchmark configurations (batch_size, input_dim, output_dim)
    if args.small:
        configs = [
            (16, 64, 32),
            (32, 128, 64),
            (64, 256, 128)
        ]
    elif args.large:
        configs = [
            (128, 512, 256),
            (256, 1024, 512),
            (512, 2048, 1024)
        ]
    else:
        configs = [
            (32, 128, 64),
            (64, 256, 128),
            (128, 512, 256),
            (256, 1024, 512)
        ]

    impls = ['naive']

    print("CPU Backpropagation Benchmark")
    print("=" * 75)
    print()

    run_benchmarks(configs, impls, args.warmup, args.runs)

    print("\nNotes:")
    print("- NumPy typically uses optimized BLAS (MKL, OpenBLAS, etc.)")
    print("- Our naive implementation is expected to be slower")
    print("- Backward pass computes 3 gradients (input, weights, bias)")
    print("- GPU implementations (coming in later parts) will be 10-100x faster")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
/**
 * @file roofline.py
 * @brief Python bindings for roofline
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

"""
Roofline Model Analysis for CPU Matrix Multiplication

This script calculates arithmetic intensity and plots the roofline model
to identify memory-bound vs compute-bound operations.

References:
- Williams et al., "Roofline: An Insightful Visual Performance Model"
- https://en.wikipedia.org/wiki/Roofline_model
"""

import numpy as np
import matplotlib.pyplot as plt
import argparse


def calculate_arithmetic_intensity(M, N, K):
    """
    Calculate arithmetic intensity for matrix multiplication

    Args:
        M, N, K: Matrix dimensions (A: M×K, B: K×N, C: M×N)

    Returns:
        Arithmetic intensity in FLOPs/byte
    """
    # Compute operations: 2×M×N×K (multiply-add for each element)
    flops = 2 * M * N * K

    # Memory traffic (assuming no cache reuse)
    # Read A: M×K, Read B: K×N, Write C: M×N
    bytes_transferred = (M*K + K*N + M*N) * 4  # 4 bytes per float32

    arithmetic_intensity = flops / bytes_transferred
    return arithmetic_intensity, flops, bytes_transferred


def plot_roofline(peak_flops, peak_bandwidth, measurements, output_file=None):
    """
    Plot roofline model with measured performance

    Args:
        peak_flops: Peak compute performance (GFLOPS)
        peak_bandwidth: Peak memory bandwidth (GB/s)
        measurements: List of (name, ai, gflops) tuples
        output_file: Optional output file path
    """
    # Calculate ridge point
    ridge_point = peak_flops / peak_bandwidth

    # Create arithmetic intensity range
    ai_range = np.logspace(-1, 3, 1000)  # 0.1 to 1000 FLOPs/byte

    # Memory-bound region: Performance = AI × Bandwidth
    memory_bound = ai_range * peak_bandwidth

    # Compute-bound region: Performance = Peak FLOPs
    compute_bound = np.full_like(ai_range, peak_flops)

    # Actual roofline (minimum of both limits)
    roofline = np.minimum(memory_bound, compute_bound)

    # Create plot
    plt.figure(figsize=(12, 8))
    plt.loglog(ai_range, roofline, 'k-', linewidth=2, label='Roofline')
    plt.loglog(ai_range, memory_bound, 'k--', alpha=0.3, label='Memory Bound')
    plt.axhline(y=peak_flops, color='k', linestyle='--', alpha=0.3,
                label=f'Compute Bound ({peak_flops:.0f} GFLOPS)')

    # Plot ridge point
    plt.axvline(x=ridge_point, color='r', linestyle=':', alpha=0.5,
                label=f'Ridge Point ({ridge_point:.1f} FLOPs/byte)')

    # Plot measurements
    colors = ['red', 'orange', 'yellow', 'green', 'blue', 'purple']
    for i, (name, ai, gflops) in enumerate(measurements):
        color = colors[i % len(colors)]
        plt.loglog(ai, gflops, 'o', markersize=10, color=color,
                  label=f'{name}: {gflops:.1f} GFLOPS @ {ai:.1f} FLOPs/byte')

        # Add annotation
        efficiency = (gflops / min(ai * peak_bandwidth, peak_flops)) * 100
        plt.annotate(f'{efficiency:.0f}%', xy=(ai, gflops),
                    xytext=(5, 5), textcoords='offset points',
                    fontsize=8, alpha=0.7)

    plt.xlabel('Arithmetic Intensity (FLOPs/byte)', fontsize=12)
    plt.ylabel('Performance (GFLOPS)', fontsize=12)
    plt.title(f'Roofline Model: CPU Matrix Multiplication\n'
              f'Peak: {peak_flops:.0f} GFLOPS, Bandwidth: {peak_bandwidth:.0f} GB/s',
              fontsize=14)
    plt.legend(loc='lower right', fontsize=9)
    plt.grid(True, alpha=0.3)
    plt.tight_layout()

    if output_file:
        plt.savefig(output_file, dpi=150)
        print(f"Roofline plot saved to {output_file}")

    plt.show()


def analyze_size_scaling():
    """Analyze how arithmetic intensity scales with matrix size"""
    sizes = [128, 256, 512, 1024, 2048, 4096]
    results = []

    print("Matrix Size Scaling Analysis")
    print("=" * 70)
    print(f"{'Size':>6} | {'FLOPs':>12} | {'Memory (MB)':>12} | {'AI (FLOPs/byte)':>16}")
    print("-" * 70)

    for size in sizes:
        ai, flops, bytes_mem = calculate_arithmetic_intensity(size, size, size)
        results.append((size, ai, flops, bytes_mem))
        print(f"{size:6d} | {flops/1e6:12.1f} | {bytes_mem/1e6:12.2f} | {ai:16.2f}")

    print()
    return results


def main():
    parser = argparse.ArgumentParser(description='Roofline model analysis for CPU MatMul')
    parser.add_argument('--peak-flops', type=float, default=300.0,
                       help='Peak CPU GFLOPS (default: 300)')
    parser.add_argument('--peak-bandwidth', type=float, default=40.0,
                       help='Peak memory bandwidth GB/s (default: 40)')
    parser.add_argument('--output', type=str, default='roofline_cpu_matmul.png',
                       help='Output file path')

    args = parser.parse_args()

    # Analyze size scaling
    analyze_size_scaling()

    # Example measurements (replace with actual benchmark results)
    measurements = [
        ('Naive 128³', 5.6, 8.5),
        ('Naive 512³', 22.4, 18.7),
        ('Naive 1024³', 44.8, 25.4),
        ('Tiled 512³', 22.4, 45.8),
        ('Tiled 1024³', 44.8, 68.2),
        ('Parallel 1024³', 44.8, 245.6),
    ]

    print("\nPlotting roofline model...")
    plot_roofline(args.peak_flops, args.peak_bandwidth, measurements, args.output)


if __name__ == "__main__":
    main()

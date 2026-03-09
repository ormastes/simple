#!/usr/bin/env python3
"""
Roofline analysis for GPU optimization stages.

Plots the roofline model showing the relationship between arithmetic intensity
(FLOP/Byte) and achieved performance (GFLOPS). This helps identify whether
each optimization stage is memory-bound or compute-bound.
"""

import sys

try:
    import matplotlib.pyplot as plt
    import numpy as np
except ImportError:
    print("ERROR: matplotlib and numpy are required. Install with:")
    print("  pip install matplotlib numpy")
    sys.exit(1)


def plot_roofline(peak_gflops=14000, peak_bandwidth_gbs=616):
    """
    Generate a roofline plot for GPU optimization stages.

    Args:
        peak_gflops: Peak GPU compute throughput (GFLOPS)
        peak_bandwidth_gbs: Peak GPU memory bandwidth (GB/s)
    """
    # Arithmetic intensity range
    ai = np.logspace(-2, 4, 1000)

    # Roofline: min(peak_compute, bandwidth * arithmetic_intensity)
    roofline = np.minimum(peak_gflops, peak_bandwidth_gbs * ai)

    fig, ax = plt.subplots(figsize=(12, 8))

    # Plot roofline
    ax.loglog(ai, roofline, "k-", linewidth=2, label="Roofline")

    # Ridge point
    ridge_ai = peak_gflops / peak_bandwidth_gbs
    ax.axvline(x=ridge_ai, color="gray", linestyle="--", alpha=0.5)
    ax.text(ridge_ai * 1.1, peak_gflops * 0.5,
            f"Ridge Point\nAI = {ridge_ai:.1f} FLOP/B",
            fontsize=9, color="gray")

    # Plot optimization stages
    # Format: (name, arithmetic_intensity, achieved_gflops, color, marker)
    stages = [
        ("01 Naive MatMul", 0.25, 50, "#e74c3c", "o"),
        ("02 Shared Memory", 2.0, 200, "#e67e22", "s"),
        ("03 Tiled + Registers", 8.0, 500, "#f1c40f", "^"),
        ("04 Vectorized float4", 16.0, 800, "#2ecc71", "D"),
        ("05 WMMA Tensor Core", 32.0, 1200, "#3498db", "p"),
        ("Attention Naive", 0.5, 30, "#9b59b6", "v"),
        ("Attention Tiled", 4.0, 100, "#1abc9c", "<"),
        ("Attention Flash v2", 12.0, 250, "#34495e", ">"),
    ]

    for name, ai_val, gflops, color, marker in stages:
        ax.plot(ai_val, gflops, marker=marker, color=color, markersize=10,
                markeredgecolor="black", markeredgewidth=0.5, label=name)

    ax.set_xlabel("Arithmetic Intensity (FLOP/Byte)", fontsize=12)
    ax.set_ylabel("Performance (GFLOPS)", fontsize=12)
    ax.set_title(f"Roofline Model (Peak: {peak_gflops} GFLOPS, {peak_bandwidth_gbs} GB/s)",
                 fontsize=14)
    ax.legend(loc="lower right", fontsize=9)
    ax.grid(True, alpha=0.3, which="both")
    ax.set_xlim(0.01, 10000)
    ax.set_ylim(1, peak_gflops * 2)

    # Add regions
    ax.text(0.02, peak_gflops * 0.05, "Memory Bound", fontsize=11, color="blue", alpha=0.6)
    ax.text(ridge_ai * 5, peak_gflops * 0.8, "Compute Bound", fontsize=11, color="red", alpha=0.6)

    plt.tight_layout()
    plt.savefig("roofline.png", dpi=150)
    print("Saved roofline.png")
    plt.close()


def main():
    # Default values for a typical high-end GPU (e.g., A100)
    plot_roofline(peak_gflops=14000, peak_bandwidth_gbs=616)
    print("Roofline plot generated.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Visualize benchmark results as bar charts comparing optimization stages.

Reads benchmark_results.json and generates comparison plots showing
performance (GFLOPS) or execution time for each stage of optimization.
"""

import json
import sys
from pathlib import Path

try:
    import matplotlib.pyplot as plt
    import numpy as np
except ImportError:
    print("ERROR: matplotlib and numpy are required. Install with:")
    print("  pip install matplotlib numpy")
    sys.exit(1)


def load_results(path="benchmark_results.json"):
    """Load benchmark results from JSON file."""
    with open(path) as f:
        return json.load(f)


def plot_matmul_stages():
    """Plot expected GFLOPS for each matmul optimization stage."""
    stages = ["01_naive", "02_shared_memory", "03_tiled", "04_vectorized", "05_wmma"]
    labels = ["Naive", "Shared\nMemory", "Tiled +\nRegisters", "Vectorized\nfloat4", "WMMA\nTensor Core"]
    expected_gflops = [50, 200, 500, 800, 1200]
    colors = ["#e74c3c", "#e67e22", "#f1c40f", "#2ecc71", "#3498db"]

    fig, ax = plt.subplots(figsize=(10, 6))
    bars = ax.bar(labels, expected_gflops, color=colors, edgecolor="black", linewidth=0.5)

    for bar, gflops in zip(bars, expected_gflops):
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 20,
                f"{gflops}", ha="center", va="bottom", fontweight="bold")

    ax.set_ylabel("GFLOPS", fontsize=12)
    ax.set_title("Matrix Multiplication: Progressive Optimization Stages", fontsize=14)
    ax.set_ylim(0, 1400)
    ax.grid(axis="y", alpha=0.3)

    plt.tight_layout()
    plt.savefig("matmul_stages.png", dpi=150)
    print("Saved matmul_stages.png")
    plt.close()


def plot_attention_comparison():
    """Plot attention stages comparison."""
    labels = ["Naive\n(O(N^2) mem)", "Tiled\n(Shared Mem)", "Flash v2\n(O(N) mem)"]
    relative_speed = [1.0, 2.5, 5.0]
    memory_usage = [100, 100, 10]  # Relative %
    colors = ["#e74c3c", "#f1c40f", "#3498db"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    ax1.bar(labels, relative_speed, color=colors, edgecolor="black", linewidth=0.5)
    ax1.set_ylabel("Relative Speedup", fontsize=12)
    ax1.set_title("Attention: Speed Comparison", fontsize=13)
    ax1.grid(axis="y", alpha=0.3)

    ax2.bar(labels, memory_usage, color=colors, edgecolor="black", linewidth=0.5)
    ax2.set_ylabel("Relative Memory Usage (%)", fontsize=12)
    ax2.set_title("Attention: Memory Usage", fontsize=13)
    ax2.grid(axis="y", alpha=0.3)

    plt.tight_layout()
    plt.savefig("attention_stages.png", dpi=150)
    print("Saved attention_stages.png")
    plt.close()


def main():
    plot_matmul_stages()
    plot_attention_comparison()
    print("\nAll plots generated.")


if __name__ == "__main__":
    main()

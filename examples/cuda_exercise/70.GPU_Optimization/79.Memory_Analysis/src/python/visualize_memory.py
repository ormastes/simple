"""
Memory usage timeline visualization using matplotlib.

Reads a JSON log of allocation events and plots:
- Memory usage over time
- Peak usage marker
- Per-label breakdown

Usage:
    python visualize_memory.py memory_log.json
"""

import json
import sys
from pathlib import Path

try:
    import matplotlib.pyplot as plt
    import matplotlib.ticker as ticker
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False


def load_events(path: str) -> list:
    """Load allocation events from a JSON file.

    Expected format:
    [
        {"time_ms": 0.0, "action": "alloc", "label": "weights", "size": 4096},
        {"time_ms": 1.5, "action": "free", "label": "weights", "size": 4096},
        ...
    ]
    """
    with open(path) as f:
        return json.load(f)


def compute_timeline(events: list) -> tuple:
    """Convert events into (times, usages) arrays for plotting."""
    times = []
    usages = []
    current = 0
    for ev in events:
        t = ev["time_ms"]
        if ev["action"] == "alloc":
            current += ev["size"]
        elif ev["action"] == "free":
            current -= ev["size"]
        times.append(t)
        usages.append(current)
    return times, usages


def plot_timeline(times: list, usages: list, output_path: str = None):
    """Plot memory usage over time."""
    if not HAS_MATPLOTLIB:
        print("matplotlib not available; skipping plot")
        return

    fig, ax = plt.subplots(figsize=(12, 6))

    # Convert to MB
    usages_mb = [u / (1024 * 1024) for u in usages]

    ax.plot(times, usages_mb, linewidth=1.5, color="steelblue")
    ax.fill_between(times, usages_mb, alpha=0.3, color="steelblue")

    # Mark peak
    peak_idx = usages_mb.index(max(usages_mb))
    ax.annotate(
        f"Peak: {usages_mb[peak_idx]:.1f} MB",
        xy=(times[peak_idx], usages_mb[peak_idx]),
        xytext=(times[peak_idx] + 1, usages_mb[peak_idx] + 5),
        arrowprops=dict(arrowstyle="->", color="red"),
        fontsize=10,
        color="red",
    )

    ax.set_xlabel("Time (ms)")
    ax.set_ylabel("GPU Memory Usage (MB)")
    ax.set_title("GPU Memory Usage Timeline")
    ax.yaxis.set_major_formatter(ticker.FormatStrFormatter("%.0f"))
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    if output_path:
        plt.savefig(output_path, dpi=150)
        print(f"Saved plot to {output_path}")
    else:
        plt.show()


def main():
    if len(sys.argv) < 2:
        print("Usage: python visualize_memory.py <memory_log.json> [output.png]")
        sys.exit(1)

    events = load_events(sys.argv[1])
    times, usages = compute_timeline(events)

    output = sys.argv[2] if len(sys.argv) > 2 else None
    plot_timeline(times, usages, output)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Benchmark all optimization stages and collect timing data.

Runs each matmul, backprop, and attention stage with configurable matrix sizes,
collects GPU timing via CUDA events, and outputs a JSON results file.
"""

import subprocess
import json
import sys
import os
from pathlib import Path


def find_test_binary():
    """Locate the compiled test binary in common build directories."""
    candidates = [
        Path("build/70.GPU_Optimization/78.Progressive_Optimizations/78_Progressive_Optimizations_test"),
        Path("build/78_Progressive_Optimizations_test"),
    ]
    for p in candidates:
        if p.exists():
            return str(p)
    return None


def run_benchmark(binary, test_filter, iterations=10):
    """Run a specific test with timing and return elapsed time."""
    env = os.environ.copy()
    env["GTEST_FILTER"] = test_filter
    env["BENCHMARK_ITERATIONS"] = str(iterations)

    try:
        result = subprocess.run(
            [binary, f"--gtest_filter={test_filter}"],
            capture_output=True, text=True, timeout=300, env=env
        )
        return result.stdout, result.returncode
    except subprocess.TimeoutExpired:
        return "TIMEOUT", -1


def main():
    binary = find_test_binary()
    if binary is None:
        print("ERROR: Could not find test binary. Build the project first.")
        sys.exit(1)

    print(f"Using binary: {binary}")

    stages = {
        "matmul": [
            "MatmulStagesTest.Naive",
            "MatmulStagesTest.SharedMemory",
            "MatmulStagesTest.Tiled",
            "MatmulStagesTest.Vectorized",
            "MatmulStagesTest.WMMA",
        ],
        "backprop": [
            "BackpropStagesTest.Naive",
            "BackpropStagesTest.Fused",
            "BackpropStagesTest.Optimized",
        ],
        "attention": [
            "AttentionStagesTest.Naive",
            "AttentionStagesTest.Tiled",
            "AttentionStagesTest.FlashV2",
        ],
    }

    results = {}
    for category, tests in stages.items():
        results[category] = {}
        for test in tests:
            print(f"Running {test}...")
            output, rc = run_benchmark(binary, test)
            results[category][test] = {
                "return_code": rc,
                "output": output[:500] if isinstance(output, str) else "",
            }

    output_path = "benchmark_results.json"
    with open(output_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nResults written to {output_path}")


if __name__ == "__main__":
    main()

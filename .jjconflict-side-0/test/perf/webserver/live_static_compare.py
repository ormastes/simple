#!/usr/bin/env python3
"""Live static HTTP harness for Simple and an optional nginx target.

This script is intentionally conservative: it benchmarks only servers that are
explicitly supplied by URL or command, and reports SKIP when nginx or a target
server is unavailable. It is a proof harness, not a claim that Simple is faster
than nginx.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import os
import shutil
import signal
import socket
import statistics
import subprocess
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass


@dataclass
class Target:
    name: str
    url: str
    command: str | None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--requests", type=int, default=256)
    parser.add_argument("--concurrency", type=int, default=16)
    parser.add_argument("--timeout", type=float, default=5.0)
    parser.add_argument("--warmup", type=int, default=16)
    parser.add_argument("--simple-url", default=os.getenv("SIMPLE_WEBSERVER_URL", ""))
    parser.add_argument("--simple-cmd", default=os.getenv("SIMPLE_WEBSERVER_CMD", ""))
    parser.add_argument("--nginx-url", default=os.getenv("NGINX_WEBSERVER_URL", ""))
    parser.add_argument("--nginx-cmd", default=os.getenv("NGINX_WEBSERVER_CMD", ""))
    parser.add_argument("--probe", action="store_true")
    return parser.parse_args()


def tool_status() -> dict[str, str]:
    return {
        name: shutil.which(name) or "missing"
        for name in ("nginx", "docker", "wrk", "hey", "ab", "curl", "python3")
    }


def start_command(command: str) -> subprocess.Popen[str]:
    return subprocess.Popen(
        command,
        shell=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        preexec_fn=os.setsid,
    )


def stop_process(proc: subprocess.Popen[str] | None) -> None:
    if proc is None or proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
        proc.wait(timeout=3)
    except Exception:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except Exception:
            pass


def wait_ready(url: str, timeout_s: float) -> bool:
    deadline = time.monotonic() + timeout_s
    while time.monotonic() < deadline:
        try:
            fetch_once(url, timeout_s=1.0)
            return True
        except Exception:
            time.sleep(0.05)
    return False


def fetch_once(url: str, timeout_s: float) -> int:
    request = urllib.request.Request(url, headers={"Connection": "close"})
    with urllib.request.urlopen(request, timeout=timeout_s) as response:
        response.read()
        return response.status


def timed_fetch(url: str, timeout_s: float) -> tuple[int, int]:
    start = time.perf_counter_ns()
    try:
        status = fetch_once(url, timeout_s)
    except (urllib.error.URLError, socket.timeout, TimeoutError, OSError):
        return 0, time.perf_counter_ns() - start
    return status, time.perf_counter_ns() - start


def percentile(sorted_values: list[int], pct: float) -> int:
    if not sorted_values:
        return 0
    idx = int((len(sorted_values) - 1) * pct)
    return sorted_values[idx]


def bench(target: Target, requests: int, concurrency: int, timeout_s: float, warmup: int) -> str:
    for _ in range(warmup):
        timed_fetch(target.url, timeout_s)

    start = time.perf_counter_ns()
    with concurrent.futures.ThreadPoolExecutor(max_workers=concurrency) as pool:
        results = list(pool.map(lambda _: timed_fetch(target.url, timeout_s), range(requests)))
    total_ns = time.perf_counter_ns() - start

    latencies = sorted(lat for status, lat in results if 200 <= status < 400)
    errors = len(results) - len(latencies)
    req_per_s = int((len(results) * 1_000_000_000) / total_ns) if total_ns > 0 else 0
    avg_us = int(statistics.mean(latencies) / 1000) if latencies else 0
    p50_us = percentile(latencies, 0.50) // 1000
    p99_us = percentile(latencies, 0.99) // 1000
    total_ms = total_ns // 1_000_000

    return (
        f"{target.name},{requests},{concurrency},{avg_us},{p50_us},"
        f"{p99_us},{total_ms},{req_per_s},{errors},{target.url}"
    )


def main() -> int:
    args = parse_args()
    tools = tool_status()
    for name, path in tools.items():
        print(f"tool,{name},{path}")

    if args.probe:
        return 0

    targets = [
        Target("simple", args.simple_url, args.simple_cmd or None),
        Target("nginx", args.nginx_url, args.nginx_cmd or None),
    ]

    print("label,requests,concurrency,avg_us,p50_us,p99_us,total_ms,req_per_s,errors,url")
    ran = False
    procs: list[subprocess.Popen[str] | None] = []
    try:
        for target in targets:
            if target.name == "nginx" and tools["nginx"] == "missing" and not target.url:
                print("SKIP,nginx_missing,no_nginx_binary_or_url")
                continue
            if not target.url:
                print(f"SKIP,{target.name}_missing,no_url")
                continue

            proc = start_command(target.command) if target.command else None
            procs.append(proc)
            if not wait_ready(target.url, args.timeout):
                print(f"SKIP,{target.name}_not_ready,{target.url}")
                continue

            print(bench(target, args.requests, args.concurrency, args.timeout, args.warmup))
            ran = True
    finally:
        for proc in procs:
            stop_process(proc)

    return 0 if ran else 2


if __name__ == "__main__":
    sys.exit(main())

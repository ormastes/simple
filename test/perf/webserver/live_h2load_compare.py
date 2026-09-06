#!/usr/bin/env python3
"""Fail-closed, duration-based Simple/nginx comparison using h2load.

The producer writes raw outputs and machine-readable evidence.  It never treats
one reachable target or a missing Simple executable as comparative evidence.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import platform
import re
import shlex
import shutil
import signal
import socket
import ssl
import subprocess
import sys
import time
import urllib.parse
import urllib.request
from dataclasses import asdict, dataclass
from pathlib import Path


REQUESTS_RE = re.compile(
    r"requests:\s+(\d+) total,\s+(\d+) started,\s+(\d+) done,\s+"
    r"(\d+) succeeded,\s+(\d+) failed,\s+(\d+) errored,\s+(\d+) timeout"
)
RATE_RE = re.compile(r"([0-9]+(?:\.[0-9]+)?)\s+req/s")
LATENCY_RE = re.compile(
    r"time for request:\s+\S+\s+\S+\s+([0-9]+(?:\.[0-9]+)?)(us|ms|s)"
)
PERCENTILE_RE = re.compile(r"^\s*(50|95|99)%\s+([0-9]+(?:\.[0-9]+)?)(us|ms|s)\s*$", re.M)
MIN_ABBA_SAMPLES = 32


@dataclass
class H2Result:
    total: int
    succeeded: int
    failed: int
    errored: int
    timeout: int
    rps: float
    mean_latency_us: float
    p50_us: float
    p95_us: float
    p99_us: float


def duration_us(value: str, unit: str) -> float:
    return float(value) * {"us": 1.0, "ms": 1000.0, "s": 1_000_000.0}[unit]


def parse_h2load(text: str) -> H2Result:
    requests = REQUESTS_RE.search(text)
    rate = RATE_RE.search(text)
    latency = LATENCY_RE.search(text)
    percentiles = {key: duration_us(value, unit) for key, value, unit in PERCENTILE_RE.findall(text)}
    if not requests or not rate or not latency:
        raise ValueError("incomplete-h2load-output")
    total, _started, done, succeeded, failed, errored, timeout = map(int, requests.groups())
    if done != succeeded + failed or total < done:
        raise ValueError("inconsistent-h2load-request-counts")
    if failed < errored + timeout:
        raise ValueError("inconsistent-h2load-failure-counts")
    return H2Result(
        total=total, succeeded=succeeded, failed=failed, errored=errored, timeout=timeout,
        rps=float(rate.group(1)), mean_latency_us=duration_us(*latency.groups()),
        p50_us=percentiles.get("50", 0.0), p95_us=percentiles.get("95", 0.0),
        p99_us=percentiles.get("99", 0.0),
    )


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def fetch_identity(url: str, timeout: float, insecure: bool) -> tuple[int, str]:
    context = ssl._create_unverified_context() if insecure else ssl.create_default_context()
    request = urllib.request.Request(url, headers={"Connection": "close"})
    with urllib.request.urlopen(request, timeout=timeout, context=context) as response:
        body = response.read()
        return len(body), hashlib.sha256(body).hexdigest()


def proc_group_usage(pgid: int) -> tuple[int, int]:
    ticks = 0
    max_rss_kib = 0
    for entry in Path("/proc").glob("[0-9]*"):
        try:
            fields = (entry / "stat").read_text().split()
            if int(fields[4]) != pgid:
                continue
            ticks += int(fields[13]) + int(fields[14])
            for line in (entry / "status").read_text().splitlines():
                if line.startswith(("VmHWM:", "VmRSS:")):
                    max_rss_kib = max(max_rss_kib, int(line.split()[1]))
        except (FileNotFoundError, PermissionError, ProcessLookupError, ValueError, IndexError):
            continue
    return ticks, max_rss_kib


def target_protocol(url: str) -> tuple[str, str, str]:
    parsed = urllib.parse.urlsplit(url)
    if parsed.scheme not in ("http", "https") or not parsed.hostname:
        raise ValueError("target-url-must-be-http-or-https")
    return parsed.scheme, parsed.path or "/", parsed.query


def tls_identity(url: str, timeout: float, insecure: bool, http_version: str) -> dict[str, str]:
    parsed = urllib.parse.urlsplit(url)
    if parsed.scheme == "http":
        return {"tls_version": "none", "cipher": "none", "alpn": http_version}
    context = ssl._create_unverified_context() if insecure else ssl.create_default_context()
    context.set_alpn_protocols(["h2" if http_version == "h2" else "http/1.1"])
    with socket.create_connection((parsed.hostname, parsed.port or 443), timeout=timeout) as raw:
        with context.wrap_socket(raw, server_hostname=parsed.hostname) as secured:
            cipher = secured.cipher()
            return {"tls_version": secured.version() or "unknown",
                    "cipher": cipher[0] if cipher else "unknown",
                    "alpn": secured.selected_alpn_protocol() or "none"}


def command_uses_artifact(command: str, artifact: Path) -> bool:
    try:
        words = shlex.split(command)
    except ValueError:
        return False
    executables = [word for word in words if "=" not in word or word.startswith(("/", "."))]
    if not executables:
        return False
    try:
        return Path(executables[0]).resolve() == artifact.resolve()
    except OSError:
        return False


def parse_h2load_log(text: str) -> list[int]:
    latencies: list[int] = []
    for line in text.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) != 3:
            raise ValueError("invalid-h2load-request-log")
        try:
            _client, status, latency_us = map(int, fields)
        except ValueError as error:
            raise ValueError("invalid-h2load-request-log") from error
        if status < 200 or status >= 400 or latency_us < 0:
            raise ValueError("unsuccessful-h2load-request-log")
        latencies.append(latency_us)
    if not latencies:
        raise ValueError("empty-h2load-request-log")
    return sorted(latencies)


def percentile(values: list[int], fraction: float) -> float:
    return float(values[int((len(values) - 1) * fraction)])


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--simple-artifact", default=os.getenv("SIMPLE_WEBSERVER_ARTIFACT", ""))
    parser.add_argument("--simple-url", default=os.getenv("SIMPLE_WEBSERVER_URL", ""))
    parser.add_argument("--simple-cmd", default=os.getenv("SIMPLE_WEBSERVER_CMD", ""))
    parser.add_argument("--nginx-url", default=os.getenv("NGINX_WEBSERVER_URL", ""))
    parser.add_argument("--nginx-cmd", default=os.getenv("NGINX_WEBSERVER_CMD", ""))
    parser.add_argument("--duration", type=int, default=15)
    parser.add_argument("--warmup", type=int, default=5)
    parser.add_argument("--samples", type=int, default=MIN_ABBA_SAMPLES)
    parser.add_argument("--clients", type=int, default=16)
    parser.add_argument("--streams", type=int, default=8)
    parser.add_argument("--timeout", type=float, default=5.0)
    parser.add_argument("--insecure", action="store_true")
    parser.add_argument("--http-version", choices=("h2", "http1.1"), default="h2")
    parser.add_argument("--evidence-dir", default="build/test-artifacts/05_perf/webserver/h2load-compare")
    return parser.parse_args()


def start(command: str) -> subprocess.Popen[str] | None:
    if not command:
        return None
    return subprocess.Popen(command, shell=True, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, preexec_fn=os.setsid)


def stop(proc: subprocess.Popen[str] | None) -> None:
    if proc is None or proc.poll() is not None:
        return
    os.killpg(proc.pid, signal.SIGTERM)
    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait(timeout=2)


def main() -> int:
    args = arguments()
    artifact = Path(args.simple_artifact) if args.simple_artifact else None
    h2load = shutil.which("h2load")
    if not artifact or not artifact.is_file() or not os.access(artifact, os.X_OK):
        print("STATUS,UNAVAILABLE,simple-executable-artifact-required")
        return 2
    if not h2load:
        print("STATUS,UNAVAILABLE,h2load-required")
        return 2
    if not args.simple_url or not args.nginx_url:
        print("STATUS,UNAVAILABLE,paired-target-urls-required")
        return 2
    if not args.simple_cmd or not args.nginx_cmd:
        print("STATUS,UNAVAILABLE,managed-server-commands-required-for-cpu-rss")
        return 2
    if not command_uses_artifact(args.simple_cmd, artifact):
        print("STATUS,UNAVAILABLE,simple-command-must-launch-admitted-artifact")
        return 2
    if args.duration <= 0 or args.warmup < 0 or args.clients <= 0 or args.streams <= 0:
        print("STATUS,FAIL,invalid-workload-parameters")
        return 2
    if args.samples < MIN_ABBA_SAMPLES or args.samples % 4:
        print(f"STATUS,FAIL,at-least-{MIN_ABBA_SAMPLES}-complete-abba-samples-required")
        return 2
    try:
        simple_shape = target_protocol(args.simple_url)
        nginx_shape = target_protocol(args.nginx_url)
    except ValueError as error:
        print(f"STATUS,FAIL,{error}")
        return 2
    if simple_shape != nginx_shape:
        print("STATUS,FAIL,http-tls-path-query-parity-required")
        return 2

    evidence = Path(args.evidence_dir)
    evidence.mkdir(parents=True, exist_ok=True)
    targets = {"simple": (args.simple_url, args.simple_cmd), "nginx": (args.nginx_url, args.nginx_cmd)}
    processes: dict[str, subprocess.Popen[str] | None] = {}
    rows: list[dict[str, object]] = []
    try:
        for name, (_url, command) in targets.items():
            processes[name] = start(command)
        deadline = time.monotonic() + args.timeout
        identities: dict[str, tuple[int, str]] = {}
        while time.monotonic() < deadline and len(identities) != 2:
            for name, (url, _command) in targets.items():
                if name in identities:
                    continue
                try:
                    identities[name] = fetch_identity(url, 1.0, args.insecure)
                except Exception:
                    pass
            if len(identities) != 2:
                time.sleep(0.05)
        if len(identities) != 2:
            print("STATUS,UNAVAILABLE,paired-target-readiness-required")
            return 2
        if identities["simple"] != identities["nginx"]:
            print("STATUS,FAIL,payload-size-sha256-parity-required")
            return 1
        try:
            tls_profiles = {name: tls_identity(url, args.timeout, args.insecure, args.http_version)
                            for name, (url, _command) in targets.items()}
        except (OSError, ssl.SSLError) as error:
            print(f"STATUS,UNAVAILABLE,tls-profile-probe-failed:{type(error).__name__}")
            return 2
        if tls_profiles["simple"] != tls_profiles["nginx"]:
            print("STATUS,FAIL,tls-version-cipher-alpn-parity-required")
            return 1
        for name, proc in processes.items():
            assert proc is not None
            if proc.poll() is not None or proc_group_usage(os.getpgid(proc.pid))[1] <= 0:
                print(f"STATUS,UNAVAILABLE,{name}-managed-process-not-observable")
                return 2

        manifest = {
            "schema": "simple-nginx-h2load-environment-v1",
            "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "host": {"platform": platform.platform(), "machine": platform.machine(),
                     "cpu_count": os.cpu_count(), "python": platform.python_version()},
            "h2load": subprocess.run([h2load, "--version"], text=True, capture_output=True).stdout.strip(),
            "simple_artifact": {"path": str(artifact.resolve()), "sha256": sha256_file(artifact),
                                "bytes": artifact.stat().st_size},
            "workload": {"duration_s": args.duration, "warmup_s": args.warmup,
                         "clients": args.clients, "streams": args.streams,
                         "samples": args.samples, "order": "ABBA"},
            "protocol": simple_shape[0], "path": simple_shape[1], "query": simple_shape[2],
            "http_version": args.http_version,
            "payload": {"bytes": identities["simple"][0], "sha256": identities["simple"][1]},
            "tls": tls_profiles["simple"],
            "targets": {name: {"url": value[0], "managed_process": bool(value[1]),
                               "command_sha256": hashlib.sha256(value[1].encode()).hexdigest()}
                        for name, value in targets.items()},
        }
        (evidence / "environment.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")

        pattern = ("simple", "nginx", "nginx", "simple")
        clock_ticks = os.sysconf("SC_CLK_TCK")
        for index in range(args.samples):
            name = pattern[index % 4]
            url = targets[name][0]
            proc = processes[name]
            pgid = os.getpgid(proc.pid) if proc else -1
            before_ticks, before_rss = proc_group_usage(pgid) if pgid > 0 else (0, 0)
            command = [h2load, "--duration", f"{args.duration}s", "--warm-up-time", f"{args.warmup}s",
                       "-c", str(args.clients), "-m", str(args.streams)]
            request_log = evidence / f"sample-{index + 1:02d}-{name}.requests.tsv"
            command.extend(["--log-file", str(request_log)])
            if args.http_version == "http1.1":
                command.append("--h1")
            if args.insecure:
                command.append("-k")
            command.append(url)
            completed = subprocess.run(command, text=True, capture_output=True,
                                       timeout=args.duration + args.warmup + args.timeout + 10)
            raw = completed.stdout + completed.stderr
            (evidence / f"sample-{index + 1:02d}-{name}.txt").write_text(raw)
            if completed.returncode != 0:
                print("STATUS,FAIL,h2load-nonzero")
                return 1
            try:
                result = parse_h2load(raw)
                request_latencies = parse_h2load_log(request_log.read_text())
            except ValueError as error:
                print(f"STATUS,FAIL,{error}")
                return 1
            if len(request_latencies) != result.succeeded or result.failed or result.errored or result.timeout:
                print("STATUS,FAIL,error-free-complete-request-log-required")
                return 1
            result.p50_us = percentile(request_latencies, 0.50)
            result.p95_us = percentile(request_latencies, 0.95)
            result.p99_us = percentile(request_latencies, 0.99)
            after_ticks, after_rss = proc_group_usage(pgid) if pgid > 0 else (0, 0)
            row = asdict(result)
            row.update({"sample": index + 1, "order": "ABBA"[index % 4], "server": name,
                        "duration_s": args.duration, "warmup_s": args.warmup,
                        "clients": args.clients, "streams": args.streams,
                        "server_cpu_s": max(0, after_ticks - before_ticks) / clock_ticks,
                        "server_max_rss_kib": max(before_rss, after_rss),
                        "resource_scope": "process-group" if proc else "unavailable-external-target",
                        "body_bytes": identities[name][0], "body_sha256": identities[name][1]})
            rows.append(row)

        with (evidence / "raw.jsonl").open("w") as stream:
            for row in rows:
                stream.write(json.dumps(row, sort_keys=True) + "\n")
        (evidence / "summary.json").write_text(json.dumps({"status": "PASS", "rows": rows}, indent=2) + "\n")
        with (evidence / "summary.csv").open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
        print(f"STATUS,PASS,{evidence}")
        return 0
    finally:
        for proc in processes.values():
            stop(proc)


if __name__ == "__main__":
    raise SystemExit(main())

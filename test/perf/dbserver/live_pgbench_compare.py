#!/usr/bin/env python3
"""Paired PostgreSQL/Simple pgwire benchmark evidence collector.

The collector deliberately emits unavailable rows instead of substituting a
mock, embedded database, or historical result for either live target.
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
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from statistics import median
from typing import Any


SCHEMA = """DROP TABLE IF EXISTS simple_bench_accounts;
CREATE TABLE simple_bench_accounts (
  id BIGINT PRIMARY KEY,
  balance BIGINT NOT NULL,
  payload TEXT NOT NULL
);
INSERT INTO simple_bench_accounts
SELECT i, i * 7, repeat('x', 96) FROM generate_series(1, 100000) AS i;
"""
WORKLOAD = """\\set account_id random(1, 100000)
BEGIN;
SELECT balance, payload FROM simple_bench_accounts WHERE id = :account_id;
UPDATE simple_bench_accounts SET balance = balance + 1 WHERE id = :account_id;
COMMIT;
"""
ABBA = ("postgres", "simple", "simple", "postgres")
MIN_ABBA_SAMPLES = 32
NUMBER = r"([0-9]+(?:\.[0-9]+)?)"


@dataclass
class Target:
    name: str
    url: str
    start_cmd: str
    process: subprocess.Popen[str] | None = None
    pgid: int | None = None
    cpu_start: int | None = None
    cpu_end: int | None = None
    max_rss_kib: int | None = None
    cpu_ticks_by_pid: dict[int, int] = field(default_factory=dict)
    fixture_balance_sum: int | None = None
    expected_balance_delta: int = 0


@dataclass(frozen=True)
class ProcessGroupUsage:
    cpu_ticks: int
    rss_kib: int
    process_count: int
    pid_ticks: dict[int, int]


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def command_identity(command: str) -> dict[str, str]:
    if not command:
        return {"command": "", "executable": "", "sha256": ""}
    exe = shlex.split(command)[0]
    resolved = shutil_which(exe)
    digest = ""
    if resolved and Path(resolved).is_file():
        digest = hashlib.sha256(Path(resolved).read_bytes()).hexdigest()
    return {"command": command, "executable": resolved or exe, "sha256": digest}


def shutil_which(exe: str) -> str | None:
    if "/" in exe:
        return str(Path(exe).resolve()) if Path(exe).exists() else None
    for directory in os.environ.get("PATH", "").split(os.pathsep):
        candidate = Path(directory) / exe
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate.resolve())
    return None


def process_group_usage(pgid: int) -> ProcessGroupUsage:
    """Return aggregate CPU and resident memory for the managed server group.

    A server wrapper commonly forks workers, so the shell launcher PID is not
    meaningful evidence.  RSS is the instantaneous sum for the complete group;
    callers retain the maximum across the measured interval.
    """
    ticks = 0
    rss_kib = 0
    process_count = 0
    pid_ticks: dict[int, int] = {}
    for entry in Path("/proc").glob("[0-9]*"):
        try:
            fields = (entry / "stat").read_text().split()
            if int(fields[4]) != pgid:
                continue
            process_count += 1
            pid_ticks[int(entry.name)] = int(fields[13]) + int(fields[14])
            ticks += pid_ticks[int(entry.name)]
            for line in (entry / "status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    rss_kib += int(line.split()[1])
                    break
        except (FileNotFoundError, PermissionError, ProcessLookupError, ValueError, IndexError):
            continue
    return ProcessGroupUsage(ticks, rss_kib, process_count, pid_ticks)


def observe_process_group(target: Target, usage: ProcessGroupUsage) -> None:
    """Retain CPU for workers that terminate before the next final sample."""
    target.max_rss_kib = max(target.max_rss_kib or 0, usage.rss_kib)
    for pid, ticks in usage.pid_ticks.items():
        target.cpu_ticks_by_pid[pid] = max(target.cpu_ticks_by_pid.get(pid, 0), ticks)


def run(argv: list[str], timeout: float, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(argv, text=True, capture_output=True, timeout=timeout, env=env)


def psql(psql_bin: str, url: str, sql: str, timeout: float) -> subprocess.CompletedProcess[str]:
    return run([psql_bin, "-X", "-v", "ON_ERROR_STOP=1", "-At", url, "-c", sql], timeout)


def command_uses_artifact(command: str, artifact: Path) -> bool:
    try:
        words = shlex.split(command)
    except ValueError:
        return False
    if not words:
        return False
    try:
        return Path(words[0]).resolve() == artifact.resolve()
    except OSError:
        return False


def wait_ready(psql_bin: str, target: Target, timeout: float) -> str | None:
    deadline = time.monotonic() + timeout
    last = "not-attempted"
    while time.monotonic() < deadline:
        try:
            result = psql(psql_bin, target.url, "SELECT 1", min(2.0, timeout))
            if result.returncode == 0 and result.stdout.strip().endswith("1"):
                return None
            last = (result.stderr or result.stdout).strip()[-300:]
        except (subprocess.TimeoutExpired, OSError) as exc:
            last = type(exc).__name__
        time.sleep(0.1)
    return f"readiness-timeout:{last}"


def fixture_state(psql_bin: str, url: str, timeout: float) -> tuple[str | None, dict[str, int]]:
    query = (
        "SELECT count(*) || '|' || COALESCE(sum(balance), 0) || '|' || "
        "COALESCE(min(length(payload)), 0) || '|' || COALESCE(max(length(payload)), 0) "
        "FROM simple_bench_accounts"
    )
    try:
        result = psql(psql_bin, url, query, timeout)
    except (subprocess.TimeoutExpired, OSError) as exc:
        return f"fixture-query-{type(exc).__name__}", {}
    if result.returncode != 0:
        return "fixture-query-failed", {}
    try:
        count, balance_sum, payload_min, payload_max = (int(part) for part in result.stdout.strip().split("|"))
    except ValueError:
        return "fixture-query-invalid", {}
    if count != 100000 or payload_min != 96 or payload_max != 96:
        return "fixture-query-mismatch", {}
    return None, {"row_count": count, "balance_sum": balance_sum,
                  "payload_min_bytes": payload_min, "payload_max_bytes": payload_max}


def configure(target: Target, psql_bin: str, timeout: float) -> tuple[str | None, dict[str, str], dict[str, int]]:
    try:
        setup = psql(psql_bin, target.url, SCHEMA, timeout)
    except (subprocess.TimeoutExpired, OSError) as exc:
        return f"schema-setup-{type(exc).__name__}", {}, {}
    if setup.returncode != 0:
        return "schema-setup-failed", {}, {}
    settings_sql = (
        "SELECT current_setting('fsync') || '|' || "
        "current_setting('synchronous_commit') || '|' || "
        "current_setting('full_page_writes')"
    )
    try:
        settings = psql(psql_bin, target.url, settings_sql, timeout)
    except (subprocess.TimeoutExpired, OSError) as exc:
        return f"durability-query-{type(exc).__name__}", {}, {}
    if settings.returncode != 0:
        return "durability-query-failed", {}, {}
    parts = settings.stdout.strip().split("|")
    if len(parts) != 3:
        return "durability-query-invalid", {}, {}
    durability = dict(zip(("fsync", "synchronous_commit", "full_page_writes"), parts))
    reason, fixture = fixture_state(psql_bin, target.url, timeout)
    if reason:
        return reason, durability, {}
    return None, durability, fixture


def parse_pgbench(text: str) -> dict[str, Any]:
    patterns = {
        "tps": rf"tps\s*=\s*{NUMBER}",
        "latency_avg_ms": rf"latency average\s*=\s*{NUMBER}\s*ms",
        "transactions": r"number of transactions actually processed:\s*([0-9]+)",
        "failed": r"number of failed transactions:\s*([0-9]+)",
        "retried": r"number of transactions retried:\s*([0-9]+)",
    }
    values: dict[str, Any] = {}
    for key, pattern in patterns.items():
        match = re.search(pattern, text, re.IGNORECASE)
        if not match:
            raise ValueError("missing-required-pgbench-metrics")
        values[key] = float(match.group(1)) if key in ("tps", "latency_avg_ms") else int(match.group(1))
    if values["tps"] <= 0 or values["latency_avg_ms"] <= 0 or values["transactions"] <= 0:
        raise ValueError("missing-required-pgbench-metrics")
    return values


def run_pgbench_monitored(argv: list[str], timeout: float, target: Target) -> tuple[subprocess.CompletedProcess[str] | None, ProcessGroupUsage, str | None]:
    """Run a client while polling the complete managed server process group."""
    if target.pgid is None:
        return None, ProcessGroupUsage(0, 0, 0, {}), "managed-server-process-not-observable"
    try:
        process = subprocess.Popen(argv, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError as exc:
        return None, process_group_usage(target.pgid), f"pgbench-exec:{type(exc).__name__}"
    deadline = time.monotonic() + timeout
    max_rss_kib = 0
    final_usage = process_group_usage(target.pgid)
    while process.poll() is None:
        final_usage = process_group_usage(target.pgid)
        observe_process_group(target, final_usage)
        max_rss_kib = max(max_rss_kib, final_usage.rss_kib)
        if final_usage.process_count == 0:
            process.kill()
            stdout, stderr = process.communicate()
            return subprocess.CompletedProcess(argv, process.returncode, stdout, stderr), final_usage, "managed-server-process-not-observable"
        if time.monotonic() >= deadline:
            process.kill()
            process.communicate()
            return None, final_usage, "pgbench-exec:TimeoutExpired"
        time.sleep(0.05)
    stdout, stderr = process.communicate()
    final_usage = process_group_usage(target.pgid)
    observe_process_group(target, final_usage)
    max_rss_kib = max(max_rss_kib, final_usage.rss_kib)
    return subprocess.CompletedProcess(argv, process.returncode, stdout, stderr), ProcessGroupUsage(final_usage.cpu_ticks, max_rss_kib, final_usage.process_count, final_usage.pid_ticks), None


def pgbench_once(args: argparse.Namespace, target: Target, workload: Path, duration: int) -> tuple[dict[str, Any] | None, str | None]:
    argv = [args.pgbench, "-n", "-c", str(args.clients), "-j", str(args.jobs), "-T", str(duration), "-f", str(workload), target.url]
    started = time.monotonic()
    if target.pgid is None:
        return None, "managed-server-process-not-observable"
    result, usage, monitor_reason = run_pgbench_monitored(argv, duration + args.command_grace, target)
    if monitor_reason:
        return None, monitor_reason
    assert result is not None
    if result.returncode != 0:
        return None, f"pgbench-exit-{result.returncode}"
    try:
        metrics = parse_pgbench(result.stdout + "\n" + result.stderr)
    except ValueError as exc:
        return None, str(exc)
    if metrics["failed"] or metrics["retried"]:
        reason = f"invalid-transactions:failed={metrics['failed']},retried={metrics['retried']}"
        if not args.record_invalid_transactions:
            return None, reason
        metrics.update({"transaction_valid": False, "invalid_reason": reason})
    else:
        metrics["transaction_valid"] = True
    target.expected_balance_delta += metrics["transactions"]
    observe_process_group(target, usage)
    metrics.update({"wall_seconds": time.monotonic() - started,
                    "server_process_group_cpu_ticks": usage.cpu_ticks,
                    "server_process_group_rss_kib": usage.rss_kib,
                    "resource_scope": "managed-process-group"})
    return metrics, None


def verify_persistence(target: Target, psql_bin: str, timeout: float) -> str | None:
    reason, fixture = fixture_state(psql_bin, target.url, timeout)
    if reason:
        return f"post-run-{reason}"
    expected = (target.fixture_balance_sum or 0) + target.expected_balance_delta
    if fixture["balance_sum"] != expected:
        return "post-run-balance-sum-mismatch"
    return None


def unavailable(name: str, reason: str) -> dict[str, Any]:
    return {"target": name, "status": "unavailable", "reason": reason}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--postgres-url", default="")
    parser.add_argument("--simple-url", default="")
    parser.add_argument("--postgres-start-cmd", default="")
    parser.add_argument("--simple-start-cmd", default="")
    parser.add_argument("--simple-artifact", default=os.getenv("SIMPLE_DBSERVER_ARTIFACT", ""))
    parser.add_argument("--pgbench", default="pgbench")
    parser.add_argument("--psql", default="psql")
    parser.add_argument("--out-dir", default="build/test-artifacts/pgbench-compare")
    parser.add_argument("--duration", type=int, default=30)
    parser.add_argument("--warmup-duration", type=int, default=10)
    parser.add_argument("--samples", type=int, default=MIN_ABBA_SAMPLES)
    parser.add_argument("--clients", type=int, default=16)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--ready-timeout", type=float, default=20)
    parser.add_argument("--command-grace", type=float, default=10)
    parser.add_argument("--record-invalid-transactions", action="store_true",
                        help="retain failed/retried pgbench rows as explicitly invalid evidence")
    args = parser.parse_args(argv)
    if args.duration <= 0 or args.warmup_duration <= 0 or args.clients <= 0 or args.jobs <= 0:
        parser.error("duration, warmup-duration, clients, and jobs must be positive")
    if args.samples < MIN_ABBA_SAMPLES or args.samples % 4:
        parser.error(f"samples must be at least {MIN_ABBA_SAMPLES} and divisible by four (complete ABBA blocks)")

    artifact = Path(args.simple_artifact) if args.simple_artifact else None
    if not artifact or not artifact.is_file() or not os.access(artifact, os.X_OK):
        print("STATUS: UNAVAILABLE simple-executable-artifact-required")
        return 2
    if not args.postgres_start_cmd or not args.simple_start_cmd:
        print("STATUS: UNAVAILABLE managed-server-commands-required-for-process-group-cpu-rss")
        return 2
    if not command_uses_artifact(args.simple_start_cmd, artifact):
        print("STATUS: UNAVAILABLE simple-command-must-launch-admitted-artifact")
        return 2

    out = Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    workload = out / "workload.sql"
    workload.write_text(WORKLOAD)
    targets = {
        "postgres": Target("postgres", args.postgres_url, args.postgres_start_cmd),
        "simple": Target("simple", args.simple_url, args.simple_start_cmd),
    }
    manifest: dict[str, Any] = {
        "schema": "simple-pgbench-compare-v1", "fixture_schema_sha256": sha256_text(SCHEMA),
        "workload_sha256": sha256_text(WORKLOAD), "fixture_rows": 100000,
        "duration_seconds": args.duration, "warmup_seconds": args.warmup_duration,
        "samples": args.samples, "order": "ABBA", "clients": args.clients, "jobs": args.jobs,
        "host": {"platform": platform.platform(), "machine": platform.machine(), "cpu_count": os.cpu_count()},
        "tools": {"pgbench": command_identity(args.pgbench), "psql": command_identity(args.psql)},
        "simple_artifact": {"path": str(artifact.resolve()), "sha256": hashlib.sha256(artifact.read_bytes()).hexdigest(),
                            "bytes": artifact.stat().st_size},
        "targets": {},
    }
    raw: list[dict[str, Any]] = []
    available: dict[str, Target] = {}
    try:
        for name, target in targets.items():
            if not target.url:
                manifest["targets"][name] = unavailable(name, "missing-target-url")
                continue
            try:
                target.process = subprocess.Popen(target.start_cmd, shell=True, text=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
                target.pgid = os.getpgid(target.process.pid)
                initial_usage = process_group_usage(target.pgid)
                target.cpu_start = initial_usage.cpu_ticks
                observe_process_group(target, initial_usage)
            except OSError as exc:
                manifest["targets"][name] = unavailable(name, f"managed-server-start-{type(exc).__name__}")
                continue
            reason = wait_ready(args.psql, target, args.ready_timeout)
            if reason:
                manifest["targets"][name] = unavailable(name, reason)
                continue
            if target.pgid is None or process_group_usage(target.pgid).process_count == 0:
                manifest["targets"][name] = unavailable(name, "managed-server-process-not-observable")
                continue
            reason, durability, fixture = configure(target, args.psql, args.ready_timeout)
            if reason:
                manifest["targets"][name] = unavailable(name, reason)
                continue
            target.fixture_balance_sum = fixture["balance_sum"]
            manifest["targets"][name] = {"target": name, "status": "ready", "url": target.url, "durability": durability,
                                         "fixture": fixture, "server": command_identity(target.start_cmd),
                                         "resource_scope": "managed-process-group"}
            available[name] = target

        if len(available) == 2:
            postgres_durability = manifest["targets"]["postgres"]["durability"]
            simple_durability = manifest["targets"]["simple"]["durability"]
            if postgres_durability != simple_durability:
                for name in ("postgres", "simple"):
                    manifest["targets"][name] = unavailable(name, "durability-settings-mismatch")
                available.clear()

        for name in ("postgres", "simple"):
            if name not in available:
                continue
            warmup_metrics, reason = pgbench_once(args, available[name], workload, args.warmup_duration)
            if warmup_metrics and not warmup_metrics["transaction_valid"]:
                reason = warmup_metrics["invalid_reason"]
            if reason:
                manifest["targets"][name] = unavailable(name, f"warmup-{reason}")
                available.pop(name)

        for index in range(args.samples):
            name = ABBA[index % 4]
            if name not in available:
                raw.append({"sample": index + 1, "block": index // 4 + 1, "position": ABBA[index % 4], **unavailable(name, manifest["targets"][name]["reason"])})
                continue
            metrics, reason = pgbench_once(args, available[name], workload, args.duration)
            row = {"sample": index + 1, "block": index // 4 + 1, "position": ABBA[index % 4], "target": name}
            if reason:
                row.update(unavailable(name, reason))
            elif metrics and not metrics["transaction_valid"]:
                row.update({"status": "invalid", **metrics})
            else:
                row.update({"status": "measured", **(metrics or {})})
            raw.append(row)

        for name, target in tuple(available.items()):
            measured_rows = [row for row in raw if row["target"] == name and row["status"] == "measured"]
            invalid_rows = [row for row in raw if row["target"] == name and row["status"] == "invalid"]
            if invalid_rows:
                manifest["targets"][name] = unavailable(name, "invalid-transactions-recorded")
                continue
            if len(measured_rows) != args.samples // 2:
                continue
            reason = verify_persistence(target, args.psql, args.ready_timeout)
            if reason:
                manifest["targets"][name] = unavailable(name, reason)
                for row in measured_rows:
                    row.update(unavailable(name, reason))
                continue
            manifest["targets"][name]["result_query_persistence_check"] = "verified"

        for target in targets.values():
            if target.pgid is None:
                continue
            final_usage = process_group_usage(target.pgid)
            observe_process_group(target, final_usage)
            target.cpu_end = sum(target.cpu_ticks_by_pid.values())
    finally:
        for target in targets.values():
            if target.pgid is not None:
                try:
                    os.killpg(target.pgid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
            if target.process and target.process.poll() is None:
                try:
                    target.process.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    if target.pgid is not None:
                        try:
                            os.killpg(target.pgid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                    else:
                        target.process.kill()

    (out / "raw.jsonl").write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in raw))
    summary: dict[str, Any] = {"schema": "simple-pgbench-summary-v1", "targets": {}}
    for name in ("postgres", "simple"):
        rows = [row for row in raw if row["target"] == name and row["status"] == "measured"]
        if len(rows) != args.samples // 2:
            invalid = [row for row in raw if row["target"] == name and row["status"] == "invalid"]
            reason = "invalid-transactions-recorded" if invalid else manifest["targets"][name].get("reason", "incomplete-samples")
            summary["targets"][name] = unavailable(name, reason)
        else:
            target = targets[name]
            summary["targets"][name] = {
                "status": "measured", "samples": len(rows),
                "tps_median": median(row["tps"] for row in rows),
                "latency_avg_ms_median": median(row["latency_avg_ms"] for row in rows),
                "transactions": sum(row["transactions"] for row in rows),
                "failed": sum(row["failed"] for row in rows), "retried": sum(row["retried"] for row in rows),
                "server_process_group_cpu_ticks_delta": None if target.cpu_start is None or target.cpu_end is None else target.cpu_end - target.cpu_start,
                "server_process_group_max_rss_kib": target.max_rss_kib,
                "resource_scope": "managed-process-group",
                "result_query_persistence_check": manifest["targets"][name].get("result_query_persistence_check", "unverified"),
            }
    (out / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    manifest["completed_unix_ns"] = time.time_ns()
    (out / "environment.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    with (out / "summary.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=["target", "status", "samples", "tps_median", "latency_avg_ms_median", "transactions", "failed", "retried", "server_process_group_cpu_ticks_delta", "server_process_group_max_rss_kib", "resource_scope", "result_query_persistence_check", "reason"])
        writer.writeheader()
        for name, values in summary["targets"].items():
            writer.writerow({"target": name, **values})
    print(f"pgbench_compare_evidence={out}")
    if all(v["status"] == "measured" for v in summary["targets"].values()):
        print("STATUS: PASS pgbench comparison evidence collected")
        return 0
    print("STATUS: UNAVAILABLE pgbench comparison evidence incomplete or invalid")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())

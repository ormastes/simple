#!/usr/bin/env python3
"""Measure checker startup separately from manifest orchestration and checking.

Python rows deliberately do not implement Simple parsing.  They bound only
manifest validation, hashing, sharding, and worker-process overhead.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = ROOT / "test/05_perf/checker_startup_manifest.tsv"
DEFAULT_RUST_SIMPLE = ROOT / "src/compiler_rust/target/bootstrap/simple"
DEFAULT_CHECKER = ROOT / "src/app/check/main.spl"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_manifest(path: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    seen: set[str] = set()
    for line_no, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw or raw.startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 3:
            raise ValueError(f"{path}:{line_no}: expected id<TAB>digest<TAB>path")
        item_id, expected, source_name = fields
        if item_id in seen:
            raise ValueError(f"{path}:{line_no}: duplicate id {item_id}")
        source = Path(source_name)
        if not source.is_absolute():
            source = ROOT / source
        if not source.is_file():
            raise ValueError(f"{path}:{line_no}: missing source {source_name}")
        actual = sha256_file(source)
        if actual != expected:
            raise ValueError(
                f"{path}:{line_no}: digest mismatch for {source_name}: "
                f"expected {expected}, got {actual}"
            )
        seen.add(item_id)
        rows.append({"id": item_id, "source_digest": expected, "path": source_name})
    if not rows:
        raise ValueError(f"{path}: manifest is empty")
    return rows


def write_manifest(path: Path, rows: list[dict[str, str]]) -> None:
    text = "".join(f"{r['id']}\t{r['source_digest']}\t{r['path']}\n" for r in rows)
    path.write_text(text, encoding="utf-8")


def shard_rows(rows: list[dict[str, str]], workers: int) -> list[list[dict[str, str]]]:
    count = min(workers, len(rows))
    shards: list[list[dict[str, str]]] = [[] for _ in range(count)]
    for index, row in enumerate(rows):
        shards[index % count].append(row)
    return shards


def proc_snapshot(root_pids: list[int]) -> tuple[int, int, int]:
    """Return live count, zombie count, and aggregate current RSS in KiB."""
    parents: dict[int, int] = {}
    rss: dict[int, int] = {}
    states: dict[int, str] = {}
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            fields = (entry / "stat").read_text(encoding="utf-8").split()
            pid = int(fields[0])
            parents[pid] = int(fields[3])
            states[pid] = fields[2]
            for line in (entry / "status").read_text(encoding="utf-8").splitlines():
                if line.startswith("VmRSS:"):
                    rss[pid] = int(line.split()[1])
                    break
        except (FileNotFoundError, PermissionError, ProcessLookupError, ValueError):
            continue
    selected = set(root_pids)
    changed = True
    while changed:
        changed = False
        for pid, parent in parents.items():
            if parent in selected and pid not in selected:
                selected.add(pid)
                changed = True
    zombies = sum(1 for pid in selected if states.get(pid) == "Z")
    return len(selected) - zombies, zombies, sum(rss.get(pid, 0) for pid in selected)


def run_group(
    commands: list[list[str]], envs: list[dict[str, str]], work: Path, timeout_s: float
) -> dict[str, object]:
    work.mkdir(parents=True, exist_ok=True)
    children: dict[int, dict[str, object]] = {}
    start = time.monotonic()
    for index, command in enumerate(commands):
        stdout_path = work / f"worker-{index}.stdout"
        stderr_path = work / f"worker-{index}.stderr"
        pid = os.fork()
        if pid == 0:
            os.setsid()
            out_fd = os.open(stdout_path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
            err_fd = os.open(stderr_path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
            os.dup2(out_fd, 1)
            os.dup2(err_fd, 2)
            os.close(out_fd)
            os.close(err_fd)
            try:
                os.chdir(ROOT)
                os.execve(command[0], command, envs[index])
            except BaseException as exc:
                os.write(2, f"exec failed: {exc}\n".encode())
                os._exit(127)
        children[pid] = {
            "index": index,
            "command": command,
            "stdout": stdout_path,
            "stderr": stderr_path,
        }

    pending = set(children)
    max_processes = len(children)
    max_zombies = 0
    peak_rss_kb = 0
    timed_out = False
    while pending:
        process_count, zombie_count, rss_kb = proc_snapshot(list(children))
        max_processes = max(max_processes, process_count)
        max_zombies = max(max_zombies, zombie_count)
        peak_rss_kb = max(peak_rss_kb, rss_kb)
        for pid in list(pending):
            waited, status, usage = os.wait4(pid, os.WNOHANG)
            if waited:
                pending.remove(pid)
                children[pid]["status"] = status
                children[pid]["usage"] = usage
        if pending and time.monotonic() - start > timeout_s:
            timed_out = True
            for pid in pending:
                try:
                    os.killpg(pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
            time.sleep(0.1)
            for pid in pending:
                try:
                    os.killpg(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            for pid in list(pending):
                waited, status, usage = os.wait4(pid, 0)
                pending.remove(pid)
                children[pid]["status"] = status
                children[pid]["usage"] = usage
        if pending:
            time.sleep(0.02)

    wall_s = time.monotonic() - start
    user_s = sum(float(c["usage"].ru_utime) for c in children.values())
    sys_s = sum(float(c["usage"].ru_stime) for c in children.values())
    # Very short Python workers can exit between /proc samples.  Their direct
    # per-process maxima are an exact lower bound and make a zero-RSS row
    # impossible; the sampled tree sum remains authoritative when larger.
    direct_peak_rss_kb = sum(int(c["usage"].ru_maxrss) for c in children.values())
    peak_rss_kb = max(peak_rss_kb, direct_peak_rss_kb)
    ordered = sorted(children.values(), key=lambda c: int(c["index"]))
    results = []
    for child in ordered:
        status = int(child["status"])
        exit_code = os.waitstatus_to_exitcode(status)
        results.append(
            {
                "exit_code": exit_code,
                "stdout": Path(child["stdout"]).read_text(encoding="utf-8", errors="replace"),
                "stderr": Path(child["stderr"]).read_text(encoding="utf-8", errors="replace"),
            }
        )
    return {
        "wall_s": wall_s,
        "user_s": user_s,
        "sys_s": sys_s,
        "cpu_percent": ((user_s + sys_s) / wall_s * 100.0) if wall_s else 0.0,
        "peak_rss_kb": peak_rss_kb,
        "peak_process_count": max_processes,
        "peak_zombie_count": max_zombies,
        "timed_out": timed_out,
        "results": results,
    }


def outcome_checksum(outcomes: list[dict[str, object]]) -> str:
    canonical = "".join(
        json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
        for row in sorted(outcomes, key=lambda r: (str(r["id"]), str(r["path"])))
    )
    return hashlib.sha256(canonical.encode()).hexdigest()


def python_worker(manifest: Path, result: Path) -> int:
    rows = read_manifest(manifest)
    with result.open("w", encoding="utf-8") as stream:
        for row in rows:
            stream.write(
                json.dumps(
                    {
                        **row,
                        "status": "orchestration_ok",
                        "exit_code": 0,
                        "semantic_parity": "not_applicable",
                    },
                    sort_keys=True,
                )
                + "\n"
            )
    return 0


def parse_last_json(stdout: str) -> dict[str, object] | None:
    for line in reversed(stdout.splitlines()):
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            return value
    return None


def normalize_status(value: object) -> str:
    status = str(value).lower()
    if status in {"ok", "pass", "passed", "success", "checked"}:
        return "ok"
    return status


def rust_outcomes(
    shards: list[list[dict[str, str]]], group: dict[str, object]
) -> tuple[list[dict[str, object]], str]:
    outcomes: list[dict[str, object]] = []
    proof = "exact"
    for rows, result in zip(shards, group["results"]):
        summary = parse_last_json(str(result["stdout"]))
        success = (
            result["exit_code"] == 0
            and summary is not None
            and summary.get("status") == "ok"
            and int(summary.get("checked", -1)) == len(rows)
            and int(summary.get("errors", -1)) == 0
        )
        if not success:
            proof = "unproven_chunk_aggregate_failure"
        for row in rows:
            outcomes.append(
                {
                    **row,
                    "status": "ok" if success else "aggregate_error",
                    "exit_code": int(result["exit_code"]),
                }
            )
    return outcomes, proof


def native_outcomes(result_paths: list[Path]) -> tuple[list[dict[str, object]], str]:
    terminal: dict[tuple[str, str], dict[str, object]] = {}
    for path in result_paths:
        if not path.exists():
            continue
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not isinstance(row, dict) or "id" not in row or "path" not in row:
                continue
            if "exit_code" not in row or "status" not in row:
                continue
            terminal[(str(row["id"]), str(row["path"]))] = {
                "id": str(row["id"]),
                "path": str(row["path"]),
                "source_digest": str(row.get("source_digest", "")),
                "status": normalize_status(row["status"]),
                "exit_code": int(row["exit_code"]),
            }
    outcomes = list(terminal.values())
    return outcomes, "exact" if outcomes else "missing_terminal_rows"


def make_env(cache_dir: Path) -> dict[str, str]:
    env = dict(os.environ)
    env["SIMPLE_CACHE"] = str(cache_dir / "simple-cache")
    env["SIMPLE_NATIVE_BUILD_CACHE_DIR"] = str(cache_dir / "native-build")
    env["XDG_CACHE_HOME"] = str(cache_dir / "xdg")
    return env


def engine_commands(
    engine: str,
    shards: list[list[dict[str, str]]],
    shard_paths: list[Path],
    result_paths: list[Path],
    rust_simple: Path,
    checker: Path,
    runner: Path | None,
    compiler_digest: str,
) -> tuple[list[list[str]], list[list[str]]]:
    if engine == "python-orchestration":
        startup = [[sys.executable, str(Path(__file__).resolve()), "--worker-help"] for _ in shards]
        total = [
            [sys.executable, str(Path(__file__).resolve()), "--python-worker", f"--manifest={manifest}", f"--result={result}"]
            for manifest, result in zip(shard_paths, result_paths)
        ]
    elif engine == "rust-source":
        startup = [[str(rust_simple), "run", str(checker), "--help"] for _ in shards]
        total = [
            [str(rust_simple), "run", str(checker), "--json", *[row["path"] for row in rows]]
            for rows in shards
        ]
    else:
        if runner is None:
            raise ValueError(f"{engine}: runner missing; set SIMPLE_STAGE4_DIAG_CHECK_RUNNER or --runner")
        mode = engine.removeprefix("pure-simple-")
        empty = shard_paths[0].parent / "empty.tsv"
        empty.write_text("", encoding="utf-8")
        startup = [
            [str(runner), f"--manifest={empty}", f"--result={result}.startup", f"--compiler-digest={compiler_digest}", f"--mode={mode}"]
            for result in result_paths
        ]
        total = [
            [str(runner), f"--manifest={manifest}", f"--result={result}", f"--compiler-digest={compiler_digest}", f"--mode={mode}"]
            for manifest, result in zip(shard_paths, result_paths)
        ]
    return startup, total


def benchmark(args: argparse.Namespace) -> dict[str, object]:
    manifest_path = Path(args.manifest).resolve()
    rows = read_manifest(manifest_path)
    worker_values = [int(value) for value in args.workers.split(",")]
    if any(value < 1 for value in worker_values):
        raise ValueError("worker counts must be positive")
    states = args.cache_states.split(",")
    if states != ["cold", "warm"]:
        raise ValueError("--cache-states must be cold,warm so warm rows have a measured cold predecessor")
    runner_text = args.runner or os.environ.get("SIMPLE_STAGE4_DIAG_CHECK_RUNNER", "")
    runner = Path(runner_text).resolve() if runner_text else None
    engines = args.engine.split(",")
    report_rows: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(prefix="simple-checker-perf-") as temp_name:
        temp = Path(temp_name)
        for engine in engines:
            for requested_workers in worker_values:
                shards = shard_rows(rows, requested_workers)
                worker_count = len(shards)
                lane = temp / f"{engine}-{worker_count}"
                lane.mkdir(parents=True)
                startup_cache = lane / "startup-cache"
                total_cache = lane / "total-cache"
                startup_cache.mkdir()
                total_cache.mkdir()
                for state in states:
                    run_dir = lane / state
                    run_dir.mkdir()
                    shard_paths: list[Path] = []
                    result_paths: list[Path] = []
                    for index, shard in enumerate(shards):
                        shard_path = run_dir / f"shard-{index}.tsv"
                        write_manifest(shard_path, shard)
                        shard_paths.append(shard_path)
                        result_paths.append(run_dir / f"result-{index}.jsonl")
                    startup, total = engine_commands(
                        engine,
                        shards,
                        shard_paths,
                        result_paths,
                        Path(args.rust_simple).resolve(),
                        Path(args.checker).resolve(),
                        runner,
                        args.compiler_digest,
                    )
                    startup_envs = [make_env(startup_cache) for _ in startup]
                    total_envs = [make_env(total_cache) for _ in total]
                    startup_metrics = run_group(startup, startup_envs, run_dir / "startup", args.timeout)
                    total_metrics = run_group(total, total_envs, run_dir / "total", args.timeout)
                    if engine == "python-orchestration":
                        outcomes = []
                        for path in result_paths:
                            for line in path.read_text(encoding="utf-8").splitlines():
                                outcomes.append(json.loads(line))
                        parity_proof = "not_applicable_no_simple_semantics"
                    elif engine == "rust-source":
                        outcomes, parity_proof = rust_outcomes(shards, total_metrics)
                    else:
                        outcomes, parity_proof = native_outcomes(result_paths)
                    report_rows.append(
                        {
                            "engine": engine,
                            "cache_state": state,
                            "workers": worker_count,
                            "files": len(rows),
                            "startup_wall_ms": round(float(startup_metrics["wall_s"]) * 1000, 3),
                            "total_wall_ms": round(float(total_metrics["wall_s"]) * 1000, 3),
                            "files_per_second": round(len(rows) / float(total_metrics["wall_s"]), 6),
                            "cpu_seconds": round(float(total_metrics["user_s"]) + float(total_metrics["sys_s"]), 6),
                            "cpu_percent": round(float(total_metrics["cpu_percent"]), 3),
                            "peak_rss_kb": int(total_metrics["peak_rss_kb"]),
                            "peak_process_count": int(total_metrics["peak_process_count"]),
                            "peak_zombie_count": int(total_metrics["peak_zombie_count"]),
                            "worker_exit_codes": [r["exit_code"] for r in total_metrics["results"]],
                            "timed_out": bool(total_metrics["timed_out"]),
                            "outcome_count": len(outcomes),
                            "outcome_checksum": outcome_checksum(outcomes),
                            "parity_proof": parity_proof,
                            "outcomes": outcomes,
                        }
                    )
    try:
        manifest_label = str(manifest_path.relative_to(ROOT))
    except ValueError:
        manifest_label = str(manifest_path)
    return {
        "schema_version": 1,
        "scope": "parse/check preflight; not HIR/MIR/codegen or artifact execution",
        "python_semantics": "none; orchestration and SHA-256 verification only",
        "cache_definition": "cold=fresh logical cache directories; warm=same directories, immediately repeated; OS page cache uncontrolled",
        "manifest": manifest_label,
        "manifest_digest": sha256_file(manifest_path),
        "manifest_files": len(rows),
        "host": {"cpu_count": os.cpu_count(), "python": sys.version.split()[0]},
        "artifacts": {
            "rust_simple": str(Path(args.rust_simple).resolve()),
            "rust_simple_digest": sha256_file(Path(args.rust_simple).resolve()),
            "checker": str(Path(args.checker).resolve()),
            "checker_digest": sha256_file(Path(args.checker).resolve()),
            "runner": str(runner) if runner else None,
            "runner_digest": sha256_file(runner) if runner and runner.is_file() else None,
            "compiler_digest": args.compiler_digest or None,
        },
        "rows": report_rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--engine", default="python-orchestration,rust-source")
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--workers", default="1,4")
    parser.add_argument("--cache-states", default="cold,warm")
    parser.add_argument("--rust-simple", default=str(DEFAULT_RUST_SIMPLE))
    parser.add_argument("--checker", default=str(DEFAULT_CHECKER))
    parser.add_argument("--runner")
    parser.add_argument("--compiler-digest", default="")
    parser.add_argument("--timeout", type=float, default=300.0)
    parser.add_argument("--output")
    parser.add_argument("--python-worker", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--worker-help", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--result", help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        if args.worker_help:
            print("ready")
            return 0
        if args.python_worker:
            if not args.result:
                raise ValueError("--python-worker requires --result")
            return python_worker(Path(args.manifest), Path(args.result))
        report = benchmark(args)
        rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.output:
            Path(args.output).write_text(rendered, encoding="utf-8")
        else:
            print(rendered, end="")
        return 0
    except (OSError, ValueError) as exc:
        print(f"checker-performance: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

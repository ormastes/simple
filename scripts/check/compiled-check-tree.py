#!/usr/bin/env python3
"""Run a compiled Simple checker in parallel, bounded, resumable batches.

This file is orchestration only.  All Simple parsing/check semantics come from
the compiled checker supplied with --checker.  A failed batch is isolated by
rerunning only that batch's files one at a time, which yields exact per-file
outcomes without paying one process startup for every passing source.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_ROOTS = ("src/compiler", "src/app", "src/lib")
# GNU time writes the per-batch high-water metrics. Production runs are Linux
# build hosts; SIMPLE_CHECK_TIME_BIN exists so the orchestrator can be
# exercised on hosts without /usr/bin/time (the metrics file is simply absent
# there and read_metrics falls back to zeros).
TIME_BIN = Path(os.environ.get("SIMPLE_CHECK_TIME_BIN", "/usr/bin/time"))


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def discover(roots: list[str], limit: int | None) -> list[dict[str, str]]:
    paths: set[Path] = set()
    for root_name in roots:
        root = Path(root_name)
        if not root.is_absolute():
            root = ROOT / root
        if root.is_file() and root.suffix == ".spl":
            paths.add(root.resolve())
        elif root.is_dir():
            paths.update(path.resolve() for path in root.rglob("*.spl") if path.is_file())
        else:
            raise ValueError(f"source root does not exist: {root_name}")
    ordered = sorted(paths, key=lambda path: str(path))
    if limit is not None:
        ordered = ordered[:limit]
    rows = []
    for index, path in enumerate(ordered, 1):
        try:
            label = str(path.relative_to(ROOT))
        except ValueError:
            label = str(path)
        rows.append(
            {
                "id": f"source-{index:06d}",
                "source_digest": sha256_file(path),
                "path": label,
            }
        )
    if not rows:
        raise ValueError("no .spl files discovered")
    return rows


def manifest_text(rows: list[dict[str, str]]) -> str:
    return "".join(f"{r['id']}\t{r['source_digest']}\t{r['path']}\n" for r in rows)


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def read_metrics(path: Path) -> dict[str, float | int]:
    values: dict[str, float | int] = {
        "user_s": 0.0,
        "system_s": 0.0,
        "wall_s": 0.0,
        "max_rss_kb": 0,
    }
    if not path.is_file():
        return values
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        key, separator, raw = line.partition("=")
        if not separator or key not in values:
            continue
        try:
            values[key] = int(raw) if key == "max_rss_kb" else float(raw)
        except ValueError:
            continue
    return values


def run_checker(
    checker: Path,
    files: list[dict[str, str]],
    stem: Path,
    timeout_s: float,
    max_rss_kib: int = 0,
    rss_interval_s: float = 2.0,
) -> dict[str, object]:
    stdout_path = stem.with_suffix(".stdout.log")
    stderr_path = stem.with_suffix(".stderr.log")
    metrics_path = stem.with_suffix(".metrics")
    command = [
        str(TIME_BIN),
        "-f",
        "user_s=%U\nsystem_s=%S\nwall_s=%e\nmax_rss_kb=%M",
        "-o",
        str(metrics_path),
        str(checker),
        "--progress",
        "count",
        *[row["path"] for row in files],
    ]
    started = time.monotonic()
    timed_out = False
    rss_ceiling_exceeded = False
    rss_sampler = "proc-tree" if Path("/proc").is_dir() else "unsupported"
    rss_tree_peak_kib = 0
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.Popen(
            command,
            cwd=ROOT,
            stdout=stdout,
            stderr=stderr,
            start_new_session=True,
        )
        # Memory ceiling (doc/08_tracking/bug/executable_checker_failed_only_retry_peak_rss_2026-08-02):
        # sample the checker process TREE between wait slices and kill the
        # process group when the summed resident set exceeds --max-rss-kib.
        # A ceiling can only be enforced on a platform whose tree RSS it can
        # measure: where /proc is unavailable the sampler reports
        # "unsupported", records nothing, and NEVER claims enforcement.
        deadline = started + timeout_s
        while process.poll() is None:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                timed_out = True
                break
            if max_rss_kib > 0 and rss_sampler == "proc-tree":
                sample = tree_rss_kib(process.pid)
                if sample is not None:
                    rss_tree_peak_kib = max(rss_tree_peak_kib, sample)
                    if sample > max_rss_kib:
                        rss_ceiling_exceeded = True
                        break
            try:
                process.wait(timeout=min(rss_interval_s, max(remaining, 0.05)))
            except subprocess.TimeoutExpired:
                continue
        if process.poll() is None:
            # Timed out or hit the RSS ceiling: same bounded teardown as the
            # original timeout path, so per-file isolation is preserved.
            os.killpg(process.pid, signal.SIGTERM)
            try:
                exit_code = process.wait(timeout=2.0)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                exit_code = process.wait()
        else:
            exit_code = process.returncode
    metrics = read_metrics(metrics_path)
    return {
        "exit_code": exit_code,
        "timed_out": timed_out,
        "rss_ceiling_exceeded": rss_ceiling_exceeded,
        "rss_sampler": rss_sampler,
        "rss_tree_peak_kib": rss_tree_peak_kib,
        "rss_ceiling_kib": max_rss_kib,
        "elapsed_s": round(time.monotonic() - started, 6),
        "metrics": metrics,
        "stdout": str(stdout_path),
        "stderr": str(stderr_path),
        "stdout_digest": sha256_file(stdout_path),
        "stderr_digest": sha256_file(stderr_path),
        "file_count": len(files),
    }


def tree_rss_kib(pid: int) -> int | None:
    """Summed VmRSS (KiB) of `pid` and all its descendants via /proc.

    Returns None when /proc is unavailable or unreadable so callers can
    distinguish "tree used X" from "this platform cannot be measured".
    """
    proc = Path("/proc")
    if not proc.is_dir():
        return None
    try:
        children: dict[int, list[int]] = {}
        rss_by_pid: dict[int, int] = {}
        for entry in proc.iterdir():
            if not entry.name.isdigit():
                continue
            try:
                status = (entry / "status").read_text(encoding="ascii", errors="replace")
            except OSError:
                continue
            rss = 0
            for line in status.splitlines():
                if line.startswith("VmRSS:"):
                    try:
                        rss = int(line.split()[1])
                    except (ValueError, IndexError):
                        rss = 0
                    break
            try:
                stat = (entry / "stat").read_text(encoding="ascii", errors="replace")
                ppid = int(stat.rpartition(")")[2].split()[1])
            except (OSError, ValueError, IndexError):
                continue
            children.setdefault(ppid, []).append(int(entry.name))
            rss_by_pid[int(entry.name)] = rss
        total = 0
        stack = [pid]
        seen: set[int] = set()
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            total += rss_by_pid.get(current, 0)
            stack.extend(children.get(current, []))
        return total
    except OSError:
        return None


def diagnostic_family(result: dict[str, object]) -> tuple[str, str]:
    if result["timed_out"]:
        return "timeout", "checker invocation exceeded its bounded timeout"
    if result.get("rss_ceiling_exceeded"):
        return (
            "rss_ceiling",
            f"checker process tree exceeded the --max-rss-kib ceiling ({result.get('rss_ceiling_kib')} KiB)",
        )
    exit_code = int(result["exit_code"])
    if exit_code < 0:
        return f"signal_{-exit_code}", f"checker terminated by signal {-exit_code}"
    stdout = Path(str(result["stdout"])).read_text(encoding="utf-8", errors="replace")
    stderr = Path(str(result["stderr"])).read_text(encoding="utf-8", errors="replace")
    combined = stdout + "\n" + stderr
    code = re.search(r"(?:error|warning)\[([^]]+)\]", combined, re.IGNORECASE)
    if code:
        family = code.group(1).upper()
    elif "SSpec" in combined and ("guidance" in combined.lower() or "expect" in combined):
        family = "sspec_guidance"
    elif re.search(r"unexpected (?:token|character)", combined, re.IGNORECASE):
        family = "parser_unexpected_token"
    elif re.search(r"\bexpected\b", combined, re.IGNORECASE):
        family = "parser_expected_form"
    elif re.search(r"\.spl:\s*check failed", combined):
        family = "parser_error_without_diagnostic"
    elif "file not found" in combined.lower():
        family = "file_not_found"
    else:
        family = f"exit_{exit_code}_unclassified"

    first = ""
    for raw in combined.splitlines():
        line = raw.strip()
        if not line or line.startswith("All checks passed") or "error(s) found" in line:
            continue
        line = re.sub(r"^[^:]+\.spl(?::\d+){0,2}:?\s*", "<source>: ", line)
        line = re.sub(r"\bline \d+\b", "line <n>", line, flags=re.IGNORECASE)
        first = line[:500]
        break
    return family, first or f"checker exited {exit_code} without a diagnostic line"


def run_tasks(
    checker: Path,
    tasks: list[tuple[str, list[dict[str, str]], Path]],
    workers: int,
    timeout_s: float,
    resume: bool,
    max_rss_kib: int = 0,
    rss_interval_s: float = 2.0,
) -> dict[str, dict[str, object]]:
    results: dict[str, dict[str, object]] = {}
    pending = []
    for task_id, rows, stem in tasks:
        result_path = stem.with_suffix(".result.json")
        if resume and result_path.is_file():
            results[task_id] = json.loads(result_path.read_text(encoding="utf-8"))
        else:
            pending.append((task_id, rows, stem))
    with ThreadPoolExecutor(max_workers=workers) as pool:
        future_to_id = {
            pool.submit(run_checker, checker, rows, stem, timeout_s, max_rss_kib, rss_interval_s): task_id
            for task_id, rows, stem in pending
        }
        stem_by_id = {task_id: stem for task_id, _, stem in pending}
        for future in as_completed(future_to_id):
            task_id = future_to_id[future]
            results[task_id] = future.result()
            write_json(stem_by_id[task_id].with_suffix(".result.json"), results[task_id])
    return results


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--checker", required=True)
    parser.add_argument("--root", action="append", dest="roots")
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument(
        "--max-rss-kib",
        type=int,
        default=0,
        help="kill a checker batch whose process tree exceeds this RSS (KiB); 0 disables the ceiling",
    )
    parser.add_argument(
        "--rss-interval-s",
        type=float,
        default=2.0,
        help="process-tree RSS sampling interval while a checker batch runs",
    )
    parser.add_argument("--max-files", type=int)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()

    try:
        checker = Path(args.checker).resolve()
        if not checker.is_file() or not os.access(checker, os.X_OK):
            raise ValueError(f"checker is not executable: {checker}")
        if not TIME_BIN.is_file():
            raise ValueError("/usr/bin/time is required")
        if args.workers < 1 or args.batch_size < 1 or args.timeout <= 0:
            raise ValueError("workers, batch size, and timeout must be positive")
        if args.max_rss_kib < 0:
            raise ValueError("--max-rss-kib must be >= 0 (0 disables the ceiling)")
        if args.rss_interval_s <= 0:
            raise ValueError("--rss-interval-s must be positive")
        rows = discover(args.roots or list(DEFAULT_ROOTS), args.max_files)
        output = Path(args.output_dir).resolve()
        if output.exists() and not args.resume:
            raise ValueError(f"output exists; pass --resume to reuse it: {output}")
        output.mkdir(parents=True, exist_ok=True)
        (output / "batch").mkdir(exist_ok=True)
        (output / "file").mkdir(exist_ok=True)

        manifest = manifest_text(rows)
        manifest_digest = sha256_text(manifest)
        manifest_path = output / "manifest.tsv"
        metadata_path = output / "run.json"
        metadata = {
            "schema_version": 1,
            "checker": str(checker),
            "checker_digest": sha256_file(checker),
            "repo_root": str(ROOT),
            "roots": args.roots or list(DEFAULT_ROOTS),
            "workers": args.workers,
            "batch_size": args.batch_size,
            "timeout_s": args.timeout,
            "max_rss_kib": args.max_rss_kib,
            "rss_interval_s": args.rss_interval_s,
            "manifest_digest": manifest_digest,
            "source_count": len(rows),
        }
        if args.resume and metadata_path.exists():
            previous = json.loads(metadata_path.read_text(encoding="utf-8"))
            for key in ("checker_digest", "manifest_digest", "batch_size"):
                if previous.get(key) != metadata[key]:
                    raise ValueError(f"resume mismatch for {key}")
        manifest_path.write_text(manifest, encoding="utf-8")
        write_json(metadata_path, metadata)

        batches = [rows[index : index + args.batch_size] for index in range(0, len(rows), args.batch_size)]
        batch_tasks = []
        for index, batch in enumerate(batches, 1):
            batch_id = f"batch-{index:06d}"
            batch_tasks.append((batch_id, batch, output / "batch" / batch_id))
        batch_results = run_tasks(checker, batch_tasks, args.workers, args.timeout, args.resume, args.max_rss_kib, args.rss_interval_s)
        with (output / "batch-results.jsonl").open("w", encoding="utf-8") as stream:
            for batch_id, _, _ in batch_tasks:
                stream.write(json.dumps({"batch_id": batch_id, **batch_results[batch_id]}, sort_keys=True) + "\n")

        failed_batches = [
            (batch_id, batch, stem)
            for batch_id, batch, stem in batch_tasks
            if batch_results[batch_id]["exit_code"] != 0
            or batch_results[batch_id]["timed_out"]
            or batch_results[batch_id]["rss_ceiling_exceeded"]
        ]
        isolate_tasks = []
        row_by_id = {row["id"]: row for row in rows}
        batch_by_id: dict[str, str] = {}
        for batch_id, batch, _ in batch_tasks:
            for row in batch:
                batch_by_id[row["id"]] = batch_id
        for _, batch, _ in failed_batches:
            for row in batch:
                isolate_tasks.append((row["id"], [row], output / "file" / row["id"]))
        isolated = (
            run_tasks(checker, isolate_tasks, args.workers, args.timeout, args.resume, args.max_rss_kib, args.rss_interval_s)
            if isolate_tasks
            else {}
        )

        file_results = []
        failed_batch_ids = {item[0] for item in failed_batches}
        for row in rows:
            batch_id = batch_by_id[row["id"]]
            if batch_id not in failed_batch_ids:
                file_results.append(
                    {
                        **row,
                        "batch_id": batch_id,
                        "status": "pass_in_batch",
                        "exit_code": 0,
                        "error_family": "none",
                        "diagnostic": "",
                        "classification": "not_applicable",
                    }
                )
                continue
            result = isolated[row["id"]]
            if (
                result["exit_code"] == 0
                and not result["timed_out"]
                and not result.get("rss_ceiling_exceeded", False)
            ):
                status = "pass_individual_after_failed_batch"
                family, diagnostic = "none", ""
                classification = "not_applicable"
            else:
                status = "fail_individual"
                family, diagnostic = diagnostic_family(result)
                classification = "needs_triage"
            file_results.append(
                {
                    **row,
                    "batch_id": batch_id,
                    "status": status,
                    "exit_code": result["exit_code"],
                    "error_family": family,
                    "diagnostic": diagnostic,
                    "classification": classification,
                    "stdout_digest": result["stdout_digest"],
                    "stderr_digest": result["stderr_digest"],
                }
            )

        with (output / "file-results.jsonl").open("w", encoding="utf-8") as stream:
            for row in file_results:
                stream.write(json.dumps(row, sort_keys=True) + "\n")
        failures = [row for row in file_results if row["status"] == "fail_individual"]
        isolated_passes = [
            row for row in file_results if row["status"] == "pass_individual_after_failed_batch"
        ]
        families = Counter(row["error_family"] for row in failures)
        classification_path = output / "failure-classification.tsv"
        with classification_path.open("w", encoding="utf-8") as stream:
            stream.write("id\tsource_digest\tpath\terror_family\tclassification\tdiagnostic\n")
            for row in failures:
                diagnostic = str(row["diagnostic"]).replace("\t", " ").replace("\n", " ")
                stream.write(
                    f"{row['id']}\t{row['source_digest']}\t{row['path']}\t"
                    f"{row['error_family']}\tneeds_triage\t{diagnostic}\n"
                )
        summary = {
            **metadata,
            "batch_count": len(batches),
            "failed_batch_count": len(failed_batches),
            "passed_files": len(rows) - len(failures),
            "failing_files": len(failures),
            "isolated_passes_from_failed_batches": len(isolated_passes),
            "error_families": dict(sorted(families.items())),
            "classification_file": str(classification_path),
            "complete_per_file_outcomes": len(file_results) == len(rows),
        }
        write_json(output / "summary.json", summary)
        print(json.dumps(summary, sort_keys=True))
        return 1 if failures or failed_batches else 0
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"compiled-check-tree: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

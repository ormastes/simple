#!/usr/bin/env python3
"""Finite native matched-app measurements; never bootstrap/ISA qualification."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def percentile(values, percent):
    return sorted(values)[math.ceil(len(values) * percent / 100) - 1]


def fields(path):
    return dict(line.split("=", 1) for line in path.read_text().splitlines() if "=" in line)


def stage_provider(source, output, expected_digest):
    """Keep the loader's existing relative build/providers/ admission policy."""
    relative = Path("build/providers") / ("matched-provider" + source.suffix)
    destination = output / relative
    destination.parent.mkdir(parents=True)
    shutil.copyfile(source, destination)
    if digest(destination) != expected_digest:
        raise ValueError("staged production provider hash mismatch")
    return relative, destination


def sample_record(path, kind, size, vector):
    if path.stat().st_size > 1024 * 1024:
        raise ValueError("app stdout exceeded 1 MiB")
    lines = path.read_text().splitlines()
    records = [line for line in lines if line.startswith("ITEM5_PERF_V1 ")]
    if len(records) != 1:
        raise ValueError("expected exactly one measured record after three warmups")
    pairs = [word.split("=", 1) for word in records[0].split()[1:]]
    record = dict(pairs)
    required = {"kind", "size", "operations", "ns", "checksum", "results", "provider_calls", "warmups"}
    if set(record) != required or len(pairs) != len(required):
        raise ValueError("missing, duplicate or unknown sample fields")
    if record["kind"] != kind:
        raise ValueError("wrong workload")
    for key in required - {"kind"}:
        record[key] = int(record[key])
        if record[key] < 0:
            raise ValueError("negative sample field")
    if record["size"] != size or record["operations"] != (32 if kind == "db" else 128):
        raise ValueError("wrong workload size or operation count")
    if record["warmups"] != 3 or record["ns"] <= 0:
        raise ValueError("invalid timing/warmup count")
    calls = record["provider_calls"]
    if (not vector and calls != 0) or (vector and calls <= 0):
        raise ValueError("missing vector calls or unexpected scalar provider use")
    if kind == "db" and vector and calls != 32:
        raise ValueError("DB query cache/fallback bypassed measured provider work")
    wires = [line.removeprefix("ITEM5_PERF_WIRE_V1 hex=") for line in lines
             if line.startswith("ITEM5_PERF_WIRE_V1 hex=")]
    if kind == "http":
        if len(wires) != 1:
            raise ValueError("missing complete HTTP wire result")
        wire = bytes.fromhex(wires[0])
        if not wire.startswith(b"HTTP/1.1 200") or not wire.endswith(b"ITEM5_MATCHED_HTTP_BODY"):
            raise ValueError("invalid HTTP response")
        record["wire_hex"] = wires[0]
    elif wires:
        raise ValueError("unexpected HTTP record in DB workload")
    return record


def host_metadata():
    def read(path):
        try:
            return Path(path).read_text().strip()
        except OSError as error:
            return "unavailable: " + str(error)
    governors = {str(p): read(p) for p in Path("/sys/devices/system/cpu/cpufreq").glob("policy*/scaling_governor")}
    return {"kernel": platform.uname()._asdict(), "cpuinfo": read("/proc/cpuinfo"),
            "loadavg": read("/proc/loadavg"), "meminfo": read("/proc/meminfo"),
            "governors": governors, "governor_scope": "unavailable" if not governors else "reported sysfs policies"}


def functional_gate(evidence_path, manifest):
    """Require completed canonical actual-app evidence; not hash-only admission."""
    e = fields(evidence_path)
    if e.get("schema") != "item5-app-vector-runner-v1" or e.get("qualification") != "execution-evidence-only":
        raise ValueError("canonical completed actual-app execution evidence required")
    bindings = {"producer_compiler_sha256": manifest["compiler"]["sha256"],
                "producer_source_commit": manifest["producer_source_commit"],
                "app_source_commit": manifest["functional_app_source_commit"],
                "provider_identity": str(manifest["provider_id"]),
                "implementation_identity": str(manifest["implementation_id"])}
    if any(e.get(key) != value for key, value in bindings.items()):
        raise ValueError("functional source/producer/provider binding mismatch")
    directory = evidence_path.parent
    hello = directory / "staged/producer-hello.json"
    if digest(hello) != e.get("producer_hello_receipt_sha256"):
        raise ValueError("functional producer receipt hash mismatch")
    h = json.loads(hello.read_text())
    if h.get("runtime_archive_sha256") != manifest["runtime"]["sha256"]:
        raise ValueError("functional runtime differs from measurement runtime")
    evidence_files = [evidence_path, hello]
    for role in ("db-scalar", "db-vector", "http-scalar", "http-vector"):
        receipt = directory / "receipts" / (role + ".rss.env")
        r = fields(receipt)
        if r.get("status") != "complete" or r.get("exit_status") != "0" or r.get("quiescent") != "1":
            raise ValueError("functional application was not successfully quiescent: " + role)
        evidence_files.append(receipt)
    return {str(p): digest(p) for p in evidence_files}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--samples", type=int, choices=(30, 100), default=30)
    p.add_argument("--timeout-seconds", type=int, default=1200)
    p.add_argument("--cohort-timeout-seconds", type=int, default=3600)
    p.add_argument("--max-rss-kib", type=int, default=1048576)
    a = p.parse_args()
    if not 1 <= a.timeout_seconds <= 1800 or not 1 <= a.max_rss_kib <= 5859375 or not 1 <= a.cohort_timeout_seconds <= 21600:
        p.error("invalid finite resource limit")
    m = json.loads(a.manifest.read_text())
    if m.get("schema") != "item5-matched-app-performance-v1" or m.get("mode") != "production":
        p.error("production benchmark manifest required; observer runs are separate")
    for key in ("app_source_commit", "app_source_tree", "producer_source_commit", "functional_app_source_commit"):
        value = m.get(key, "")
        if len(value) != 40 or any(c not in "0123456789abcdef" for c in value):
            p.error("invalid source identity: " + key)
    repository = Path(m["source_repository"]).resolve(strict=True)
    def git_object(revision):
        return subprocess.run(["git", "-C", str(repository), "rev-parse", revision],
                              check=True, capture_output=True, text=True, timeout=30).stdout.strip()
    if git_object(m["app_source_commit"] + "^{tree}") != m["app_source_tree"]:
        p.error("benchmark source tree does not match the actual commit")
    if git_object(m["app_source_commit"] + ":src") != git_object(m["functional_app_source_commit"] + ":src"):
        p.error("functional gate and benchmark must share identical production src tree")
    # Paths and hashes come from actual build provenance, never synthesized here.
    names = ("db_scalar", "db_vector", "http_scalar", "http_vector", "provider", "compiler", "runtime", "watchdog", "functional_evidence")
    inputs = {}
    for name in names:
        entry = m[name]
        path = Path(entry["path"]).resolve(strict=True)
        if not path.is_file() or digest(path) != entry["sha256"]:
            p.error("input hash mismatch: " + name)
        inputs[name] = path
    functional_hashes = functional_gate(inputs["functional_evidence"], m)
    symbols = subprocess.run(["nm", "-D", "--undefined-only", str(inputs["provider"])],
                             check=True, capture_output=True, text=True, timeout=30).stdout
    if "simple_vector_test_" in symbols:
        p.error("instrumented provider is not a production timing artifact")
    out = a.output.resolve()
    out.mkdir(exist_ok=False)
    provider_argument, staged_provider = stage_provider(inputs["provider"], out, m["provider"]["sha256"])
    (out / "manifest.json").write_text(json.dumps(m, indent=2) + "\n")
    (out / "scope.txt").write_text("Matched native application timings; no ISA, release or bootstrap admission.\n")
    (out / "host-before.json").write_text(json.dumps(host_metadata(), indent=2) + "\n")
    tools = [Path(__file__).resolve(), Path(sys.executable).resolve(), inputs["watchdog"]]
    tools.extend(Path(shutil.which(name)).resolve() for name in ("perl", "nm", "git"))
    tool_hashes = {str(path): digest(path) for path in tools}
    (out / "tools.json").write_text(json.dumps(tool_hashes, indent=2) + "\n")
    (out / "functional-evidence.json").write_text(json.dumps(functional_hashes, indent=2) + "\n")
    env = os.environ.copy()
    for key in tuple(env):
        if key in ("LD_PRELOAD", "LD_AUDIT", "LD_LIBRARY_PATH") or key.startswith("SIMPLE_VECTOR_TEST_"):
            del env[key]
    samples = []
    started = time.monotonic()
    terminal = {"status": "failed", "completed_samples": 0}
    try:
        for kind, size in (("db", 1025), ("db", 65536), ("http", 128)):
            for pair in range(a.samples):
                order = ("scalar", "vector") if pair % 2 == 0 else ("vector", "scalar")
                compared = {}
                for lane in order:
                    remaining = a.cohort_timeout_seconds - int(time.monotonic() - started)
                    if remaining <= 0:
                        raise RuntimeError("finite cohort time budget exhausted; partial samples retained")
                    role = kind + "_" + lane
                    run = out / f"{kind}-{size}-{pair:03d}-{lane}"
                    run.mkdir()
                    app = [str(inputs[role])]
                    if kind == "db":
                        app.append(str(size))
                    if lane == "vector":
                        app += [provider_argument.as_posix(), m["provider"]["sha256"]]
                        if kind == "db":
                            app += [str(m["provider_id"]), str(m["implementation_id"])]
                    cmd = ["perl", str(inputs["watchdog"]), f"--max-rss-kib={a.max_rss_kib}",
                           "--rss-cap-mode=enforce", f"--timeout-seconds={min(a.timeout_seconds, remaining)}",
                           f"--receipt={run / 'rss.env'}", "--", *app]
                    (run / "command.json").write_text(json.dumps(cmd) + "\n")
                    with (run / "stdout").open("wb") as stdout, (run / "stderr").open("wb") as stderr:
                        result = subprocess.run(cmd, stdout=stdout, stderr=stderr, env=env, cwd=out)
                    receipt = fields(run / "rss.env")
                    if result.returncode or receipt.get("quiescent") != "1" or receipt.get("exit_status") != "0" or receipt.get("status") != "complete":
                        raise RuntimeError("sample failed or watchdog not quiescent: " + str(run))
                    record = sample_record(run / "stdout", kind, size, lane == "vector")
                    record.update(lane=lane, pair=pair, order=list(order),
                                  max_process_rss_kib=int(receipt["peak_rss_kib"]))
                    samples.append(record)
                    compared[lane] = record
                    with (out / "samples.jsonl").open("a") as stream:
                        stream.write(json.dumps(record) + "\n")
                    terminal["completed_samples"] += 1
                for key in ("checksum", "results", "operations", "wire_hex"):
                    if compared["scalar"].get(key) != compared["vector"].get(key):
                        raise RuntimeError("matched workload result mismatch: " + key)
        for name in names:
            if digest(inputs[name]) != m[name]["sha256"]:
                raise RuntimeError("input changed during cohort: " + name)
        if digest(staged_provider) != m["provider"]["sha256"]:
            raise RuntimeError("staged production provider changed during cohort")
        for path, expected in {**tool_hashes, **functional_hashes}.items():
            if digest(path) != expected:
                raise RuntimeError("tool or functional evidence changed during cohort: " + path)
        summaries = []
        for kind, size in (("db", 1025), ("db", 65536), ("http", 128)):
            lanes = {}
            for lane in ("scalar", "vector"):
                rows = [r for r in samples if (r["kind"], r["size"], r["lane"]) == (kind, size, lane)]
                values = [r["ns"] for r in rows]
                lanes[lane] = {"samples": len(rows), "p50_ns": percentile(values, 50),
                               "p95_ns": percentile(values, 95),
                               "max_startup_inclusive_process_rss_kib": max(r["max_process_rss_kib"] for r in rows)}
            ratios = []
            for pair in range(a.samples):
                rows = {r["lane"]: r for r in samples if (r["kind"], r["size"], r["pair"]) == (kind, size, pair)}
                ratios.append(rows["vector"]["ns"] / rows["scalar"]["ns"])
            summaries.append({"kind": kind, "size": size, "lanes": lanes,
                              "paired_vector_over_scalar_p50": percentile(ratios, 50),
                              "paired_vector_over_scalar_p95": percentile(ratios, 95)})
        (out / "summary.json").write_text(json.dumps(summaries, indent=2) + "\n")
        terminal["status"] = "measurements-complete"
        terminal["provider_call_evidence"] = "Simple owner reports; independent instrumented ISA proof required"
    finally:
        (out / "host-after.json").write_text(json.dumps(host_metadata(), indent=2) + "\n")
        terminal["wall_seconds_including_setup"] = time.monotonic() - started
        (out / "terminal.json").write_text(json.dumps(terminal, indent=2) + "\n")


if __name__ == "__main__":
    main()

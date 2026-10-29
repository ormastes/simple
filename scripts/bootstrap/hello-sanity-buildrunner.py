"""Production BuildRunner Hello adapter. Missing providers are never passes.

The provider consists of the manager, canonical manifest writer and a qualified
local-worker template. Each invocation owns its own state and published output.
"""
from pathlib import Path
import os
import re
import shutil


def verified_memory_receipt(state, receipt, output, artifact, limit):
    """Bind the worker's memory receipt to the manager's verified result."""
    lines = receipt.read_text().splitlines()
    if len(lines) != 13 or lines[0:2] != ["SIMPLE-BUILD-RESULT-1", "hello"]:
        raise ValueError("invalid BuildRunner result receipt")
    attempt, identity, host, status, exit_code = lines[2:7]
    if not re.fullmatch(r"[1-9][0-9]*", attempt) or not re.fullmatch(r"[0-9a-f]{64}", identity):
        raise ValueError("invalid result identity")
    if not re.fullmatch(r"[A-Za-z0-9_-]+", host) or status != "OK" or exit_code != "0":
        raise ValueError("invalid result owner or status")
    if lines[10] != "1" or lines[11] != output or lines[12] != matrix_digest(artifact):
        raise ValueError("result does not bind the published executable")
    memory = state / "attempts" / "hello" / attempt / host / "compiler.memory"
    if not memory.is_file():
        raise ValueError("worker memory receipt missing")
    fields = {}
    for line in memory.read_text().splitlines():
        if "=" not in line:
            raise ValueError("malformed worker memory receipt")
        key, value = line.split("=", 1)
        if key in fields:
            raise ValueError("duplicate worker memory receipt field")
        fields[key] = value
    expected = {"format", "task_identity", "requested_policy", "reserved_bytes",
                "enforcement", "enforced_bytes", "observed_peak_bytes", "peak_metric"}
    if set(fields) != expected or fields["format"] != "simple-build-memory-v1" or fields["task_identity"] != identity:
        raise ValueError("memory receipt identity or format mismatch")
    metrics = {"job-memory": "job-commit-peak", "cgroup-memory-max": "cgroup-memory-peak"}
    if fields["requested_policy"] != "enforce" or fields["reserved_bytes"] != str(limit) or fields["enforced_bytes"] != str(limit) or metrics.get(fields["enforcement"]) != fields["peak_metric"]:
        raise ValueError("worker did not prove the requested memory enforcement")
    if not re.fullmatch(r"0|[1-9][0-9]*", fields["observed_peak_bytes"]):
        raise ValueError("invalid worker memory peak")
    return memory


def run_one_source(matrix, backend, manager, manifest_writer, template, target):
    """Run and verify a one-source compiler task through the production manager."""
    lane = matrix.out / ("buildrunner-" + backend + "-one-source")
    lane.mkdir()
    values = {"phase": matrix.args.phase, "backend": backend,
              "compiler_sha256": matrix.sha, "status": "FAIL"}
    try:
        pinned = {Path(path): matrix_digest(path) for path in (manager, manifest_writer, template)}
        source = lane / "source"
        source.mkdir()
        (source / "src").mkdir()
        fixture = matrix.root / "test/fixtures/bootstrap/hello_sanity_matrix/single.spl"
        shutil.copyfile(fixture, source / "src/main.spl")
        shutil.copytree(matrix.runtime, source / "runtime", symlinks=False)
        paths = sorted((p.relative_to(source).as_posix() for p in source.rglob("*")
                        if p.is_file()), key=str.lower)
        if not paths or len({p.lower() for p in paths}) != len(paths):
            raise ValueError("invalid or ambiguous BuildRunner input inventory")
        (source / "inputs.txt").write_text("".join(p + "\n" for p in paths))
        (source / "links.txt").write_text("")
        manifest = lane / "manifest.sdn"
        state = lane / "state"
        published = lane / "published"
        output = "hello.exe" if os.name == "nt" else "hello"
        cmd = [manifest_writer, "--job-from-inventory", template, matrix.compiler,
               source, "hello", "sanity", output, "inputs.txt",
               "--memory-limit-bytes", str(matrix.args.max_rss_kib * 1024),
               "--links-inventory", "links.txt", "--work-timeout-ms",
               str(matrix.args.timeout_seconds * 1000), "--manifest", manifest,
               "--", "native-build", "--source", "src", "--entry", "src/main.spl",
               "--entry-closure", "--target", target, "--backend", backend,
               "--runtime-path", "runtime", "--runtime-bundle", "core-c-bootstrap",
               "--threads", "1", "--output", output]
        matrix.run(lane, "manifest", cmd)
        args = ["--manifest", manifest, "--state", state, "--source-root", source,
                "--output-root", published]
        matrix.run(lane, "manager-run", [manager, "run", *args])
        out, _ = matrix.run(lane, "manager-verify", [manager, "verify", *args])
        if b"builder: verified tasks=1" not in out:
            raise ValueError("manager did not verify the expected task")
        receipt = state / "receipts/hello.sdn"
        artifact = published / output
        if not receipt.is_file() or not artifact.is_file() or not artifact.stat().st_size:
            raise ValueError("verified receipt or published executable missing")
        verified_memory_receipt(state, receipt, output, artifact, matrix.args.max_rss_kib * 1024)
        matrix.check_executable(lane, artifact)
        if any(matrix_digest(path) != sha for path, sha in pinned.items()):
            raise ValueError("BuildRunner provider identity changed during execution")
        values.update(status="PASS", executable_sha256=matrix_digest(artifact),
                      receipt_sha256=matrix_digest(receipt),
                      manager_sha256=pinned[Path(manager)],
                      manifest_writer_sha256=pinned[Path(manifest_writer)],
                      template_sha256=pinned[Path(template)])
    except Exception as error:
        values["reason"] = str(error)
    return values


def matrix_digest(path):
    import hashlib
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

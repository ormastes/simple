"""Production BuildRunner Hello adapter. Missing providers are never passes.

The provider consists of the manager, canonical manifest writer and a qualified
local-worker template. Each invocation owns its own state and published output.
"""
from pathlib import Path
import os
import re
import shutil


MEMORY_POLICIES = ("enforce", "monitor")
MONITOR_PEAK_METRICS = ("process-tree-peak", "child-rss-peak")
MONITOR_VERDICT = "functional-only BuildRunner hello (monitor policy; memory qualification deferred)"


def lane_status(policy):
    """Only enforce evidence may carry the qualified PASS marker."""
    if policy == "enforce":
        return "PASS"
    if policy == "monitor":
        return "FUNCTIONAL"
    raise ValueError("unknown memory policy")


def verified_memory_receipt(state, receipt, output, artifact, limit, policy="enforce"):
    """Bind the worker's memory receipt to the manager's verified result.

    policy "enforce" requires kernel-enforced memory. policy "monitor" is the
    opt-in functional-only mode for hosts without enforcement; it never proves
    memory qualification.
    """
    if policy not in MEMORY_POLICIES:
        raise ValueError("unknown memory policy")
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
    if policy == "monitor":
        if fields["requested_policy"] == "enforce" or fields["enforcement"] != "none" or fields["enforced_bytes"] != "0":
            raise ValueError("monitor receipt claims enforcement it did not request")
        if fields["requested_policy"] != "monitor" or fields["reserved_bytes"] != str(limit):
            raise ValueError("worker did not prove the requested memory monitoring")
        if fields["peak_metric"] not in MONITOR_PEAK_METRICS:
            raise ValueError("monitor receipt peak metric is not monitor-only")
        if not re.fullmatch(r"0|[1-9][0-9]*", fields["observed_peak_bytes"]):
            raise ValueError("invalid worker memory peak")
        return memory
    metrics = {"job-memory": "job-commit-peak", "cgroup-memory-max": "cgroup-memory-peak"}
    if fields["requested_policy"] != "enforce" or fields["reserved_bytes"] != str(limit) or fields["enforced_bytes"] != str(limit) or metrics.get(fields["enforcement"]) != fields["peak_metric"]:
        raise ValueError("worker did not prove the requested memory enforcement")
    if not re.fullmatch(r"0|[1-9][0-9]*", fields["observed_peak_bytes"]):
        raise ValueError("invalid worker memory peak")
    return memory


def unpack_verified_lane(bundle, destination, expected):
    """Read only flat, bounded artifacts from a manager-verified task output."""
    import ast
    import stat
    import zipfile
    with zipfile.ZipFile(bundle) as archive:
        members = archive.infolist()
        names = [item.filename for item in members]
        if len(names) != len(set(names)) or len(names) > 128:
            raise ValueError("ambiguous or oversized worker bundle")
        if sum(item.file_size for item in members) > 128 * 1024 * 1024:
            raise ValueError("worker bundle exceeds extraction budget")
        for item in members:
            mode = item.external_attr >> 16
            if (not re.fullmatch(r"[A-Za-z0-9_.-]+", item.filename) or
                    item.filename in {".", ".."} or item.is_dir() or
                    (stat.S_IFMT(mode) and not stat.S_ISREG(mode))):
                raise ValueError("unsafe worker bundle member")
        def member(name):
            try:
                return archive.read(name)
            except KeyError as error:
                raise ValueError("worker bundle member missing") from error
        def record(name):
            fields = {}
            for line in member(name).decode().splitlines():
                if ": " not in line:
                    raise ValueError("malformed worker evidence record")
                key, value = line.split(": ", 1)
                if key in fields:
                    raise ValueError("duplicate worker evidence field")
                try:
                    fields[key] = value if value in {"true", "false"} else ast.literal_eval(value)
                except (SyntaxError, TypeError, MemoryError, RecursionError) as error:
                    raise ValueError("malformed worker evidence record") from error
            return fields
        identity = record("managed-lane.sdn")
        if identity != expected:
            raise ValueError("managed lane identity mismatch")
        result = record("result.sdn")
        if (result.get("status") != "PASS" or
                any(result.get(key) != expected[key] for key in
                    ("phase", "compiler_sha256", "compile_route"))):
            raise ValueError("managed lane did not pass with exact producer")
        executable = "hello.exe" if os.name == "nt" else "hello"
        import hashlib
        if hashlib.sha256(member(executable)).hexdigest() != result.get("executable_sha256"):
            raise ValueError("worker executable identity mismatch")
        destination.mkdir()
        archive.extractall(destination)
    artifact = destination / executable
    artifact.chmod(artifact.stat().st_mode | 0o100)
    return artifact


def run_lane(matrix, backend, name, manager, manifest_writer, template, target):
    """Dispatch compile, explicit link and execution within one enforced task."""
    import sys
    lane = matrix.out / ("buildrunner-" + backend + "-" + name)
    lane.mkdir()
    policy = getattr(matrix.args, "memory_policy", "enforce")
    # manifest_main.spl parses --memory-policy only before --manifest; under
    # enforce the argv is emitted exactly as before.
    policy_argv = ["--memory-policy", "monitor"] if policy == "monitor" else []
    values = {"phase": matrix.args.phase, "backend": backend, "lane": name,
              "compile_route": matrix.args.compile_route,
              "compiler_sha256": matrix.sha, "status": "FAIL", "admitted": False}
    try:
        if name not in ("one-source", "two-objects", "static-library", "shared-library"):
            raise ValueError("unsupported Hello form")
        # The existing matrix's platform-specific link captures are native-host
        # evidence. A cross target must not be silently relabeled as native.
        import platform
        machine = platform.machine().lower()
        architecture = "aarch64" if machine in {"arm64", "aarch64"} else "x86_64" if machine in {"amd64", "x86_64"} else machine
        host = "windows" if os.name == "nt" else "darwin" if sys.platform == "darwin" else "linux"
        suffixes = {"darwin": {"darwin", "apple-darwin", "macos"},
                    "linux": {"linux", "linux-gnu", "unknown-linux-gnu"},
                    "windows": {"windows", "pc-windows-msvc"} if matrix.args.windows_abi == "msvc"
                    else {"windows-gnu", "pc-windows-gnu"}}
        if target not in {architecture + "-" + suffix for suffix in suffixes[host]}:
            raise ValueError("BuildRunner target differs from native linkage host")
        producer = Path(sys.executable).resolve()
        pinned = {Path(path): matrix_digest(path) for path in (manager, manifest_writer, template, producer)}
        source = lane / "source"
        source.mkdir()
        for relative in (
                "scripts/bootstrap/hello-sanity-buildrunner-worker.py",
                "scripts/bootstrap/hello-sanity-matrix.py",
                "scripts/bootstrap/hello-sanity-matrix-darwin.py",
                "scripts/bootstrap/hello-sanity-matrix-windows.py",
                "scripts/bootstrap/run-process-group-bounded-log-windows.py",
                "scripts/bootstrap/bootstrap-session-exec.c",
                "scripts/resource/macos-process-observer.c",
                "scripts/resource/macos-observer-denial-policy.h",
                "scripts/resource/process-tree-rss-watchdog.pl"):
            destination = source / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(matrix.root / relative, destination)
        fixtures = Path("test/fixtures/bootstrap/hello_sanity_matrix")
        shutil.copytree(matrix.root / fixtures, source / fixtures)
        shutil.copyfile(matrix.compiler, source / ("compiler.exe" if os.name == "nt" else "compiler"))
        for relative, expected_hash in matrix.runtime_hashes.items():
            destination = source / "runtime" / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(matrix.runtime / relative, destination)
            if matrix_digest(destination) != expected_hash:
                raise ValueError("runtime authority changed during staging")
        if matrix_digest(source / ("compiler.exe" if os.name == "nt" else "compiler")) != matrix.sha:
            raise ValueError("compiler changed during staging")
        paths = sorted((p.relative_to(source).as_posix() for p in source.rglob("*")
                        if p.is_file()), key=str.lower)
        if not paths or len({p.lower() for p in paths}) != len(paths):
            raise ValueError("invalid or ambiguous BuildRunner input inventory")
        (source / "inputs.txt").write_text("".join(p + "\n" for p in paths))
        (source / "links.txt").write_text("")
        manifest, state, published = lane / "manifest.sdn", lane / "state", lane / "published"
        output = "hello-result.zip"
        # A form has up to eight sequential commands. The worker retains each
        # per-command bound; the production owner also caps the complete task.
        task_seconds = matrix.args.timeout_seconds * 8 + 30
        cmd = [manifest_writer, "--job-from-inventory", template, producer,
               source, "hello", "sanity", output, "inputs.txt",
               "--memory-limit-bytes", str(matrix.args.max_rss_kib * 1024),
               "--links-inventory", "links.txt", "--work-timeout-ms",
               str(task_seconds * 1000), *policy_argv, "--manifest", manifest, "--",
               "scripts/bootstrap/hello-sanity-buildrunner-worker.py",
               "--backend", backend, "--lane", name, "--phase", str(matrix.args.phase),
               "--target", target,
               "--compile-route", matrix.args.compile_route, "--compiler-sha256", matrix.sha,
               "--timeout-seconds", str(matrix.args.timeout_seconds),
               "--max-rss-kib", str(matrix.args.max_rss_kib),
               "--min-free-disk-bytes", str(matrix.args.min_free_disk_bytes),
               "--max-log-bytes", str(matrix.args.max_log_bytes),
               "--linker", str(matrix.linker), "--windows-abi", matrix.args.windows_abi,
               "--output", output]
        if getattr(matrix.args, "trace_stages", False):
            cmd.append("--trace-stages")
        matrix.run(lane, "manifest", cmd)
        args = ["--manifest", manifest, "--state", state, "--source-root", source,
                "--output-root", published]
        trace_args = ["--trace-stages"] if getattr(matrix.args, "trace_stages", False) else []
        matrix.run(lane, "manager-run", [manager, "run", *args, *trace_args], seconds=task_seconds + 30)
        out, _ = matrix.run(lane, "manager-verify", [manager, "verify", *args])
        if b"builder: verified tasks=1" not in out:
            raise ValueError("manager did not verify the expected task")
        receipt, bundle = state / "receipts/hello.sdn", published / output
        if not receipt.is_file() or not bundle.is_file() or not bundle.stat().st_size:
            raise ValueError("verified receipt or published bundle missing")
        memory = verified_memory_receipt(state, receipt, output, bundle, matrix.args.max_rss_kib * 1024, policy)
        artifact = unpack_verified_lane(bundle, lane / "verified", {
            "format": "hello-buildrunner-lane-v1", "lane": name, "backend": backend,
            "phase": matrix.args.phase, "compile_route": matrix.args.compile_route,
            "compiler_sha256": matrix.sha, "status": "PASS", "admitted": "false"})
        matrix.check_executable(lane, artifact)
        if any(matrix_digest(path) != sha for path, sha in pinned.items()):
            raise ValueError("BuildRunner provider identity changed during execution")
        values.update(status=lane_status(policy), executable_sha256=matrix_digest(artifact),
                      receipt_sha256=matrix_digest(receipt), memory_receipt_sha256=matrix_digest(memory),
                      bundle_sha256=matrix_digest(bundle), python_sha256=pinned[producer],
                      manager_sha256=pinned[Path(manager)],
                      manifest_writer_sha256=pinned[Path(manifest_writer)],
                      template_sha256=pinned[Path(template)])
        if policy == "monitor":
            values.update(memory_policy="monitor", evidence_scope="functional-only-memory-deferred",
                          verdict=MONITOR_VERDICT)
            print(MONITOR_VERDICT, flush=True)
    except Exception as error:
        values["reason"] = str(error)
    return values


def run_one_source(matrix, backend, manager, manifest_writer, template, target):
    return run_lane(matrix, backend, "one-source", manager, manifest_writer, template, target)


def matrix_digest(path):
    import hashlib
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

#!/usr/bin/env python3
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
CONFIG_PATH = REPO_ROOT / "scripts" / "mcp_performance_guard_config.json"


def load_config():
    return json.loads(CONFIG_PATH.read_text())


def rel(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def read_text(path: Path) -> str:
    return path.read_text() if path.exists() else ""


def parse_args():
    parser = argparse.ArgumentParser(
        description="MCP performance guard: static audit, perf smoke, and verify."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    for name in ("static-audit", "perf-smoke", "verify"):
        sub = subparsers.add_parser(name)
        sub.add_argument("--context", default="manual")
        sub.add_argument("--strict", action="store_true")

    return parser.parse_args()


def print_section(title: str):
    print(f"\n== {title} ==")


def parse_elapsed_ms(raw: str) -> float:
    raw = raw.strip()
    parts = raw.split(":")
    if len(parts) == 2:
        minutes = int(parts[0])
        seconds = float(parts[1])
        return (minutes * 60.0 + seconds) * 1000.0
    if len(parts) == 3:
        hours = int(parts[0])
        minutes = int(parts[1])
        seconds = float(parts[2])
        return (hours * 3600.0 + minutes * 60.0 + seconds) * 1000.0
    raise ValueError(f"unsupported elapsed format: {raw}")


def load_mcp_json(config):
    path = REPO_ROOT / config["wrapper_config"]["mcp_json"]
    return json.loads(path.read_text())


def audit_wrapper_config(config, errors, warnings):
    mcp_json = load_mcp_json(config)
    servers = mcp_json.get("mcpServers", {})
    expected_servers = config["wrapper_config"]["expected_servers"]
    print_section("Wrapper Config Audit")
    for name, expected in expected_servers.items():
        actual = servers.get(name)
        if actual is None:
            errors.append(f"missing MCP server entry `{name}` in .mcp.json")
            continue
        actual_command = actual.get("command")
        actual_args = actual.get("args", [])
        if actual_command != expected["command"]:
            errors.append(
                f"{name} command drifted: expected `{expected['command']}`, got `{actual_command}`"
            )
        if actual_args != expected["args"]:
            errors.append(
                f"{name} args drifted: expected {expected['args']}, got {actual_args}"
            )
        launch_text = " ".join([actual_command] + actual_args)
        if "bin/simple run " in launch_text or launch_text.endswith(".spl"):
            errors.append(f"{name} launches raw source instead of cached wrapper: `{launch_text}`")
        print(f"{name}: command={actual_command} args={actual_args}")


def audit_wrapper_files(config, errors, warnings):
    print_section("Wrapper File Audit")
    for rule in config["wrapper_files"]:
        path = REPO_ROOT / rule["path"]
        content = read_text(path)
        if not content:
            errors.append(f"missing wrapper file `{rule['path']}`")
            continue
        for needle in rule.get("must_contain", []):
            if needle not in content:
                errors.append(f"{rule['path']} missing required wrapper pattern `{needle}`")
        for needle in rule.get("must_not_contain", []):
            if needle in content:
                errors.append(f"{rule['path']} contains forbidden source-launch pattern `{needle}`")
        print(f"{rule['path']}: checked")


def iter_unique_files(globs):
    seen = set()
    for pattern in globs:
        for path in REPO_ROOT.glob(pattern):
            if path.is_file() and path not in seen:
                seen.add(path)
                yield path


def audit_handler_patterns(config, errors, warnings):
    print_section("Hot Path Audit")
    for path in iter_unique_files(config["handler_scan_globs"]):
        content = read_text(path)
        for pattern in config["forbidden_scan_patterns"]:
            if pattern in content:
                errors.append(f"{rel(path)} contains forbidden full-scan primitive `{pattern}`")
    for path in iter_unique_files(config["handler_shell_subprocess_globs"]):
        content = read_text(path)
        for pattern in config["forbidden_shell_subprocess_patterns"]:
            if pattern in content:
                errors.append(f"{rel(path)} contains forbidden shell subprocess `{pattern}`")
    print("handler modules scanned for direct full scans and shell subprocesses")


def audit_invalidation(config, errors, warnings):
    print_section("Invalidation Audit")
    for rule in config["mutation_invalidation"]:
        path = REPO_ROOT / rule["path"]
        content = read_text(path)
        symbol = rule["required_symbol"]
        if symbol not in content:
            errors.append(f"{rule['path']} is missing invalidation symbol `{symbol}`")
        else:
            print(f"{rule['path']}: invalidation present")


def build_base_env():
    env = os.environ.copy()
    env.setdefault("SIMPLE_LOG", "error")
    env.setdefault("RUST_LOG", "error")
    env.setdefault("OBSIDIAN_VAULT_PATH", "")
    return env


def parse_time_v(stderr_text: str):
    wall = None
    rss_kb = None
    for line in stderr_text.splitlines():
        if "Elapsed (wall clock) time" in line:
            wall = line.split(": ", 1)[1].strip()
        elif "Maximum resident set size" in line:
            rss_kb = int(line.split(":", 1)[1].strip())
    if wall is None or rss_kb is None:
        raise RuntimeError("failed to parse `/usr/bin/time -v` output")
    return parse_elapsed_ms(wall), rss_kb / 1024.0


def measure_startup(check):
    env = build_base_env()
    cmd = check["command"]
    subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        env=env,
        input=b"",
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    proc = subprocess.run(
        ["/usr/bin/time", "-v", *cmd],
        cwd=REPO_ROOT,
        env=env,
        input=b"",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    elapsed_ms, rss_mb = parse_time_v(proc.stderr.decode("utf-8", "replace"))
    return {
        "returncode": proc.returncode,
        "elapsed_ms": elapsed_ms,
        "rss_mb": rss_mb,
    }


def materialize_fixture_vault(check):
    source = REPO_ROOT / check["fixture_vault"]
    workdir = Path(tempfile.mkdtemp(prefix="obsidian-perf-vault-"))
    shutil.copytree(source, workdir / "vault", dirs_exist_ok=True)
    vault = workdir / "vault"
    seed_files = sorted(vault.rglob("*.md"))
    copy_count = int(check.get("fixture_copies", 0))
    for i in range(copy_count):
        seed = seed_files[i % len(seed_files)]
        stem = seed.stem
        target = seed.with_name(f"{stem}-copy-{i:03d}.md")
        content = seed.read_text()
        content = content.replace("[[", "[[")
        target.write_text(content + f"\n\nreplica: {i}\n")
    return workdir, vault


def run_obsidian_request(check):
    temp_root, vault = materialize_fixture_vault(check)
    env = build_base_env()
    env["OBSIDIAN_VAULT_PATH"] = str(vault)
    payload = "\n".join(
        [
            json.dumps(
                {
                    "jsonrpc": "2.0",
                    "id": 1,
                    "method": "initialize",
                    "params": {
                        "protocolVersion": "2025-06-18",
                        "capabilities": {},
                        "clientInfo": {"name": "mcp-perf-guard", "version": "1"},
                    },
                }
            ),
            json.dumps(
                {
                    "jsonrpc": "2.0",
                    "id": 2,
                    "method": "tools/call",
                    "params": {
                        "name": "search_vault",
                        "arguments": {"query": "perf", "limit": 10, "mode": "full"},
                    },
                }
            ),
            json.dumps({"jsonrpc": "2.0", "id": 3, "method": "shutdown", "params": {}}),
            "",
        ]
    )
    started = time.perf_counter()
    proc = subprocess.run(
        check["command"],
        cwd=REPO_ROOT,
        env=env,
        input=payload.encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=10,
    )
    elapsed_ms = (time.perf_counter() - started) * 1000.0
    shutil.rmtree(temp_root, ignore_errors=True)
    return {
        "returncode": proc.returncode,
        "elapsed_ms": elapsed_ms,
        "stdout": proc.stdout.decode("utf-8", "replace"),
        "stderr": proc.stderr.decode("utf-8", "replace"),
    }


def run_static_audit(config, strict=False, context="manual"):
    errors = []
    warnings = []
    print(f"MCP static audit context: {context}")
    audit_wrapper_config(config, errors, warnings)
    audit_wrapper_files(config, errors, warnings)
    audit_handler_patterns(config, errors, warnings)
    audit_invalidation(config, errors, warnings)
    print_section("Static Audit Result")
    if warnings:
        for warning in warnings:
            print(f"WARN: {warning}")
    if errors:
        for error in errors:
            print(f"FAIL: {error}")
        return 1
    print("PASS: no static MCP performance violations found")
    return 0


def run_perf_smoke(config, strict=False, context="manual"):
    print(f"MCP perf smoke context: {context}")
    failures = []

    print_section("Warm Startup Checks")
    for check in config["startup_checks"]:
        result = measure_startup(check)
        print(
            f"{check['name']}: {result['elapsed_ms']:.2f} ms, {result['rss_mb']:.2f} MB RSS, rc={result['returncode']}"
        )
        if result["returncode"] != 0:
            failures.append(f"{check['name']} exited with rc={result['returncode']}")
            continue
        if result["elapsed_ms"] > check["budget_ms"]:
            failures.append(
                f"{check['name']} startup exceeded budget: {result['elapsed_ms']:.2f} ms > {check['budget_ms']:.2f} ms"
            )
        if result["rss_mb"] > check["budget_rss_mb"]:
            failures.append(
                f"{check['name']} RSS exceeded budget: {result['rss_mb']:.2f} MB > {check['budget_rss_mb']:.2f} MB"
            )

    print_section("Representative Request Checks")
    for check in config["request_checks"]:
        result = run_obsidian_request(check)
        print(
            f"{check['name']}: {result['elapsed_ms']:.2f} ms, rc={result['returncode']}, stdout_bytes={len(result['stdout'])}"
        )
        if result["returncode"] != 0:
            failures.append(f"{check['name']} exited with rc={result['returncode']}")
            continue
        if result["elapsed_ms"] > check["budget_ms"]:
            failures.append(
                f"{check['name']} request exceeded budget: {result['elapsed_ms']:.2f} ms > {check['budget_ms']:.2f} ms"
            )

    print_section("Perf Smoke Result")
    if failures:
        for failure in failures:
            print(f"FAIL: {failure}")
        return 1
    print("PASS: startup and request budgets are within threshold")
    return 0


def git_changed_files():
    proc = subprocess.run(
        ["git", "status", "--short"],
        cwd=REPO_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.decode("utf-8", "replace"))
    changed = []
    for raw_line in proc.stdout.decode("utf-8", "replace").splitlines():
        line = raw_line.rstrip()
        if not line:
            continue
        path = line[3:]
        if " -> " in path:
            path = path.split(" -> ", 1)[1]
        changed.append(path)
    return changed


def doc_has_required_headings(path: Path, required_headings):
    content = read_text(path)
    missing = []
    for heading in required_headings:
        if heading not in content:
            missing.append(heading)
    return missing


def run_doc_traceability(config):
    print_section("Doc Traceability")
    changed = git_changed_files()
    doc_config = config["doc_traceability"]
    relevant = [
        path
        for path in changed
        if any(path.startswith(prefix) for prefix in doc_config["relevant_prefixes"])
    ]
    if not relevant:
        print("no MCP/tooling changes detected in worktree")
        return 0

    changed_docs = [
        path
        for path in changed
        if any(path.startswith(prefix) for prefix in doc_config["doc_prefixes"])
    ]
    print("relevant changed files:")
    for path in relevant:
        print(f"- {path}")
    if not changed_docs:
        print("FAIL: MCP/tooling changes are missing companion plan/architecture/design docs")
        return 1

    failures = []
    for doc_path in changed_docs:
        path = REPO_ROOT / doc_path
        missing = doc_has_required_headings(path, doc_config["required_headings"])
        if not missing:
            print(f"{doc_path}: headings present")
            return 0
        failures.append((doc_path, missing))

    for doc_path, missing in failures:
        print(f"FAIL: {doc_path} missing headings: {', '.join(missing)}")
    return 1


def run_verify(config, strict=False, context="manual"):
    print(f"MCP verify context: {context}")
    static_rc = run_static_audit(config, strict=True, context=context)
    perf_rc = run_perf_smoke(config, strict=True, context=context)
    doc_rc = run_doc_traceability(config)
    print_section("Verify Result")
    if static_rc == 0 and perf_rc == 0 and doc_rc == 0:
        print("STATUS: PASS")
        return 0
    print("STATUS: FAIL")
    return 1


def main():
    args = parse_args()
    config = load_config()
    if args.command == "static-audit":
        return run_static_audit(config, strict=args.strict, context=args.context)
    if args.command == "perf-smoke":
        return run_perf_smoke(config, strict=args.strict, context=args.context)
    if args.command == "verify":
        return run_verify(config, strict=args.strict, context=args.context)
    raise AssertionError(f"unknown command: {args.command}")


if __name__ == "__main__":
    sys.exit(main())

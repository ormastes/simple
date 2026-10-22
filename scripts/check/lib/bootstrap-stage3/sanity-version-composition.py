#!/usr/bin/python3
"""Closed remaining-version owner. No native compile or green-control replay.

The profile is an actual pre-owner capture, authenticated by its reviewed hash.
Owner code is a separate finite overlay, never labelled original build input.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

PROFILE_SHA = "44f1c7bf2a12ccebd3b8aa237cbc46ad729d1007c1ae7477ec9bbe57db54aac6"
PROFILE_NAME = "cranelift-aarch64-core-c-rc1-version-only-v1"
OWNER_PATHS = {
    "scripts/check/lib/bootstrap-stage3/sanity.shs",
    "scripts/check/lib/bootstrap-stage3/sanity-version-composition.py",
    "scripts/bootstrap/resume-stage2-version-admission.shs",
    "scripts/bootstrap/phase2-runtime-binding.shs",
    "scripts/bootstrap/lib/verify-stage2-compiler-tests.shs",
    "test/01_unit/scripts/bootstrap_version_composition_spec.spl",
}
MANDATORY_OWNER_PATHS = OWNER_PATHS - {"test/01_unit/scripts/bootstrap_version_composition_spec.spl"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def regular(path, maximum=128 * 1024 * 1024):
    path = Path(path)
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode), f"nonregular authority: {path}")
    require(before.st_size <= maximum, f"authority exceeds bound: {path}")
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        opened = os.fstat(fd)
        require((opened.st_dev, opened.st_ino) == (before.st_dev, before.st_ino), "authority replaced on open")
        data = bytearray()
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                break
            data.extend(chunk)
            require(len(data) <= maximum, "authority grew past bound")
        after = os.fstat(fd)
    finally:
        os.close(fd)
    identity = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
    require(identity(opened) == identity(after) == identity(path.lstat()), "authority changed while reading")
    return bytes(data)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def env_record(path):
    result = {}
    for line in regular(path, 1024 * 1024).decode().splitlines():
        key, value = line.split("=", 1)
        require(key not in result, f"duplicate receipt key: {key}")
        result[key] = value
    return result


def pinned(path, expected):
    data = regular(path)
    require(sha(data) == expected, f"authority digest differs: {path}")
    return data


def profile(path):
    value = json.loads(pinned(path, PROFILE_SHA))
    require(value["profile"] == PROFILE_NAME, "unsupported composition profile")
    return value


def history(value, candidate):
    history_root = Path(value["history"])
    for role in ["stage2-sanity.env", "stage2-command.transcript", "source-inputs-before.txt",
                 "git-state-before.env", "runtime-admitted.txt", "tool-authority-before.txt"]:
        pinned(history_root / role, value[role])
    require(sha(regular(candidate)) == value["candidate_sha256"], "candidate differs from actual successful native build")
    old = env_record(history_root / "stage2-sanity.env")
    expected = {
        "schema": "simple-bootstrap-sanity-evidence-v1", "status": "error",
        "candidate_sha256_before": value["candidate_sha256"],
        "candidate_sha256_after": value["candidate_sha256"], "sha_stable_status": "0",
        "version_status": "0", "version_output": "simple-bootstrap " + value["expected_version"],
        "version_expected": "", "version_expect_status": "1", "version_match_status": "1",
        "unsupported_status": "1", "unsupported_match_status": "0",
        "frontend_smoke_status": "0", "frontend_smoke_backend": "cranelift",
        "frontend_smoke_bootstrap_mode_status": "0", "frontend_smoke_bootstrap0_raw_status": "0",
        "frontend_smoke_bootstrap1_raw_status": "0", "frontend_smoke_bootstrap1_ran": "true",
        "checks_run": "0",
    }
    for key, expected_value in expected.items():
        require(old.get(key) == expected_value, f"original history is not version-only failure: {key}")
    watcher = history_root.parent.parent / "root-refresh-watchdog.env"
    pinned(watcher, value["root_watchdog_sha256"])
    observed = env_record(watcher)
    require(observed["quiescent"] == "1" and observed["exit_status"] == "1", "original execution cleanup differs")
    for mode in [0, 1]:
        prefix = f"frontend_smoke_bootstrap{mode}"
        status_path = history_root / Path(old[prefix + "_status_path"]).name
        log_path = history_root / Path(old[prefix + "_log_path"]).name
        pinned(status_path, old[prefix + "_status_sha256"])
        pinned(log_path, old[prefix + "_log_sha256"])
        status = env_record(status_path)
        for key, expected_value in [("result", "pass"), ("probe", "complete"),
                                    ("raw_status", "0"), ("bootstrap_mode", str(mode)), ("backend", "cranelift")]:
            require(status[key] == expected_value, f"original frontend group differs: {mode}/{key}")
        require(status["log_path"] == str(log_path), "frontend group is not original canonical path")
        probes = ["p2_add", "stage2_mir_retention", "stage2_module_path_naming", "hello_world_positional"]
        if mode == 0:
            probes.append("scv_prime")
        else:
            for suffix in ["raw_status", "log_path", "log_sha256", "collector_receipt_path", "collector_receipt_sha256"]:
                require(status["scv_prime_" + suffix] == ("not-run" if suffix == "raw_status" else "-"), "bootstrap1 SCV prime must remain explicit not-run")
        for probe in probes:
            require(status[probe + "_raw_status"] == "0", "original frontend criterion failed")
            probe_path = Path(status[probe + "_log_path"])
            receipt_path = Path(status[probe + "_collector_receipt_path"])
            require(probe_path.parent == history_root and receipt_path == Path(str(probe_path) + ".bounded.env"), "frontend artifact escapes history")
            log_bytes = pinned(probe_path, status[probe + "_log_sha256"])
            pinned(receipt_path, status[probe + "_collector_receipt_sha256"])
            receipt = env_record(receipt_path)
            for key, expected_value in [("schema", "simple-bounded-process-log-v1"), ("status", "complete"),
                                        ("reason", "child-exit"), ("raw_status", "0"),
                                        ("combined_stream", "stdout-stderr"), ("process_group", "setpgid"),
                                        ("artifact_limit", "none"), ("log_leaf", probe_path.name),
                                        ("log_sha256", sha(log_bytes)), ("bytes_captured", str(len(log_bytes)))]:
                require(receipt[key] == expected_value, f"original bounded criterion differs: {probe}/{key}")
            require(0 < len(log_bytes) <= int(receipt["max_bytes"]), "criterion log is empty/truncated")
    return old


def snapshot_members(data):
    result = {}
    for line in data.decode().splitlines():
        if line.startswith("file-hex:"):
            fields = line.split(":")
            require(len(fields) == 5, "source record layout differs")
            path = bytes.fromhex(fields[2]).decode()
            require(len(path.encode()) == int(fields[1]) and path not in result, "duplicate/invalid source member")
            result[path] = line
    return result


def envelope(value, root, source, git, runtime, tools, owner_manifest, owner_sha):
    original = pinned(Path(value["history"]) / "source-inputs-before.txt", value["source-inputs-before.txt"])
    current = regular(source)
    expected_git = pinned(Path(value["baseline_directory"]) / "git-before-owner-files.json", value["baseline_git_files_sha256"])
    baseline = json.loads(expected_git)
    allowed = {}
    if owner_manifest:
        authority = json.loads(pinned(owner_manifest, owner_sha))
        require(authority["schema"] == "bootstrap-version-owner-code-v1", "owner code schema differs")
        require(authority["profile_sha256"] == PROFILE_SHA, "owner code profile differs")
        require(authority["baseline_git_files_sha256"] == value["baseline_git_files_sha256"], "owner code origin differs")
        interpreter = Path(sys.executable).resolve(strict=True)
        require(str(interpreter) == authority["python_interpreter_path"], "reviewed owner interpreter path changed")
        require(sha(regular(interpreter)) == authority["python_interpreter_sha256"], "reviewed owner interpreter bytes changed")
        allowed = authority["members"]
        require(set(allowed) <= OWNER_PATHS and MANDATORY_OWNER_PATHS <= set(allowed), "mandatory owner code overlay members missing")
        for path, digest in allowed.items():
            require(sha(regular(Path(root) / path)) == digest, f"reviewed owner code changed: {path}")
            require((Path(root) / path).stat().st_mode & 0o111 == 0, f"owner code execution mode differs: {path}")
    elif current != original:
        raise ValueError("source changed without separate reviewed owner code")
    origin_members = snapshot_members(original)
    current_members = snapshot_members(current)
    projected = []
    for line in current.decode().splitlines():
        path = None
        if line.startswith("file-hex:"):
            path = bytes.fromhex(line.split(":")[2]).decode()
        if path in allowed:
            require(line.split(":")[-1] == allowed[path], "source snapshot owner member differs")
            if path in origin_members:
                projected.append(origin_members[path])
        else:
            projected.append(line)
    require(sha(("\n".join(sorted(projected)) + "\n").encode()) == value["source-inputs-before.txt"], "non-owner original source membership/content changed")
    for path in MANDATORY_OWNER_PATHS & set(allowed):
        require(path in current_members, f"reviewed owner member missing from source capture: {path}")
    # Dirty-file membership/body identities are a separately observed pre-owner
    # baseline. Only the exact reviewed control overlay may change afterward.
    require(subprocess.check_output(["git", "-C", root, "rev-parse", "HEAD"], text=True).strip() == baseline["head"], "head changed after actual native build")
    raw = subprocess.check_output(["git", "-C", root, "status", "--porcelain=v1", "-z", "--untracked-files=all"])
    before = {entry["path"]: entry for entry in baseline["entries"]}
    current_dirty = {}
    for item in raw.split(b"\0"):
        if not item:
            continue
        state, path = item[:2].decode(), item[3:].decode()
        require("R" not in state and "C" not in state, "rename/copy in original qualification tree")
        current_dirty[path] = {"status": state, "path": path, "sha256": sha(regular(Path(root) / path))}
    require(set(current_dirty) - set(allowed) == set(before) - set(allowed), "unreviewed Git membership changed")
    for path in set(before) - set(allowed):
        require(current_dirty[path] == before[path], f"unreviewed dirty input changed: {path}")
    if not allowed:
        require(sha(regular(git)) == value["git-state-before.env"], "Git state changed")
    require(sha(regular(runtime)) == value["runtime-admitted.txt"], "runtime changed")
    require(sha(regular(tools)) == value["tool-authority-before.txt"], "tool authority changed")
    require(sha(regular(Path(root) / "release/version.sdn")) == value["metadata_sha256"], "restored canonical version metadata changed")


def verify_composition(args, value):
    composition = env_record(args.composition)
    require(composition["schema"] == "simple-bootstrap-sanity-version-composition-v1", "composition schema differs")
    for key, expected in [("profile", PROFILE_NAME), ("status", "pass"),
                          ("candidate_sha256", value["candidate_sha256"]),
                          ("prior_sanity_sha256", value["stage2-sanity.env"]),
                          ("source_snapshot_sha256", value["source-inputs-before.txt"]),
                          ("runtime_snapshot_sha256", value["runtime-admitted.txt"]),
                          ("tool_snapshot_sha256", value["tool-authority-before.txt"]),
                          ("build_args_sha256", value["build_args_sha256"]),
                          ("retained_checks", "4"), ("remaining_checks", "1"), ("checks_run", "5")]:
        require(composition[key] == expected, f"composition field differs: {key}")
    control = Path(composition["version_component_path"])
    require(control == Path(str(args.composition) + ".version.env"), "noncanonical version component path")
    pinned(control, composition["version_component_sha256"])
    observed = env_record(control)
    for key, expected in [("schema", "simple-bootstrap-version-remaining-control-v1"),
                          ("canonical_version", value["expected_version"]), ("version_match_status", "0"),
                          ("candidate_sha256_before", value["candidate_sha256"]),
                          ("candidate_sha256_after", value["candidate_sha256"]),
                          ("retained_version_status", "0"),
                          ("retained_version_output", "simple-bootstrap " + value["expected_version"]),
                          ("prior_sanity_sha256", value["stage2-sanity.env"]),
                          ("metadata_control_raw_status", "0"),
                          ("metadata_sha256", value["metadata_sha256"]),
                          ("owner_manifest_sha256", args.owner_sha),
                              ("collector_sha256", sha(regular(Path(args.root) / "scripts/bootstrap/run-process-group-bounded-log.pl"))),
                              ("controller_sha256", sha(regular(Path(args.root) / "scripts/bootstrap/resume-stage2-version-admission.shs")))]:
        require(observed[key] == expected, f"remaining version control differs: {key}")
    require(composition["owner_manifest_path"] == args.owner_manifest and composition["owner_manifest_sha256"] == args.owner_sha, "composition owner code differs")
    log = Path(observed["metadata_control_log_path"])
    receipt_path = Path(observed["metadata_control_receipt_path"])
    require(log == Path(str(args.composition) + ".metadata.log") and receipt_path == Path(str(log) + ".bounded.env"), "metadata control output path differs")
    output = pinned(log, observed["metadata_control_log_sha256"])
    require(output == (value["expected_version"] + "\n").encode(), "metadata control actual stdout differs")
    pinned(receipt_path, observed["metadata_control_receipt_sha256"])
    receipt = env_record(receipt_path)
    for key, expected in [("schema", "simple-bounded-process-log-v1"), ("status", "complete"),
                          ("reason", "child-exit"), ("raw_status", "0"), ("bytes_captured", str(len(output))),
                          ("log_leaf", log.name), ("log_sha256", sha(output)),
                          ("combined_stream", "stdout-stderr"), ("artifact_limit", "none")]:
        require(receipt[key] == expected, f"metadata bounded control differs: {key}")
    require(receipt["process_group"] in ["setsid", "setpgid"], "metadata control has no canonical POSIX process owner")
    require(int(receipt["timeout_seconds"]) == 30 and int(receipt["max_bytes"]) == 65536, "metadata control resource bounds differ")
    for boundary in ["before", "after"]:
        base = Path(composition["envelope_" + boundary + "_base"])
        for role in ["source", "git", "runtime", "tools"]:
            require(sha(regular(Path(str(base) + "." + role))) == composition["envelope_" + boundary + "_" + role + "_sha256"], f"collected {boundary} envelope changed: {role}")
        envelope(value, args.root, str(base) + ".source", str(base) + ".git", str(base) + ".runtime", str(base) + ".tools", args.owner_manifest, args.owner_sha)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("operation", choices=["audit", "verify"])
    parser.add_argument("--profile", required=True)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--root", required=True)
    parser.add_argument("--source", required=True)
    parser.add_argument("--git", required=True)
    parser.add_argument("--runtime", required=True)
    parser.add_argument("--tools", required=True)
    parser.add_argument("--owner-manifest")
    parser.add_argument("--owner-sha", default="")
    parser.add_argument("--composition")
    args = parser.parse_args()
    value = profile(args.profile)
    history(value, args.candidate)
    envelope(value, args.root, args.source, args.git, args.runtime, args.tools, args.owner_manifest, args.owner_sha)
    if args.operation == "verify":
        verify_composition(args, value)
    print("remaining-version-owner: original controls authenticated; no native build or green replay")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, UnicodeError, json.JSONDecodeError) as error:
        print(f"remaining-version-owner-error: {error}", file=sys.stderr)
        sys.exit(1)

#!/usr/bin/env python3
"""Check retained native diagnostic evidence; never claim the wrapper A/B passed."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import re

OWNERS = (
    "src/lib/nogc_sync_mut/io/file_ops.spl",
    "src/compiler/80.driver/driver_aot_native_output.spl",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def native_path(value):
    return re.sub(r"^/([A-Za-z])/", r"\1:/", value)


def receipt(path):
    return dict(line.split("=", 1) for line in Path(path).read_text().splitlines() if "=" in line)


def recovery_errors(result, log):
    errors = []
    if result["exit"] != 1 or result["timeout"]:
        errors.append("not a completed rejected compile")
    if "AOT compile error in " not in log or "llc failed (exit 1):" not in log:
        errors.append("missing recovered provider failure")
    if "error: redefinition of global" not in log:
        errors.append("missing concrete LLVM diagnostic")
    if any(marker in log for marker in ("backend object-path status", "diagnostic file empty", "diagnostic unreadable")):
        errors.append("opaque or unreadable diagnostic")
    if not (0 < result["elapsed_s"] <= 90 and 0 < result["peak_sampled_tree_rss_bytes"] < 512 * 1024 * 1024):
        errors.append("focused diagnostic evidence exceeds budget")
    return errors


def controls(result, log):
    mutations = []
    for key, value in (("exit", 0), ("timeout", True), ("peak_sampled_tree_rss_bytes", 512 * 1024 * 1024)):
        changed = copy.deepcopy(result)
        changed[key] = value
        mutations.append((changed, log))
    mutations.append((result, log.replace("error: redefinition of global", "redacted")))
    mutations.append((result, log + "\nbackend object-path status 1 (diagnostic file empty)"))
    require(all(recovery_errors(item, text) for item, text in mutations), "negative control accepted")
    return len(mutations)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--admission", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    result = json.loads((args.evidence / "capsule-build.json").read_text())
    log = (args.evidence / "capsule-build.log").read_text()
    admission = receipt(args.admission)
    require(admission["status"] == "admitted", "candidate is not admitted")
    candidate = result["command"][0]
    require(digest(candidate) == result["runtime_sha256"] == admission["candidate_sha256"], "candidate hash mismatch")
    for name in ("source_snapshot", "runtime_snapshot", "tool_authority", "sanity_evidence"):
        require(digest(native_path(admission[name + "_path"])) == admission[name + "_sha256"], name + " hash mismatch")
    snapshot = Path(native_path(admission["source_snapshot_path"])).read_text().splitlines()
    for owner in OWNERS:
        rows = [line.split(":")[-1] for line in snapshot if owner.encode().hex() in line]
        require(rows == [digest(root / owner)], owner + " source mismatch")
    errors = recovery_errors(result, log)
    require(not errors, str(errors))
    count = controls(result, log)
    print(json.dumps({"status": "PASS", "scope": "retained Windows x86_64 LLVM driver diagnostic recovery only", "negative_controls_rejected": count, "wrapper_native_ab": "pending", "log_sha256": digest(args.evidence / "capsule-build.log"), "candidate_sha256": digest(candidate)}))


if __name__ == "__main__":
    main()

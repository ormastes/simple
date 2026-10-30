#!/usr/bin/env python3
"""Exercise the FreeBSD command telemetry wrapper with controlled tools only."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


REPO = Path(__file__).resolve().parents[3]
WRAPPER = REPO / "scripts/bootstrap/lib/freebsd-command-telemetry.shs"
UTILS = ("mkdir", "awk", "cat", "rm", "grep")


def write_script(path, body):
    path.write_text(body, encoding="utf-8", newline="\n")
    path.chmod(0o755)


def fixture(root, telemetry, timeout_present=True):
    root.mkdir(parents=True)
    fakebin = root / "bin"
    fakebin.mkdir()
    for name in UTILS:
        source = shutil.which(name)
        assert source, "missing host fixture utility: " + name
        (fakebin / name).symlink_to(source)
    write_script(fakebin / "date", """#!/bin/sh
echo 1700000000
""")
    if timeout_present:
        write_script(fakebin / "timeout", """#!/bin/sh
set -eu
[ "$1" = -k ] && [ "$2" = 1 ] && [ "$3" = 5 ]
shift 3
exec "$@"
""")
    if telemetry:
        write_script(fakebin / "dmesg", """#!/bin/sh
set -eu
if [ "$TELEMETRY_MODE" = fail ]; then echo 'fixture dmesg denied' >&2; exit 9; fi
i=0
while [ "$i" -lt 85 ]; do printf 'kernel-%02d\\n' "$i"; i=$((i + 1)); done
""")
        write_script(fakebin / "sysctl", """#!/bin/sh
set -eu
if [ "$TELEMETRY_MODE" = fail ]; then echo 'fixture sysctl denied' >&2; exit 9; fi
case "$2" in
  hw.physmem) echo 12884901888 ;;
  hw.pagesize) echo 4096 ;;
  vm.stats.vm.v_free_count) echo 12345 ;;
  vm.stats.vm.v_inactive_count) echo 23456 ;;
  *) exit 2 ;;
esac
""")
        write_script(fakebin / "swapinfo", """#!/bin/sh
set -eu
if [ "$TELEMETRY_MODE" = fail ]; then echo 'fixture swapinfo denied' >&2; exit 9; fi
printf 'Device 1M Used 0M Avail 1M Capacity 0%%\\n'
""")
    write_script(root / "command", """#!/bin/sh
set -eu
[ "$#" -eq 2 ] && [ "$1" = 'arg with space' ] && [ "$2" = kept ]
printf x >> "$FIXTURE_ROOT/invocations"
printf 'known stdout\\n'
printf 'known stderr\\n' >&2
exit "$FIXTURE_EXIT"
""")
    env = os.environ.copy()
    env.update(PATH=str(fakebin), FIXTURE_ROOT=str(root),
               FIXTURE_EXIT="0", TELEMETRY_MODE="ok")
    return env


def read_fields(path):
    fields = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        key, value = line.split(": ", 1)
        assert key not in fields, "duplicate telemetry field: " + key
        fields[key] = value
    return fields


def run(root, env, evidence):
    command = ["/bin/sh", str(WRAPPER), str(evidence), "--",
               str(root / "command"), "arg with space", "kept"]
    return subprocess.run(command, cwd=root, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=30)


def check_available(root):
    env = fixture(root, telemetry=True)
    evidence = root / "evidence"
    result = run(root, env, evidence)
    assert result.returncode == 0, (result.returncode, result.stderr)
    assert result.stdout == b"known stdout\n"
    assert result.stderr == b"known stderr\n"
    assert (root / "invocations").read_text() == "x"
    fields = read_fields(evidence / "command-telemetry.sdn")
    assert fields["command_exit_status"] == "0"
    assert fields["before_dmesg_status"] == "available"
    assert fields["after_dmesg_status"] == "available"
    assert fields["before_dmesg_truncated"] == "true"
    lines = (evidence / "before_dmesg.log").read_text().splitlines()
    assert len(lines) == 80 and lines[0] == "kernel-05" and lines[-1] == "kernel-84"
    for prefix in ("before", "after"):
        assert fields[prefix + "_sysctl_hw_physmem_status"] == "available"
        assert fields[prefix + "_sysctl_hw_pagesize_status"] == "available"
        assert fields[prefix + "_sysctl_vm_free_count_status"] == "available"
        assert fields[prefix + "_sysctl_vm_inactive_count_status"] == "available"
        assert fields[prefix + "_swapinfo_status"] == "available"
        assert fields[prefix + "_timestamp_status"] == "available"
    assert fields["timestamp_semantics"] == "observational-only"
    assert fields["peak_scope"] == "single-command-rusage-not-process-tree-peak"
    assert "oom" not in (evidence / "command-telemetry.sdn").read_text().lower()
    if fields["peak_status"] == "available":
        assert fields["peak_unit"] == "KiB"
        assert (evidence / "command-peak-rusage.txt").is_file()
    else:
        assert fields["peak_unit"] == "unavailable"
    return "available-telemetry"


def check_failing_telemetry_and_137(root):
    env = fixture(root, telemetry=True)
    env["FIXTURE_EXIT"] = "137"
    env["TELEMETRY_MODE"] = "fail"
    evidence = root / "evidence"
    result = run(root, env, evidence)
    assert result.returncode == 137, (result.returncode, result.stderr)
    assert result.stdout == b"known stdout\n"
    assert result.stderr == b"known stderr\n"
    assert (root / "invocations").read_text() == "x"
    fields = read_fields(evidence / "command-telemetry.sdn")
    assert fields["command_exit_status"] == "137"
    assert fields["before_dmesg_status"] == "unavailable"
    assert fields["before_dmesg_reason"] == "command-failed"
    assert fields["after_sysctl_hw_physmem_status"] == "unavailable"
    assert fields["after_swapinfo_status"] == "unavailable"
    assert "oom" not in (evidence / "command-telemetry.sdn").read_text().lower()
    return "failed-telemetry-preserves-137"


def check_missing_timeout(root):
    env = fixture(root, telemetry=False, timeout_present=False)
    env["FIXTURE_EXIT"] = "0"
    evidence = root / "evidence"
    result = run(root, env, evidence)
    assert result.returncode == 0, (result.returncode, result.stderr)
    assert result.stdout == b"known stdout\n"
    assert result.stderr == b"known stderr\n"
    assert (root / "invocations").read_text() == "x"
    fields = read_fields(evidence / "command-telemetry.sdn")
    assert fields["command_exit_status"] == "0"
    assert fields["before_dmesg_status"] == "unavailable"
    assert fields["before_dmesg_reason"] == "timeout-tool-unavailable"
    assert fields["after_swapinfo_status"] == "unavailable"
    assert fields["after_swapinfo_reason"] == "timeout-tool-unavailable"
    assert "oom" not in (evidence / "command-telemetry.sdn").read_text().lower()
    return "missing-timeout-preserves-command"


def check_receipt_storage_failure(root):
    env = fixture(root, telemetry=False)
    env["FIXTURE_EXIT"] = "137"
    evidence = root / "evidence-is-a-file"
    evidence.write_text("cannot be evidence directory\n", encoding="utf-8")
    result = run(root, env, evidence)
    assert result.returncode == 137, (result.returncode, result.stderr)
    assert result.stdout == b"known stdout\n"
    assert b"known stderr\n" in result.stderr
    assert b"evidence storage unavailable" in result.stderr
    assert (root / "invocations").read_text() == "x"
    return "receipt-storage-failure-preserves-137"


def check_receipt_truncate_failure(root):
    env = fixture(root, telemetry=False)
    env["FIXTURE_EXIT"] = "137"
    evidence = root / "evidence"
    evidence.mkdir()
    (evidence / "command-telemetry.sdn").mkdir()
    result = run(root, env, evidence)
    assert result.returncode == 137, (result.returncode, result.stderr)
    assert result.stdout == b"known stdout\n"
    assert b"known stderr\n" in result.stderr
    assert b"evidence storage unavailable" in result.stderr
    assert (root / "invocations").read_text() == "x"
    return "receipt-truncate-failure-preserves-137"


def main():
    base = Path(tempfile.mkdtemp(prefix="freebsd-command-telemetry-"))
    print("evidence=" + str(base), flush=True)
    workflow = (REPO / ".github/workflows/phase-ladder-rung.yml").read_text(encoding="utf-8")
    assert "sh scripts/bootstrap/lib/freebsd-command-telemetry.shs build/ladder/evidence -- \\" in workflow
    assert 'echo "$rc" > build/ladder/rc' in workflow
    cases = [
        ("available", check_available),
        ("failed", check_failing_telemetry_and_137),
        ("missing-timeout", check_missing_timeout),
        ("storage-failure", check_receipt_storage_failure),
        ("receipt-truncate-failure", check_receipt_truncate_failure),
    ]
    for name, check in cases:
        print("PASS " + check(base / name), flush=True)
    print("PASS: 5 command/telemetry controls; no FreeBSD or compiler qualification")


if __name__ == "__main__":
    main()

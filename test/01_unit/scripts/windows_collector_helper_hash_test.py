#!/usr/bin/env python3
"""Actual producer/consumer hash contract; Windows process launch is separate."""
import ast
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import SimpleNamespace

repo = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parents[3]
wrapper = (repo / "scripts/bootstrap/bootstrap-logged-process.shs").read_text()
helper = repo / "scripts/bootstrap/run-process-group-bounded-log-windows.py"
source = helper.read_text()
assignment = next(line.strip() for line in wrapper.splitlines() if line.strip().startswith("blwc_helper_sha="))
assert 'sha256sum <"$blwc_helper"' in assignment, "production producer must hash stdin"
legacy = assignment.replace('sha256sum <"$blwc_helper"', 'sha256sum "$blwc_helper"')
ns = {"__name__": "contract_fixture", "__file__": str(helper)}
exec(compile(source, str(helper), "exec"), ns)
main = next(n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef) and n.name == "main")
guards = [n for n in ast.walk(main) if isinstance(n, ast.If) and any(isinstance(x, ast.Raise) and isinstance(x.exc, ast.Call) and x.exc.args and isinstance(x.exc.args[0], ast.Constant) and x.exc.args[0].value == "collector helper hash mismatch" for x in n.body)]
assert len(guards) == 1, "actual helper hash admission guard must exist once"
guard = compile(ast.fix_missing_locations(ast.Module(body=guards, type_ignores=[])), str(helper), "exec")

def admit(path, supplied):
    scope = dict(ns, helper=path, args=SimpleNamespace(helper_sha256=supplied))
    try:
        exec(guard, scope)
        return True
    except RuntimeError as error:
        assert str(error) == "collector helper hash mismatch"
        return False

def produce(line, path):
    result = subprocess.run(["sh", "-c", 'blwc_helper=$1\n' + line + '\nprintf "%s" "$blwc_helper_sha"', "probe", str(path)], capture_output=True, text=True, check=True)
    return result.stdout

with tempfile.TemporaryDirectory(prefix="simple-hash-contract-") as directory:
    path = Path(directory) / "repo\\windows\\collector.py"
    path.write_bytes(helper.read_bytes())
    bad = produce(legacy, path)
    assert bad.startswith("\\") and not admit(path, bad), "named GNU filename escape must reproduce guard rejection"
    good = produce(assignment, path)
    assert re.fullmatch("[0-9a-f]{64}", good) and good == hashlib.sha256(path.read_bytes()).hexdigest()
    assert admit(path, good), "actual helper digest must admit unchanged bytes"
    assert not admit(path, "0" * 64), "wrong digest must remain rejected"
    assert not admit(path, good + "x"), "malformed digest must remain rejected"
    authored = good
    path.write_bytes(path.read_bytes().replace(b"\r\n", b"\n").replace(b"\n", b"\r\n"))
    eol = produce(assignment, path)
    assert eol != authored, "EOL distinction must not be hidden"
    assert not admit(path, authored), "authored digest must reject changed CRLF bytes"
    assert admit(path, eol), "producer and actual consumer must hash the same CRLF bytes"
print("Windows collector actual hash contract: 7 assertions PASS; native launch UNEXECUTED")

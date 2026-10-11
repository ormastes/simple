#!/usr/bin/env python3
"""Exercise production sanity dispatch and subprocess argv, not printed commands."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
OWNER = ROOT / "scripts/bootstrap/run-reviewed-native-sanity.shs"

with tempfile.TemporaryDirectory(prefix="reviewed-native-argv-") as temporary:
    root = Path(temporary)
    scripts = root / "scripts"
    scripts.mkdir()
    owner = scripts / OWNER.name
    shutil.copyfile(OWNER, owner)
    source = root / "repo/src/app/simple_lsp_mcp/main.spl"
    source.parent.mkdir(parents=True)
    source.write_text('val SERVER_NAME = "simple-lsp-mcp"\nval SERVER_VERSION = "0.9.8"\n')
    capture = root / "captured-argv.json"
    # The fixture accepts exactly the server's launcher-sensitive CLI forms.
    fixture = '''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
Path(os.environ["CAPTURE_ARGV"]).write_text(json.dumps(sys.argv))
canonical = Path(sys.argv[0]).name == "simple_lsp_mcp_server"
expected = ["--version"] if canonical else ["simple_lsp_mcp_server", "--version"]
if sys.argv[1:] != expected:
    sys.exit(17)
print("simple-lsp-mcp 0.9.8")
'''
    # Replace only the process-resource owner. The production reviewed harness
    # still selects argv, reads literal expectations and checks binary/source hashes.
    wrapper = scripts / "run-native-sanity.shs"
    wrapper.write_text('''#!/bin/sh
exec python3 "$(dirname -- "$0")/observe.py" "$@"
''')
    (scripts / "observe.py").write_text('''import pathlib, subprocess, sys
repo, out, expected_out, expected_err, expected_exit = sys.argv[1:6]
p = subprocess.run(sys.argv[6:], capture_output=True)
directory = pathlib.Path(out); directory.mkdir()
ok = (p.returncode == int(expected_exit) and p.stdout == pathlib.Path(expected_out).read_bytes()
      and p.stderr == pathlib.Path(expected_err).read_bytes())
(directory / "sanity.env").write_text("status=" + ("PASS" if ok else "FAIL") + "\\n")
sys.exit(0 if ok else 86)
''')
    env = os.environ.copy()
    env["CAPTURE_ARGV"] = str(capture)
    for name, expected in [
        ("simple_lsp_mcp_server", ["--version"]),
        ("renamed-lsp-artifact", ["simple_lsp_mcp_server", "--version"]),
    ]:
        binary = root / name
        binary.write_text(fixture)
        binary.chmod(0o755)
        result = subprocess.run(["sh", str(owner), str(root / "repo"),
                                 str(root / (name + "-receipt")), "lsp_build", str(binary)],
                                env=env, capture_output=True)
        assert result.returncode == 0, result.stderr + result.stdout
        assert json.loads(capture.read_text()) == [str(binary)] + expected
    # MCP has no reviewed LSP version contract. It must remain unqualified and
    # must not be accidentally invoked with an LSP selector or oracle.
    capture.unlink()
    mcp = root / "simple_mcp_server"
    mcp.write_text(fixture)
    mcp.chmod(0o755)
    result = subprocess.run(["sh", str(owner), str(root / "repo"),
                             str(root / "mcp-receipt"), "mcp_build", str(mcp)],
                            env=env, capture_output=True)
    assert result.returncode == 2
    assert b"no-reviewed-native-sanity-contract" in result.stderr
    assert not capture.exists(), "unqualified MCP role was actually invoked"

print("PASS: canonical LSP argv, renamed selector, MCP unqualified without invocation")

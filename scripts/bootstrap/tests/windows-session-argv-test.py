#!/usr/bin/env python3
"""Exercise literal argv through the real Windows Job guard and MSYS shell."""
import argparse
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--cc", required=True)
parser.add_argument("--output-root", required=True, type=Path)
parser.add_argument("--source-root", type=Path, default=Path(__file__).resolve().parents[3])
parser.add_argument("--consumer", choices=("native", "msys"), default="native")
args = parser.parse_args()
if os.name != "nt":
    raise SystemExit("UNSUPPORTED: actual Windows Job execution required")
root = args.source_root.resolve()
output = args.output_root.resolve()
output.mkdir(parents=True, exist_ok=False)
values = ["", r"C:\one\two", r"\\?\D:\long\path", r"\\server\share\file",
          r"one\\two", "C:\\space path\\trailing\\", "two trailing\\\\",
          'quote"and\\slash', 'slashes\\\\"quote', "single'quote",
          "*?[abc]", "$(printf not-expanded)", "%PATH%", "Unicode \uD55C\uAE00"]
capture = output / "capture.py"
capture.write_text("import json, sys\nfrom pathlib import Path\n"
                   "Path(sys.argv[1]).write_text(json.dumps(sys.argv[2:]), encoding='utf-8')\n",
                   encoding="utf-8")
consumer = [Path(sys.executable).as_posix(), capture.as_posix(),
            (output / "captured.json").as_posix()]
if args.consumer == "msys":
    consumer = ["bash", "-c", 'printf "%s\\0" "$@" > "$0"',
                (output / "captured.bin").as_posix()]
command = ["perl", "scripts/resource/process-tree-rss-watchdog.pl",
           "--budget-scope=aggregate-tests", "--aggregate-workers=1",
           "--max-rss-kib=1048576", "--interval-ms=100", "--timeout-seconds=30",
           "--receipt=" + (output / "owner.env").as_posix(), "--", *consumer, *values]
# A literal quoted script removes PowerShell/native command-line interpolation
# from the test. The retained NUL-delimited spec proves the guard's input too.
launch = output / "launch.shs"
launch.write_text("#!/usr/bin/env bash\nset -eu\ncd " + shlex.quote(root.as_posix())
                  + "\nexport SIMPLE_BOOTSTRAP_SESSION_HELPER_CACHE=$(cygpath -u "
                  + shlex.quote((output / "helper-cache").as_posix()) + ")"
                  + "\nexec " + shlex.join(command) + "\n", encoding="utf-8")
environment = os.environ.copy()
environment["CC"] = args.cc
run = subprocess.run(["bash", launch.as_posix()], env=environment, capture_output=True, timeout=90)
(output / "stdout.log").write_bytes(run.stdout)
(output / "stderr.log").write_bytes(run.stderr)
if run.returncode:
    raise SystemExit(f"FAIL: guard exit {run.returncode}; inspect {output}")
specs = list(output.glob("simple-rss-session-*/workload.spec"))
if len(specs) != 1:
    raise SystemExit("FAIL: missing unique guard input spec")
incoming = specs[0].read_bytes().split(b"\0")[-len(values)-1:-1]
if incoming != [value.encode("utf-8") for value in values]:
    raise SystemExit("FAIL: launcher changed argv before the native helper")
if args.consumer == "msys":
    actual = (output / "captured.bin").read_bytes().decode("utf-8").split("\0")[:-1]
else:
    actual = json.loads((output / "captured.json").read_text(encoding="utf-8"))
if actual != values:
    (output / "expected.json").write_text(json.dumps(values), encoding="utf-8")
    raise SystemExit(f"FAIL: native helper changed argv; inspect {output}")
receipt = (output / "owner.env").read_text(encoding="utf-8")
if "status=complete\n" not in receipt or "exit_status=0\n" not in receipt:
    raise SystemExit("FAIL: missing terminal successful Job receipt")
print(f"PASS: {len(values)} literal argv cases through Windows Job guard to {args.consumer}")

#!/usr/bin/env python3
"""Compile the actual Rust-generated private-root provider with Windows SDK targets.

Requires a real Windows-targeting C compiler. This is compile evidence only.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--cc", required=True)
parser.add_argument("--output-root", required=True, type=Path)
parser.add_argument("--source-root", type=Path, default=Path(__file__).resolve().parents[2])
args = parser.parse_args()
root = args.source_root.resolve()
output = args.output_root.resolve()
output.mkdir(parents=True, exist_ok=False)
build = (root / "src/compiler_rust/runtime/build.rs").read_text(encoding="utf-8")
stub = re.search(r"let stub_body = concat!\((.*?)\n\s*\);", build, re.S)
if stub is None:
    # Accept the prior producer too so this check can demonstrate its failure.
    stub = re.search(r"let stub_body = (\"(?:\\.|[^\"\\])*\");", build)
if stub is None:
    raise SystemExit("FAIL: generated private-root provider source not found")
body = "".join(json.loads(token) for token in re.findall(r'"(?:\\.|[^"\\])*"', stub[1]))
if '#include "platform/runtime_windows_private_root.h"' not in body:
    raise SystemExit("FAIL: selected stub is not the private-root provider")
results = []
for name, target, expected in (("default", None, "0x0602"),
                               ("windows7", "0x0601", "0x0602"),
                               ("windows10", "0x0A00", "0x0A00")):
    source = output / f"{name}.c"
    artifact = output / f"{name}.o"
    source.write_text(body + f"\n#if _WIN32_WINNT < {expected}\n#error SDK target too old\n#endif\n"
                      + (f"#if _WIN32_WINNT != {expected}\n#error explicit target changed\n#endif\n"
                         if target else ""), encoding="utf-8")
    command = [args.cc, "--target=x86_64-w64-windows-gnu", "-std=c11", "-c",
               str(source), "-I", str(root / "src/runtime"), "-o", str(artifact)]
    if target:
        command.append(f"-D_WIN32_WINNT={target}")
    completed = subprocess.run(command, capture_output=True)
    (output / f"{name}.stdout").write_bytes(completed.stdout)
    (output / f"{name}.stderr").write_bytes(completed.stderr)
    passed = completed.returncode == 0 and artifact.is_file() and artifact.stat().st_size > 0
    results.append({"case": name, "argv": command, "exit": completed.returncode,
                    "artifact": str(artifact), "passed": passed})
(output / "results.json").write_text(json.dumps(results, indent=2), encoding="utf-8")
if not all(result["passed"] for result in results):
    raise SystemExit(f"FAIL: inspect {output / 'results.json'}")
print("PASS: real private-root provider compiles for default, Windows 7, and Windows 10 SDK targets")

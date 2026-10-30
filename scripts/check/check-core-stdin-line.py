#!/usr/bin/env python3
"""Compile real core-C owners and check stdin bytes through fresh raw pipes.

Windows GNU clang is the supported checker toolchain. This is runtime ABI
regression evidence, not self-hosted runner or Rust-seed qualification.
"""
import argparse
import hashlib
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cc", required=True)
    parser.add_argument("--work-dir", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    work = Path(args.work_dir).resolve()
    work.mkdir(parents=True, exist_ok=False)
    target = subprocess.check_output([args.cc, "-dumpmachine"], text=True).strip()
    if "windows" not in target and "mingw" not in target:
        raise SystemExit("Windows GNU compiler required; no checks executed")
    owners = ["runtime_native", "runtime_legacy_core", "runtime_process",
              "runtime_memory", "runtime_simd_dispatch", "runtime_simd_utf8",
              "runtime_process_owned", "runtime_memtrack"]
    executable = work / "core-stdin-line.exe"
    command = [args.cc, "-Os", "-ffunction-sections", "-fdata-sections",
               "-std=gnu11", "-UUNICODE", "-U_UNICODE",
               "-DSIMPLE_CORE_C_STANDALONE=1", "-DSIMPLE_RUNTIME_MEMORY_OWNER=1",
               "-I" + str(root / "src/runtime"),
               "-I" + str(root / "src/runtime/platform"),
               str(root / "test/runtime/core_stdin_line_test.c")]
    command += [str(root / "src/runtime" / (owner + ".c")) for owner in owners]
    command += ["-Wl,--gc-sections,--exclude-all-symbols", "-o", str(executable)]
    with (work / "compile.log").open("wb") as log:
        subprocess.run(command, check=True, stdout=log, stderr=subprocess.STDOUT,
                       timeout=180)

    long_utf8 = "한글🙂".encode() * 16384
    cases = [
        ("lf", b"hello\n", [b"hello"]),
        ("crlf", b"hello\r\n", [b"hello"]),
        ("lone-cr", b"hello\r", [b"hello\r"]),
        ("empty-eof", b"", [b"", b""]),
        ("empty-line", b"\n", [b"", b""]),
        ("empty-crlf", b"\r\n", [b""]),
        ("final-no-lf", b"last", [b"last", b""]),
        ("4096-boundary", b"a" * 4096 + b"\n", [b"a" * 4096]),
        ("long", b"a" * 131073 + b"\n", [b"a" * 131073]),
        ("long-utf8", long_utf8 + b"\r\n", [long_utf8]),
        ("embedded-nul", b"a\0b\n", [b"a\0b"]),
        ("nul-only", b"\0\n", [b"\0"]),
        ("ctrl-z-binary", b"a\x1ab\n", [b"a\x1ab"]),
        ("multiple-lines", b"a\r\nb\nc\r", [b"a", b"b", b"c\r", b""]),
        ("bom-preserved", b"\xef\xbb\xbfhello\n", [b"\xef\xbb\xbfhello"]),
        ("invalid-utf8", b"\xff\nnext\n", [None, b"next"]),
        ("truncated-utf8", b"\xe2\x82", [None, b""]),
        ("overlong-utf8", b"\xc0\x80\n", [None]),
        ("read-error", b"", [None, None]),
    ]
    results = []
    for name, raw, expected in cases:
        invocation = [str(executable), str(len(expected))]
        if name == "read-error": invocation.append(name)
        result = subprocess.run(invocation, input=raw, capture_output=True, timeout=15)
        want = b"".join(b"nil\n" if value is None else
                        b"text:" + str(len(value)).encode() + b":" +
                        value.hex().encode() + b"\n" for value in expected)
        if result.returncode != 0 or result.stdout != want or result.stderr:
            (work / (name + ".stdout")).write_bytes(result.stdout)
            (work / (name + ".stderr")).write_bytes(result.stderr)
            raise AssertionError(f"{name}: exit={result.returncode}, output mismatch")
        results.append("PASS " + name)
    evidence = "\n".join(results) + "\nexecutable_sha256=" + hashlib.sha256(
        executable.read_bytes()).hexdigest() + "\n"
    (work / "results.txt").write_text(evidence, encoding="utf-8")
    print(evidence, end="")


if __name__ == "__main__":
    main()

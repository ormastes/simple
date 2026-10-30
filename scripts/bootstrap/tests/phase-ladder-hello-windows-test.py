#!/usr/bin/env python3
"""Real PE exit/output tests of ladder glue, not Simple compiler qualification.

Requires native Windows Python, Git Bash sh, MSVC-target Clang and kernel32.lib.
No CRT, Windows headers, Simple compiler, or helper compilation is involved.
"""
import argparse
import concurrent.futures
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile


def check(base, production, harness, args, code, ending):
    name = str(code) + "-" + ending
    stdout = b"phase-ladder-2-ok\r\n" if ending == "crlf" else b"phase-ladder-2-ok\n"
    stderr = b"extra native stderr\n" if ending == "extra-stderr" else b""
    accepted = code == 0 and ending != "extra-stderr"
    source = base / (name + ".c")
    program = base / (name + ".exe")
    out_bytes = ",".join(str(byte) for byte in stdout)
    err_bytes = ",".join(str(byte) for byte in stderr) or "0"
    source.write_text("""__declspec(dllimport) void * __stdcall GetStdHandle(unsigned long);
__declspec(dllimport) int __stdcall WriteFile(void *, const void *, unsigned long, unsigned long *, void *);
__declspec(dllimport) __declspec(noreturn) void __stdcall ExitProcess(unsigned long);
void entry(void) {
    static const unsigned char output[] = {""" + out_bytes + """};
    static const unsigned char error[] = {""" + err_bytes + """};
    unsigned long written;
    WriteFile(GetStdHandle((unsigned long)-11), output, sizeof(output), &written, 0);
    """ + ("WriteFile(GetStdHandle((unsigned long)-12), error, sizeof(error), &written, 0);" if stderr else "") + "\n    ExitProcess(" + str(code) + "u);\n}\n", encoding="ascii")
    command = [args.clang, "--target=x86_64-pc-windows-msvc", "-fuse-ld=lld", "-nostdlib",
               "-fno-stack-protector", "-Xlinker", "/entry:entry", "-Xlinker", "/subsystem:console",
               "-Xlinker", "/nodefaultlib", str(source), args.kernel32_lib, "-o", str(program)]
    compiled = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
    (base / (name + ".compile.stdout")).write_bytes(compiled.stdout)
    (base / (name + ".compile.stderr")).write_bytes(compiled.stderr)
    assert compiled.returncode == 0, (name, compiled.stderr)
    assert program.read_bytes()[:2] == b"MZ", name
    case = (name, stdout, code, stderr, accepted)
    return harness.check_case(base, production, args.shell, "windows-x86_64", case, program)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=24)
    parser.add_argument("--shell", required=True)
    parser.add_argument("--clang", required=True)
    parser.add_argument("--kernel32-lib", required=True)
    args = parser.parse_args()
    if os.name != "nt" or args.jobs < 1:
        parser.error("native Windows and positive --jobs are required")
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location("ladder_glue_controls", here / "phase-ladder-hello-test.py")
    harness = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(harness)
    production = here.parent / "phase-ladder-step.shs"
    base = Path(tempfile.mkdtemp(prefix="phase-ladder-native-hello-"))
    print("evidence=" + str(base), flush=True)
    work = [(code, ending) for code in (0, 17, 255, 256, 257, 512, 2147483648, 3221225477)
            for ending in ("lf", "crlf", "extra-stderr")]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(check, base, production, harness, args, code, ending)
                   for code, ending in work]
        for future in futures:
            print("PASS " + future.result(), flush=True)
    print("PASS: 24 real PE runner controls; no Simple compiler qualification")


if __name__ == "__main__":
    main()

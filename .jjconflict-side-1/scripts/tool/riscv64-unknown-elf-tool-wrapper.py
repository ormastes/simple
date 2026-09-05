import os
import subprocess
import sys


def tool_path(kind: str) -> str:
    if kind == "gcc":
        override = os.environ.get("SIMPLE_RISCV64_GCC", "")
        name = "riscv64-unknown-elf-gcc.exe"
    else:
        override = os.environ.get("SIMPLE_RISCV64_GXX", "")
        name = "riscv64-unknown-elf-g++.exe"
    if override:
        return override
    default = os.path.join("C:\\dev\\tool\\msys2\\mingw64\\bin", name)
    if os.path.exists(default):
        return default
    return name


def filtered_args(args: list[str]) -> list[str]:
    out: list[str] = []
    i = 0
    while i < len(args):
        arg = args[i]
        if arg.lower() == "--target=riscv64-unknown-elf":
            i += 1
            continue
        if arg.lower() == "--target":
            i += 2
            continue
        if arg.lower() == "-fuse-ld=lld":
            i += 1
            continue
        out.append(arg)
        i += 1
    return out


def main() -> int:
    if len(sys.argv) < 2 or sys.argv[1] not in ("gcc", "gxx"):
        print("usage: riscv64-unknown-elf-tool-wrapper.py gcc|gxx [args...]", file=sys.stderr)
        return 2
    return subprocess.call([tool_path(sys.argv[1]), *filtered_args(sys.argv[2:])])


if __name__ == "__main__":
    raise SystemExit(main())

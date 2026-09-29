#!/usr/bin/env python3
"""Replay a captured Linux LLD hello link with only its program object changed."""

import argparse
import hashlib
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path, PurePosixPath


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def run(command: list[str], cwd: Path) -> None:
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True,
                            check=False)
    require(result.returncode == 0,
            f"command-failed:{command[0]}:{result.stderr[-400:]}")


def global_symbols(path: Path, defined: bool) -> set[str]:
    mode = "--defined-only" if defined else "--undefined-only"
    result = subprocess.run(["nm", "-g", mode, str(path)], text=True,
                            capture_output=True, check=False)
    require(result.returncode == 0, f"object-symbol-read-failed:{path}")
    return {line.split()[-1] for line in result.stdout.splitlines() if line.split()}


def receipt_fields(path: Path) -> dict[str, str]:
    lines = path.read_text(encoding="ascii").splitlines()
    require(len(lines) == 4 and lines[0] == "simple-native-link-reproduce-v1",
            "receipt-schema-invalid")
    fields = {}
    for line in lines[1:]:
        key, separator, value = line.partition("=")
        require(separator == "=" and key not in fields and
                re.fullmatch(r"[0-9a-f]{64}", value) is not None,
                "receipt-field-invalid")
        fields[key] = value
    require(set(fields) == {"archive_sha256", "output_sha256", "linker_sha256"},
            "receipt-fields-invalid")
    return fields


def extract_reproduction(archive: Path, destination: Path) -> Path:
    with tarfile.open(archive, "r:") as source:
        members = source.getmembers()
        require(0 < len(members) <= 512, "archive-member-count-invalid")
        names = set()
        roots = set()
        total = 0
        for member in members:
            name = PurePosixPath(member.name)
            require(member.isfile() and member.name == str(name) and
                    not name.is_absolute() and
                    len(name.parts) >= 2 and
                    all(part not in ("", ".", "..") for part in name.parts) and
                    member.name not in names, "archive-member-invalid")
            names.add(member.name)
            roots.add(name.parts[0])
            total += member.size
            require(total <= 512 * 1024 * 1024, "archive-too-large")
            target = destination.joinpath(*name.parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            payload = source.extractfile(member)
            require(payload is not None, "archive-member-unreadable")
            with target.open("wb") as output:
                shutil.copyfileobj(payload, output)
        require(len(roots) == 1, "archive-root-invalid")
        root = destination / next(iter(roots))
        require((root / "response.txt").is_file() and
                (root / "version.txt").is_file(), "archive-response-missing")
        return root


def check(args: argparse.Namespace) -> str:
    paths = [args.archive, args.receipt, args.simple_binary,
             args.simple_stripped, args.c_source, args.expected_stdout,
             args.c_binary,
             args.c_stripped, args.clang, args.lld, args.strip]
    for path in paths:
        require(path.is_file(), f"input-missing:{path}")
    for path in paths[:8]:
        require(not path.is_symlink(), f"input-symlink:{path}")
    expected_stdout = args.expected_stdout.read_bytes()
    require(0 < len(expected_stdout) <= 4096 and
            expected_stdout.endswith(b"\n") and b"\0" not in expected_stdout,
            "expected-stdout-invalid")
    fields = receipt_fields(args.receipt)
    require(digest(args.archive) == fields["archive_sha256"],
            "archive-digest-mismatch")
    require(digest(args.simple_binary) == fields["output_sha256"],
            "simple-output-digest-mismatch")
    require(digest(args.lld) == fields["linker_sha256"],
            "linker-digest-mismatch")

    with tempfile.TemporaryDirectory(prefix="simple-matched-link-") as temp:
        root = extract_reproduction(args.archive, Path(temp))
        response = (root / "response.txt").read_text(encoding="utf-8").splitlines()
        require(response.count("--chroot .") == 1 and
                "--gc-sections" in response and "--icf=all" in response and
                "-pie" in response, "response-link-profile-invalid")
        outputs = [line for line in response if line.startswith("-o ")]
        require(len(outputs) == 1, "response-output-invalid")
        output_name = outputs[0][3:]
        require(re.fullmatch(r"[A-Za-z0-9_.-]+", output_name) is not None,
                "response-output-path-invalid")
        modules = [line for line in response if line.endswith(".o") and
                   "/native-build/v1/" in line and
                   PurePosixPath(line).name.startswith("object.")]
        require(len(modules) == 1 and (root / modules[0]).is_file(),
                "hello-module-object-ambiguous")

        run([str(args.lld), "@response.txt"], root)
        require(digest(root / output_name) == digest(args.simple_binary),
                "simple-link-replay-mismatch")
        run([str(args.strip), "--strip-all", "-o", "simple-stripped",
             output_name], root)
        require(digest(root / "simple-stripped") == digest(args.simple_stripped),
                "simple-strip-replay-mismatch")

        run([str(args.clang), "-Os", "-fPIE", "-ffunction-sections",
             "-fdata-sections", "-c", str(args.c_source), "-o", "c-hello.o"],
            root)
        simple_object = root / modules[0]
        c_object = root / "c-hello.o"
        require(global_symbols(simple_object, True) == {"__simple_main"} and
                global_symbols(c_object, True) == {"__simple_main"} and
                global_symbols(simple_object, False) == {"rt_println_str"} and
                global_symbols(c_object, False) == {"puts"},
                "hello-object-symbol-contract-invalid")
        c_response = ["-o c-hello" if line == outputs[0] else
                      "c-hello.o" if line == modules[0] else line
                      for line in response]
        (root / "response-c.txt").write_text("\n".join(c_response) + "\n",
                                              encoding="utf-8")
        run([str(args.lld), "@response-c.txt"], root)
        require(digest(root / "c-hello") == digest(args.c_binary),
                "c-link-replay-mismatch")
        run([str(args.strip), "--strip-all", "-o", "c-hello-stripped",
             "c-hello"], root)
        require(digest(root / "c-hello-stripped") == digest(args.c_stripped),
                "c-strip-replay-mismatch")
        for binary in (root / "simple-stripped", root / "c-hello-stripped"):
            result = subprocess.run([str(binary)], cwd=root,
                                    capture_output=True, check=False)
            require(result.returncode == 0 and result.stdout == expected_stdout,
                    f"hello-output-mismatch:{binary.name}")

    simple_bytes = args.simple_stripped.stat().st_size
    c_bytes = args.c_stripped.stat().st_size
    require(simple_bytes <= 15360, "simple-over-15kib")
    require(simple_bytes * 100 <= c_bytes * 105, "simple-over-matched-c-105-percent")
    return ("STATUS: PASS runtime-binary-size-matched-link "
            f"simple={simple_bytes} c={c_bytes} "
            f"ratio={simple_bytes / c_bytes:.6f} "
            f"archive_sha256={fields['archive_sha256']}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("archive", "receipt", "simple-binary", "simple-stripped",
                 "c-source", "expected-stdout", "c-binary", "c-stripped",
                 "clang", "lld", "strip"):
        parser.add_argument(f"--{name}", required=True, type=Path)
    args = parser.parse_args()
    for name in vars(args):
        setattr(args, name, getattr(args, name).absolute())
    try:
        print(check(args))
        return 0
    except (OSError, ValueError, tarfile.TarError) as error:
        print(f"STATUS: FAIL runtime-binary-size-matched-link — {error}",
              file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

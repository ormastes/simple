#!/usr/bin/env python3
"""Check real core-C owners and the full platform owner on private fixtures."""
import argparse
import hashlib
import os
from pathlib import Path
import stat
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cc", required=True)
    parser.add_argument("--work-dir", required=True)
    args = parser.parse_args()
    if os.name != "nt":
        raise SystemExit("Windows host required; no cases executed")
    root = Path(__file__).resolve().parents[2]
    work = Path(args.work_dir).resolve()
    work.mkdir(parents=True, exist_ok=False)
    target = subprocess.check_output([args.cc, "-dumpmachine"], text=True).strip()
    if "windows" not in target and "mingw" not in target:
        raise SystemExit("Windows GNU compiler required; no cases executed")
    owners = ["runtime_native", "runtime_legacy_core", "runtime_process",
              "runtime_memory", "runtime_simd_dispatch", "runtime_simd_utf8",
              "runtime_process_owned", "runtime_memtrack"]
    results = []
    for lane in ("core", "shared_full_policy"):
        exe = work / (lane + ".exe")
        cmd = [args.cc, "-Os", "-ffunction-sections", "-fdata-sections",
               "-std=gnu11", "-municode", "-UUNICODE", "-U_UNICODE",
               "-I" + str(root / "src/runtime"),
               "-I" + str(root / "src/runtime/platform"),
               str(root / "test/runtime/windows_remove_tree_test.c")]
        if lane == "core":
            cmd += ["-DSIMPLE_CORE_C_STANDALONE=1", "-DSIMPLE_RUNTIME_MEMORY_OWNER=1"]
            cmd += [str(root / "src/runtime" / (owner + ".c")) for owner in owners]
        else:
            # Compile the actual full platform owner; unrelated file/mmap
            # functions require the broad full-runtime link closure. Execute
            # its shared cleanup implementation below without replacing them.
            with (work / "full-owner-compile.log").open("wb") as log:
                subprocess.run(cmd + ["-DTEST_FULL_PLATFORM=1", "-fsyntax-only"],
                               check=True, stdout=log, stderr=subprocess.STDOUT, timeout=60)
            cmd += ["-DTEST_SHARED_FULL_POLICY=1"]
        cmd += ["-Wl,--gc-sections,--exclude-all-symbols", "-o", str(exe)]
        with (work / (lane + "-compile.log")).open("wb") as log:
            subprocess.run(cmd, check=True, stdout=log, stderr=subprocess.STDOUT, timeout=180)
        fixtures = work / lane
        fixtures.mkdir()

        def remove(path, expected=True, trailing=False):
            # Only fixture paths beneath the newly created private workspace.
            path.relative_to(work)
            spelling = str(path) + (os.sep if trailing else "")
            run = subprocess.run([str(exe), spelling], capture_output=True, timeout=15)
            assert run.returncode == (0 if expected else 1), (path, run.returncode, run.stderr)
            assert run.stdout.splitlines() == [b"removed" if expected else b"refused"], run.stdout
            if expected:
                assert not path.exists(), path

        for name, components in [("normal", ["child"]), ("unicode", ["한글🙂", "文字"]),
                                 ("long", ["a" * 64, "b" * 64, "c" * 64, "d" * 64])]:
            path = fixtures / name
            child = path.joinpath(*components)
            child.mkdir(parents=True)
            (child / "sentinel").write_text("owned", encoding="utf-8")
            if name == "long":
                assert len(str(child / "sentinel")) > 350
            remove(path)
            results.append(lane + "_" + name)

        remove(fixtures / "missing", lane == "core")
        results.append(lane + "_missing_semantics")

        trailing = fixtures / "trailing"
        trailing.mkdir()
        (trailing / "sentinel").write_text("owned", encoding="utf-8")
        remove(trailing, trailing=True)
        results.append(lane + "_trailing_separator")

        outside = fixtures / "outside"
        outside.mkdir()
        sentinel = outside / "sentinel"
        sentinel.write_text("must survive", encoding="utf-8")
        junction_root = fixtures / "junction"
        junction_root.mkdir()
        subprocess.run(["cmd.exe", "/d", "/c", "mklink", "/J",
                        str(junction_root / "link"), str(outside)],
                       check=True, capture_output=True, timeout=15)
        remove(junction_root)
        assert sentinel.read_text(encoding="utf-8") == "must survive"
        results.append(lane + "_junction_no_follow")

        file_link = fixtures / "file-link"
        try:
            file_link.symlink_to(sentinel)
        except OSError as error:
            if error.winerror != 1314:
                raise
            results.append(lane + "_file_symlink_UNSUPPORTED_privilege")
        else:
            remove(file_link)
            assert sentinel.read_text(encoding="utf-8") == "must survive"
            results.append(lane + "_file_symlink_no_follow")

        blocked = fixtures / "readonly"
        blocked.mkdir()
        locked = blocked / "sentinel"
        locked.write_text("must report failure", encoding="utf-8")
        locked.chmod(stat.S_IREAD)
        try:
            remove(blocked, False)
            assert locked.exists()
        finally:
            locked.chmod(stat.S_IREAD | stat.S_IWRITE)
        results.append(lane + "_readonly_refusal")
        results.append(lane + "_sha256=" + hashlib.sha256(exe.read_bytes()).hexdigest())
    evidence = "windows_remove_tree:\n  results:\n" + "".join(
        '    - "' + result + '"\n' for result in results)
    (work / "results.sdn").write_text(evidence, encoding="utf-8")
    print(evidence, end="")


if __name__ == "__main__":
    main()

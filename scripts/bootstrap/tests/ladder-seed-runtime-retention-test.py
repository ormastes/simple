#!/usr/bin/env python3
"""Retention-only shell fixtures. Archive/tool bytes are fixtures, never runtime admission."""
import argparse
import concurrent.futures
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


CASES = ("minimal", "companions", "hosted", "missing-archive", "empty-archive", "missing-seed",
         "mismatched-seed", "linked-archive", "linked-companion", "linked-hosted", "missing-input", "tool-failure")


def check(base, production, shell, mode, spaces):
    root = base / (("with spaces " if spaces else "plain-") + mode)
    profile = root / "src/compiler_rust/target/bootstrap"
    producer = root / "build/ladder/producer"
    fakebin = root / "fixture-bin"
    for directory in (profile, producer, fakebin):
        directory.mkdir(parents=True)
    (profile / "simple.exe").write_bytes(b"fixture seed, no qualification\n")
    shutil.copyfile(profile / "simple.exe", producer / "simple.exe")
    archive = profile / "libsimple_native_all.a"
    archive.write_bytes(b"fixture GNU archive bytes\n")
    for leaf in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml", ".cargo/config.toml"):
        path = root / "src/compiler_rust" / leaf
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("fixture Cargo input " + leaf + "\n")
    for tool in ("git", "cargo", "rustc", "clang", "ld.lld", "llvm-ar", "llvm-nm"):
        path = fakebin / tool
        path.write_text("""#!/bin/sh
set -eu
name=${0##*/}
printf '%s %s cwd=%s\\n' "$name" "$*" "$PWD" >> "$FIXTURE_ROOT/tool-calls"
if [ "$name" = git ]; then echo aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa; exit 0; fi
[ "$PWD" = "$FIXTURE_ROOT/src/compiler_rust" ] || exit 33
case "$1" in -vV|--version) ;; *) exit 34 ;; esac
if [ "$FIXTURE_MODE:$name" = tool-failure:clang ]; then exit 17; fi
printf 'fixture tool identity: %s\\nhost: x86_64-pc-windows-gnullvm\\n' "$name"
""", encoding="utf-8", newline="\n")
        path.chmod(0o755)
    if mode == "companions":
        for leaf in ("libsimple_runtime.a", "simple_runtime.dll", "libsimple_runtime.dll.a"):
            (profile / leaf).write_bytes(b"fixture companion " + leaf.encode())
    if mode in ("hosted", "linked-hosted"):
        (profile / "deps").mkdir()
        (profile / "deps/libspl_hosted_runtime-one.rlib").write_bytes(b"fixture rlib one")
        (profile / "deps/libspl_hosted_runtime-two.rlib").write_bytes(b"fixture rlib two")
    if mode == "missing-archive": archive.unlink()
    if mode == "empty-archive": archive.write_bytes(b"")
    if mode == "missing-seed": (profile / "simple.exe").unlink()
    if mode == "mismatched-seed": (producer / "simple.exe").write_bytes(b"different seed")
    if mode == "linked-archive":
        archive.rename(profile / "real.a")
        archive.symlink_to("real.a")
    if mode == "linked-companion": (profile / "simple_runtime.dll").symlink_to("libsimple_native_all.a")
    if mode == "linked-hosted":
        (profile / "deps/libspl_hosted_runtime-one.rlib").unlink()
        (profile / "deps/libspl_hosted_runtime-one.rlib").symlink_to("libspl_hosted_runtime-two.rlib")
    if mode == "missing-input": (root / "src/compiler_rust/Cargo.lock").unlink()
    env = os.environ.copy()
    env.update(PATH=str(fakebin) + os.pathsep + env["PATH"], FIXTURE_ROOT=str(root), FIXTURE_MODE=mode,
               SIMPLE_WINDOWS_ABI="gnu", CARGO_BUILD_JOBS="24")
    result = subprocess.run([shell, str(production), str(root), str(profile), str(producer)],
                            cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
    (root / "stdout").write_bytes(result.stdout)
    (root / "stderr").write_bytes(result.stderr)
    accepted = mode in ("minimal", "companions", "hosted")
    manifest = producer / "runtime/retention.sdn"
    assert (result.returncode == 0) == accepted, (mode, result.stderr)
    assert manifest.exists() == accepted, mode
    if accepted:
        text = manifest.read_text()
        assert "selection: not-observed\nadmission: none\n" in text
        assert 'native_all_features: "driver-compat"' in text
        assert 'environment_CARGO_BUILD_JOBS: "24"' in text
        retained = producer / "runtime/libsimple_native_all.a"
        assert retained.read_bytes() == archive.read_bytes()
        assert hashlib.sha256(archive.read_bytes()).hexdigest() in text
        assert hashlib.sha256((producer / "simple.exe").read_bytes()).hexdigest() in text
        assert hashlib.sha256((producer / "runtime/toolchain.txt").read_bytes()).hexdigest() in text
        for original in profile.glob("*.dll*"):
            assert (producer / "runtime" / original.name).read_bytes() == original.read_bytes()
        for original in profile.glob("deps/*.rlib"):
            assert (producer / "runtime/deps" / original.name).read_bytes() == original.read_bytes()
        calls = (root / "tool-calls").read_text()
        assert "cargo -vV" in calls and "rustc -vV" in calls
        assert "cargo build" not in calls
    return mode + (":spaces" if spaces else ":plain")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=24)
    parser.add_argument("--shell", default="sh")
    args = parser.parse_args()
    if args.jobs < 1: parser.error("positive --jobs required")
    production = Path(__file__).resolve().parents[1] / "lib/retain-ladder-seed-runtime.shs"
    base = Path(tempfile.mkdtemp(prefix="ladder-runtime-retention-"))
    print("evidence=" + str(base), flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(check, base, production, args.shell, mode, spaces)
                   for mode in CASES for spaces in (False, True)]
        for future in futures: print("PASS " + future.result(), flush=True)
    print("PASS: 24 retention-only shell controls; no Cargo build or runtime qualification")


if __name__ == "__main__": main()

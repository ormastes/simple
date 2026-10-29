#!/usr/bin/env python3
"""Run a real linkage lane inside a BuildRunner-owned process tree.

The manager pins this driver, its Python producer, compiler and runtime inputs.
The result bundle is a task output; it never substitutes for manager verification
or a worker memory-enforcement receipt.
"""
import argparse
import importlib.util
import os
from pathlib import Path
import signal
import threading
import types
import zipfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", required=True, choices=["llvm", "cranelift"])
    parser.add_argument("--lane", required=True,
                        choices=["one-source", "two-objects", "static-library", "shared-library"])
    parser.add_argument("--phase", required=True, type=int, choices=[2, 3])
    parser.add_argument("--compile-route", required=True, choices=["positional", "coordinator"])
    parser.add_argument("--compiler-sha256", required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--timeout-seconds", required=True, type=int)
    parser.add_argument("--max-rss-kib", required=True, type=int)
    parser.add_argument("--min-free-disk-bytes", required=True, type=int)
    parser.add_argument("--max-log-bytes", required=True, type=int)
    parser.add_argument("--linker", required=True)
    parser.add_argument("--windows-abi", default="msvc", choices=["msvc", "gnu"])
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    root = Path.cwd()
    helper = root / "scripts/bootstrap/hello-sanity-matrix.py"
    spec = importlib.util.spec_from_file_location("hello_managed_matrix", helper)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    compiler = root / ("compiler.exe" if os.name == "nt" else "compiler")
    if module.digest(compiler) != args.compiler_sha256:
        raise ValueError("staged compiler identity mismatch")
    compiler.chmod(compiler.stat().st_mode | 0o100)
    options = types.SimpleNamespace(**vars(args), source_root=root, compiler=compiler,
        runtime_path=root / "runtime", jobs=1, lanes=[args.lane],
        reuse_build_evidence=None, reuse_shared_evidence=None)
    options.output = root / "results"
    matrix = module.Matrix(options)
    matrix.out.mkdir()
    for key, name in (("SIMPLE_RT_OBJ_CACHE_DIR", "runtime"),
                      ("SIMPLE_HIR_CACHE_DIR", "hir"),
                      ("SIMPLE_FRONTEND_CACHE_DIR", "frontend")):
        cache = root / ".builder-cache" / name
        cache.mkdir(parents=True, exist_ok=True)
        matrix.base[key] = str(cache)
    for number in (signal.SIGINT, signal.SIGTERM):
        signal.signal(number, lambda *_: matrix.stop.set())
    result = matrix.lane(args.lane, threading.Barrier(1))
    if result["status"] != "PASS" or matrix.children:
        return 1
    matrix.validate_identity()
    if module.runtime_identity(matrix.runtime) != matrix.runtime_hashes:
        raise ValueError("runtime changed during managed lane")
    lane = matrix.out / args.lane
    module.sdn(lane / "managed-lane.sdn", {
        "format": "hello-buildrunner-lane-v1", "lane": args.lane,
        "backend": args.backend, "phase": args.phase,
        "compile_route": args.compile_route, "compiler_sha256": matrix.sha,
        "status": "PASS", "admitted": False})
    # Only regular top-level products/evidence are exported. Mutable compiler
    # caches remain in the manager-owned attempt for diagnostic inspection.
    with zipfile.ZipFile(args.output, "x", compression=zipfile.ZIP_DEFLATED) as bundle:
        for path in sorted(lane.iterdir()):
            if path.is_file() and not path.is_symlink():
                bundle.write(path, path.name)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

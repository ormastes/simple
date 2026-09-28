#!/usr/bin/env python3
"""Attest the Git checkouts named by a pinned Skia DEPS file."""

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys


REVISION = re.compile(r"^[0-9a-f]{40}$")


def git(path, *args):
    result = subprocess.run(
        ["git", "-C", str(path), *args],
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def git_config(path, key):
    result = subprocess.run(
        ["git", "-C", str(path), "config", "--get", key],
        capture_output=True,
        text=True,
    )
    if result.returncode not in (0, 1):
        raise ValueError(f"cannot read Git config for {path}")
    return result.stdout.strip()


def dependencies(deps_file):
    namespace = {}
    namespace["Var"] = lambda name: namespace["vars"][name]
    exec(compile(deps_file.read_text(), str(deps_file), "exec"), namespace)
    entries = namespace.get("deps")
    if not isinstance(entries, dict) or not entries:
        raise ValueError("DEPS has no dependency map")
    for path, value in sorted(entries.items()):
        if isinstance(value, dict):
            if value.get("dep_type") == "cipd":
                continue
            if value.get("condition") == "False":
                continue
            value = value.get("url")
        if not isinstance(path, str) or not isinstance(value, str):
            raise ValueError(f"unsupported Git dependency entry: {path!r}")
        url, separator, revision = value.rpartition("@")
        if not separator or not url or not REVISION.fullmatch(revision):
            raise ValueError(f"dependency has no pinned Git revision: {path}")
        yield path, url, revision


def attest(root):
    root = root.resolve(strict=True)
    manifest = []
    for name, url, expected in dependencies(root / "DEPS"):
        path = (root / name).resolve(strict=True)
        if path == root or root not in path.parents:
            raise ValueError(f"dependency escapes Skia root: {name}")
        if pathlib.Path(name).is_absolute() or ".." in pathlib.Path(name).parts:
            raise ValueError(f"invalid dependency path: {name}")
        if pathlib.Path(git(path, "rev-parse", "--show-toplevel")).resolve() != path:
            raise ValueError(f"dependency is not its own Git checkout: {name}")
        actual = git(path, "rev-parse", "HEAD")
        # Skia DEPS pins may name an annotated tag object rather than the
        # commit it points at (e.g. perfetto's "v26.1" amalgamation tag).
        # Compare commits on both sides so such pins attest correctly; a pin
        # that does not resolve locally keeps the raw comparison and fails
        # with the same typed error as before.
        resolved = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "--verify", f"{expected}^{{commit}}"],
            capture_output=True,
            text=True,
        )
        expected_commit = resolved.stdout.strip() if resolved.returncode == 0 else expected
        if actual != expected_commit:
            raise ValueError(f"dependency revision differs from DEPS: {name}")
        if git(path, "status", "--porcelain", "--untracked-files=all"):
            raise ValueError(f"dependency has local modifications: {name}")
        if git_config(path, "sync-deps.disable").lower() == "true":
            raise ValueError(f"dependency sync is disabled: {name}")
        manifest.append({"path": name, "revision": actual, "url": url})
    if not manifest:
        raise ValueError("no Git dependencies verified")
    return manifest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("skia_root", type=pathlib.Path)
    parser.add_argument("manifest", type=pathlib.Path)
    args = parser.parse_args()
    try:
        manifest = attest(args.skia_root)
        data = (json.dumps(manifest, sort_keys=True, separators=(",", ":")) + "\n").encode()
        args.manifest.write_bytes(data)
        print(hashlib.sha256(data).hexdigest())
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        print(f"Skia dependency attestation failed: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())

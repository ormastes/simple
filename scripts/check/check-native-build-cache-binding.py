#!/usr/bin/env python3
"""Tiny native execution of production cache-owner bodies, not a compiler rebuild.

The driver is a recording test double. Environment thunks, argument selection,
binding/restoration and the parent call sequence are extracted from production.
No compiler imports are loaded. Logs, source hashes and caches remain in work.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def function(source, name):
    match = re.search(r"(?m)^(?:pub )?fn " + re.escape(name) + r"\(", source)
    if not match:
        raise ValueError("missing production function: " + name)
    lines = source[match.start():].splitlines()
    result = [lines[0]]
    for line in lines[1:]:
        if line and not line[0].isspace():
            break
        result.append(line)
    return "\n".join(result).rstrip() + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--negative-control", action="store_true")
    parser.add_argument("--retry", action="store_true", help="reuse this fixture's cache and preserve prior logs")
    args = parser.parse_args()
    args.work.mkdir(parents=True, exist_ok=args.retry)
    if args.retry:
        for name in ("plan.json", "compile.log", "run.log", "result.json"):
            previous = args.work / name
            if previous.exists():
                number = 1
                while (args.work / f"{name}.previous-{number}").exists():
                    number += 1
                previous.rename(args.work / f"{name}.previous-{number}")
    originals = {}

    def read(path):
        text = (args.repo / path).read_text()
        originals[path] = hashlib.sha256(text.encode()).hexdigest()
        return text

    runtime = read("src/lib/nogc_sync_mut/io_runtime.spl")
    sosix = read("src/lib/nogc_async_mut/sosix/environment.spl")
    owner = read("src/app/io/native_build_cache.spl")
    argv = read("src/app/cli/bootstrap_focused_native_build_args.spl")
    parent = read("src/app/cli/bootstrap_main.spl")
    host_path = read("src/lib/nogc_sync_mut/fs/host_path.spl")
    platform = read("src/lib/nogc_sync_mut/sffi/platform.spl")
    pieces = []
    for symbol, body, alias in [
        ("env_get_nullable", runtime, "sosix_env_get_nullable"),
        ("env_set_process", runtime, "sosix_env_set"),
        ("env_remove_process", runtime, "sosix_env_remove"),
    ]:
        assert f"{symbol} as {alias}" in sosix
        pieces.append(function(body, symbol).replace("fn " + symbol + "(", "fn " + alias + "(", 1))
    for symbol in ("rt_env_get", "rt_env_set", "rt_env_remove", "rt_file_write_text"):
        declaration = re.search(r"(?m)^extern fn " + symbol + r"\([^\n]+", runtime).group()
        pieces.append('@unsafe(reason: "projected runtime owner ABI", capabilities: [ffi])\n' + declaration)
    declaration = re.search(r"(?m)^extern fn rt_platform_name\([^\n]+", platform).group()
    pieces.append('@unsafe(reason: "projected platform owner ABI", capabilities: [ffi])\n' + declaration)
    pieces.append(function(platform, "platform_name_raw"))
    pieces.append("var _host_windows_flag: [i64] = []")
    for name in re.findall(r"(?m)^(?:pub )?fn (\w+)\(", host_path):
        pieces.append(function(host_path, name))
    pieces.append(function(runtime, "file_write_exact"))
    for name in ("focused_native_build_arg_value", "focused_native_build_cache_dir"):
        pieces.append(function(argv, name))
    for name in ("native_build_cache_snapshot", "native_build_cache_bind", "native_build_cache_restore"):
        pieces.append(function(owner, name))
    begin = parent.index("    val previous_cache = native_build_cache_snapshot()")
    end = parent.index("    # Free-function accessors", begin)
    sequence = parent[begin:end]
    assert sequence.index("native_build_cache_bind") < sequence.index("compiler_driver_create")
    assert sequence.index("native_build_cache_restore") > sequence.index("compiler_driver_run_compile")
    if args.negative_control:
        # Reproduce the old positional route's ignored explicit CLI binding.
        sequence = sequence.replace("native_build_cache_bind(requested_cache)", 'native_build_cache_bind("")')
    pieces.append("fn fixture_owner(args: [text], options: i64) -> i64:\n" + sequence + "    result\n")
    pieces.append('''fn compiler_driver_create(options: i64) -> i64:
    options

fn compiler_driver_run_compile(status: i64) -> i64:
    val cache = native_build_cache_snapshot() ?? ""
    if not file_write_exact(cache + "/native_provider_identity.receipt", cache): return 91
    if not file_write_exact(cache + "/build_cache.sdn", cache): return 92
    if not file_write_exact(cache + "/reverse-references/CURRENT", cache): return 93
    status
''')
    names = ["inherited", "phase2/producer-a/entry-one", "phase3/producer-b/entry-one",
             "phase3/producer-b/entry-two", "returned-failure", "absent", "empty", "worker", "equivalent"]
    paths = {name: str(args.work / "roots" / name) for name in names}
    for path in paths.values():
        Path(path, "reverse-references").mkdir(parents=True, exist_ok=args.retry)
    key = '"SIMPLE_NATIVE_BUILD_CACHE_DIR"'
    quote = json.dumps
    cases = [f"    if not sosix_env_set({key}, {quote(paths['inherited'])}): return 10"]
    requested = []
    for index, name in enumerate(names[1:4], 1):
        path = paths[name]
        requested.append((path, path))
        cases += [f'    if fixture_owner(["simple", "native-build", "entry.spl", "--cache-dir", {quote(path)}], 0) != 0: return {10 + index}',
                  f"    if native_build_cache_snapshot() != {quote(paths['inherited'])}: return {20 + index}"]
        if args.negative_control:
            break
    if not args.negative_control:
        cases += [f'    if fixture_owner(["simple", "native-build", "entry.spl", "--cache-dir={paths["returned-failure"]}"], 1) != 1: return 31',
                  f"    if native_build_cache_snapshot() != {quote(paths['inherited'])}: return 32",
                  f"    if not sosix_env_remove({key}): return 33",
                  f'    if fixture_owner(["simple", "native-build", "entry.spl", "--cache-dir", {quote(paths["absent"])}], 0) != 0: return 34',
                  "    if native_build_cache_snapshot() != nil: return 35",
                  f'    if not sosix_env_set({key}, ""): return 36',
                  f'    if fixture_owner(["simple", "native-build", "entry.spl", "--cache-dir", {quote(paths["empty"])}], 0) != 0: return 37',
                  "    if native_build_cache_snapshot() == nil: return 38",
                  '    if native_build_cache_snapshot() != "": return 39',
                  f"    if not sosix_env_set({key}, {quote(paths['worker'])}): return 40",
                  '    if fixture_owner(["simple", "native-build", "entry.spl"], 0) != 0: return 41',
                  f"    if native_build_cache_snapshot() != {quote(paths['worker'])}: return 42",
                  f"    if not sosix_env_set({key}, {quote(paths['equivalent'])}): return 43",
                  f'    if fixture_owner(["simple", "native-build", "entry.spl", "--cache-dir", {quote(paths["equivalent"] + "/./")}], 0) != 0: return 44',
                  f"    if native_build_cache_snapshot() != {quote(paths['equivalent'])}: return 45"]
        requested += [(paths[name], paths[name]) for name in ("returned-failure", "absent", "empty", "worker")]
        requested.append((paths["equivalent"], paths["equivalent"] + "/./"))
    pieces.append("fn main() -> i64:\n" + "\n".join(cases) + "\n    0\n")
    # SCV's canonical source inventory covers src/ and test/; a top-level
    # standalone .spl file is deliberately outside that admission surface.
    (args.work / "src").mkdir(exist_ok=args.retry)
    source = args.work / "src" / "cache-owner-projection.spl"
    source.write_text("\n\n".join(pieces))
    # SCV cold initialization requires a genuine source revision. Keep caches
    # and evidence untracked; initialize only this new disposable fixture.
    if not (args.work / ".git").exists():
        subprocess.run(["git", "init", "-q", str(args.work)], check=True)
        (args.work / ".gitignore").write_text("*\n!.gitignore\n!src/\n!src/cache-owner-projection.spl\n")
        subprocess.run(["git", "-C", str(args.work), "add", ".gitignore", str(source.relative_to(args.work))], check=True)
        subprocess.run(["git", "-C", str(args.work), "-c", "user.name=Cache owner fixture",
                        "-c", "user.email=fixture@example.invalid", "commit", "-q", "-m",
                        "test: freeze production cache owner projection"], check=True)
    cache = args.work / "native-cache"
    cache.mkdir(exist_ok=args.retry)
    binary = args.work / "cache-owner-projection"
    command = [str(args.compiler), "native-build", str(source), "--backend", "llvm",
               "--runtime-bundle", "core-c-bootstrap", "--runtime-path", str(args.runtime),
               "--threads", "2", "--cache-dir", str(cache), "--mode", "one-binary", "--output", str(binary)]
    env = os.environ.copy()
    env.update(SIMPLE_NATIVE_BUILD_CACHE_DIR=str(cache), SIMPLE_FRONTEND_CACHE_DIR=str(args.work / "frontend-cache"),
               SIMPLE_NO_STUB_FALLBACK="1", SIMPLE_RUNTIME_PATH=str(args.runtime), SIMPLE_SCV_INVENTORY_COLD_INIT="1")
    evidence = {"schema": "native-cache-owner-projection-v1", "source_sha256": originals,
                "projection_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "compiler_sha256": hashlib.sha256(args.compiler.read_bytes()).hexdigest(),
                "argv": command, "negative_control": args.negative_control,
                "qualification": "production owner bodies with recording driver; not full compiler/bootstrap"}
    (args.work / "plan.json").write_text(json.dumps(evidence, indent=2))
    with (args.work / "compile.log").open("w") as log:
        compiled = subprocess.run(command, cwd=args.work, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=120)
    if compiled.returncode or not binary.is_file():
        raise SystemExit("FAIL: native fixture compilation; see " + str(args.work / "compile.log"))
    ran = subprocess.run([str(binary)], cwd=args.work, env=env, capture_output=True, text=True, timeout=15)
    (args.work / "run.log").write_text(ran.stdout + ran.stderr)
    evidence["run_exit"] = ran.returncode
    routed = ran.returncode == 0 and all(
        Path(path, leaf).is_file() and Path(path, leaf).read_text() == selected
        for path, selected in requested
        for leaf in ("native_provider_identity.receipt", "build_cache.sdn", "reverse-references/CURRENT"))
    inherited_untouched = not Path(paths["inherited"], "build_cache.sdn").exists()
    evidence.update(routed=routed, inherited_untouched=inherited_untouched)
    passed = (not routed and not inherited_untouched) if args.negative_control else (routed and inherited_untouched)
    evidence["status"] = "PASS" if passed else "FAIL"
    (args.work / "result.json").write_text(json.dumps(evidence, indent=2))
    print(evidence["status"] + ": native cache owner " + ("ignored-CLI negative control" if args.negative_control else "routing/restoration/filesystem"))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())

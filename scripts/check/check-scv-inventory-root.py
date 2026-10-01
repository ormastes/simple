#!/usr/bin/env python3
"""Execute the production SCV root resolver in a tiny isolated native fixture.

The existing producer needs its own inventory-compatible SIMPLE_CACHE during
compilation. The resulting probe runs against default and conflicting machine
cache environments without that setting. No compiler import closure is built.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def extract(source, name):
    pattern = r"^(?:pub )?fn " + re.escape(name) + r"\(.*?(?=^(?:(?:pub )?fn |export |struct |val |var |@)|\Z)"
    found = re.search(pattern, source, re.M | re.S)
    if not found:
        raise ValueError("missing production function: " + name)
    return found.group().rstrip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("repo", "compiler", "runtime", "work"):
        parser.add_argument("--" + key, required=True, type=Path)
    parser.add_argument("--machine-baseline", type=Path,
                        help="git-show blob captured on the worktree's owning host")
    args = parser.parse_args()
    args.work.mkdir(parents=True, exist_ok=False)
    paths = {
        "core": "src/lib/scv/compile_source_inventory_core.spl",
        "publisher": "src/app/compiler_entrypoint/admission.spl",
        "authority": "src/app/compiler_entrypoint/source_authority.spl",
        "native_closure": "src/app/io/_CliCompile/native_build_closure.spl",
        "hir": "src/compiler/80.driver/driver_hir_pipeline_lowering.spl",
        "snapshot": "src/lib/scv/compile_snapshot.spl",
        "runtime": "src/lib/nogc_sync_mut/io_runtime.spl",
        "sosix": "src/lib/nogc_async_mut/sosix/environment.spl",
        "machine": "src/compiler/80.driver/cache/cache_root.spl",
    }
    code = {key: (args.repo / value).read_text() for key, value in paths.items()}
    assert "compile_source_inventory_checkout_cache_root_v1(root)" in code["publisher"]
    assert "compile_source_inventory_read_current_v1(inventory_cache_root)" in code["hir"]
    assert "compile_source_inventory_read_current_v1(machine_cache_root())" not in code["hir"]
    assert "inventory_binding, admitted.digest" in code["hir"]
    assert "source_root, inventory_binding.source_inventory_digest, inventory" in code["hir"]
    assert "compiler_source_authority_acquire_v1(" in code["publisher"]
    assert "compiler_source_authority_publish_v1(authority)" in code["publisher"]
    assert "compiler_source_authority_acquire_v1(" in code["native_closure"]
    assert "compiler_source_authority_publish_v1(authority)" in code["native_closure"]
    assert "val snapshot = scv_compile_snapshot_acquire_v1(root, cache_root, source_roots)" in code["authority"]
    assert "compile_source_inventory_read_current_v1(cache_root)" in code["authority"]
    assert "refresh.inventory_digest, refresh.inventory_generation, false" in code["authority"]
    assert 'env_set("SIMPLE_SCV_SOURCE_INVENTORY_DIGEST", authority.source_inventory_digest)' in code["authority"]
    assert 'env_set("SIMPLE_SCV_INVENTORY_DIGEST", snapshot.inventory_digest)' in code["authority"]
    assert code["authority"].index('env_set("SIMPLE_SCV_SOURCE_INVENTORY_DIGEST"') < code["authority"].index('env_set("SIMPLE_SCV_SNAPSHOT_ROOT"')
    assert "sosix_cwd(), source_root" in code["hir"]
    assert "cwd_process as sosix_cwd" in code["sosix"]
    assert "compile_source_inventory_snapshot_cache_root_v1(" in code["snapshot"]
    assert "snapshot-open-not-owned" in code["snapshot"]
    assert "snapshot-open-receipt-mismatch" in code["snapshot"]
    machine_before = args.machine_baseline.read_text() if args.machine_baseline else subprocess.check_output(
        ["git", "-C", str(args.repo), "show", "HEAD:" + paths["machine"]], text=True)
    assert machine_before == code["machine"], "machine cache override contract changed"
    names = ["compile_source_inventory_digest_valid_v1", "compile_source_inventory_cache_root_valid_v1",
             "compile_source_inventory_plain_checkout_v1", "compile_source_inventory_checkout_cache_root_v1",
             "compile_source_inventory_snapshot_cache_root_v1", "compile_source_inventory_binding_reason_v1"]
    pieces = [extract(code["core"], name) for name in names]
    pieces.insert(0, re.search(r"(?ms)^struct CompileSourceInventoryBindingV1:.*?(?=^fn )", code["core"]).group().rstrip())
    assert "env_get_nullable as sosix_env_get_nullable" in code["sosix"]
    pieces.append(extract(code["runtime"], "env_get_nullable").replace("fn env_get_nullable(", "fn sosix_env_get_nullable(", 1))
    declaration = re.search(r"(?m)^extern fn rt_env_get\([^\n]+", code["runtime"]).group()
    pieces.append('@unsafe(reason: "production SOSIX environment owner projection", capabilities: [ffi])\n' + declaration)
    revision = "scv-revision-v1-" + "a" * 64
    root = str(args.work / "checkout")
    cases = [(root, root + "/build/scv/snapshots/" + revision, revision, root + "/build/scv"),
             (root, root + "/.simple/scv/snapshots/" + revision, revision, root + "/.simple/scv"),
             ("C:\\work\\project", "C:/work/project/build/scv/snapshots/" + revision, revision, "C:/work/project/build/scv"),
             ("\\\\?\\UNC\\server\\share\\project", "//server/share/project/build/scv/snapshots/" + revision, revision, "//server/share/project/build/scv"),
             (root + "/child", root + "/build/scv/snapshots/" + revision, revision, ""),
             ("/work/a\\b", "/work/a\\b/build/scv/snapshots/" + revision, revision, "/work/a\\b/build/scv"),
             (root, root + "/build/scv/snapshots/" + revision, "", ""),
             (root, root + "/build/scv/snapshots/" + revision, revision + "f", ""),
             (root, root + "/build/scv/snapshots/" + revision, "scv-revision-v1-" + "b" * 64, "")]
    for bad in ("/foreign/build/scv/snapshots/" + revision,
                root + "/../other/build/scv/snapshots/" + revision,
                root + "/build/scv/snapshots/" + revision + "/extra",
                root + "/build/scv/snapshots/malformed", "relative/build/scv/snapshots/" + revision):
        cases.append((root, bad, revision, ""))
    checks = [f"    if compile_source_inventory_snapshot_cache_root_v1({json.dumps(a)}, {json.dumps(b)}, {json.dumps(c)}) != {json.dumps(d)}: return {index}"
              for index, (a, b, c, d) in enumerate(cases, 1)]
    canonical_digest = hashlib.sha256(b"simple-compile-source-inventory-v1\ngeneration=1\ncount=0").hexdigest()
    manifest_digest = hashlib.sha256(b"").hexdigest()
    changed_digest = hashlib.sha256(b"simple-compile-source-inventory-v1\ngeneration=2\ncount=0").hexdigest()
    assert canonical_digest != manifest_digest
    checks += [f'    val correct = CompileSourceInventoryBindingV1("{manifest_digest}", "{canonical_digest}")',
               f'    if compile_source_inventory_binding_reason_v1(correct, "{canonical_digest}") != "ok": return 40',
               f'    if compile_source_inventory_binding_reason_v1(correct, "{manifest_digest}") != "source-inventory-digest-mismatch": return 41',
               f'    val swapped = CompileSourceInventoryBindingV1("{canonical_digest}", "{manifest_digest}")',
               f'    if compile_source_inventory_binding_reason_v1(swapped, "{canonical_digest}") != "source-inventory-digest-mismatch": return 42',
               f'    val missing = CompileSourceInventoryBindingV1("{manifest_digest}", "")',
               f'    if compile_source_inventory_binding_reason_v1(missing, "{canonical_digest}") != "source-inventory-digest-invalid": return 43',
               f'    val malformed = CompileSourceInventoryBindingV1("bad", "{canonical_digest}")',
               f'    if compile_source_inventory_binding_reason_v1(malformed, "{canonical_digest}") != "snapshot-manifest-digest-invalid": return 44',
               f'    if compile_source_inventory_binding_reason_v1(correct, "{changed_digest}") != "source-inventory-digest-mismatch": return 45',
               f"    if compile_source_inventory_checkout_cache_root_v1({json.dumps(root)}) != {json.dumps(root + '/build/scv')}: return 30",
               '    if compile_source_inventory_cache_root_valid_v1("/home/user/.cache/simple/v1/projects/default"): return 31',
               '    val before = sosix_env_get_nullable("SIMPLE_CACHE") ?? ""',
               '    val expected = sosix_env_get_nullable("SCV_TEST_EXPECT_MACHINE_CACHE") ?? ""',
               '    if before != expected: return 32',
               '    print "PASS: production SCV inventory resolver"', '    0']
    pieces.append("fn main() -> i64:\n" + "\n".join(checks))
    (args.work / "src").mkdir()
    source = args.work / "src" / "inventory-root-projection.spl"
    source.write_text("\n\n".join(pieces) + "\n")
    assert not re.search(r"(?m)^(?:export )?use ", source.read_text())
    (args.work / ".gitignore").write_text("*\n!.gitignore\n!src/\n!src/inventory-root-projection.spl\n")
    subprocess.run(["git", "init", "-q", str(args.work)], check=True)
    subprocess.run(["git", "-C", str(args.work), "add", ".gitignore", "src/inventory-root-projection.spl"], check=True)
    subprocess.run(["git", "-C", str(args.work), "-c", "user.name=SCV root fixture", "-c",
                    "user.email=fixture@example.invalid", "commit", "-q", "-m", "test: freeze SCV root production projection"], check=True)
    head = subprocess.check_output(["git", "-C", str(args.work), "rev-parse", "HEAD"], text=True).strip()
    listed = subprocess.check_output(["git", "-C", str(args.work), "ls-files", "--", "src"], text=True).splitlines()
    assert listed == ["src/inventory-root-projection.spl"]
    cache = args.work / "native-cache"
    cache.mkdir()
    binary = args.work / "inventory-root-projection"
    command = [str(args.compiler), "native-build", str(source), "--backend", "llvm", "--runtime-bundle",
               "core-c-bootstrap", "--runtime-path", str(args.runtime), "--threads", "2", "--cache-dir", str(cache),
               "--mode", "one-binary", "--output", str(binary)]
    env = os.environ.copy()
    env.update(SIMPLE_CACHE=str(args.work / "build/scv"), SIMPLE_NATIVE_BUILD_CACHE_DIR=str(cache),
               SIMPLE_FRONTEND_CACHE_DIR=str(args.work / "frontend-cache"), SIMPLE_NO_STUB_FALLBACK="1",
               SIMPLE_RUNTIME_PATH=str(args.runtime), SIMPLE_SCV_INVENTORY_COLD_INIT="1")
    assert command[command.index("--cache-dir") + 1] == env["SIMPLE_NATIVE_BUILD_CACHE_DIR"]
    assert env["SIMPLE_CACHE"].endswith("/build/scv") and args.compiler.is_file() and args.runtime.is_dir()
    evidence = {"schema": "scv-inventory-root-native-projection-v1", "git_head": head, "tracked_sources": listed,
                "source_hashes": {paths[k]: hashlib.sha256(v.encode()).hexdigest() for k, v in code.items()},
                "projection_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "compiler_sha256": hashlib.sha256(args.compiler.read_bytes()).hexdigest(), "argv": command,
                "cache_environment": {k: env[k] for k in ("SIMPLE_CACHE", "SIMPLE_NATIVE_BUILD_CACHE_DIR", "SIMPLE_FRONTEND_CACHE_DIR")},
                "qualification": "production resolver projection and source wiring; not rebuilt compiler/bootstrap"}
    (args.work / "plan.json").write_text(json.dumps(evidence, indent=2))
    with (args.work / "compile.log").open("w") as log:
        result = subprocess.run(command, cwd=args.work, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=120)
    if result.returncode or not binary.exists():
        print("FAIL: tiny native compilation; inspect " + str(args.work / "compile.log"))
        return 1
    runs = []
    for label, override in (("default", ""), ("explicit-machine", "/external/machine-cache"),
                            ("explicit-other-checkout", "/other/checkout/build/scv")):
        run_env = env.copy()
        run_env["SCV_TEST_EXPECT_MACHINE_CACHE"] = override
        if override:
            run_env["SIMPLE_CACHE"] = override
        else:
            run_env.pop("SIMPLE_CACHE", None)
        run = subprocess.run([str(binary)], cwd=args.work, env=run_env, capture_output=True, text=True, timeout=10)
        runs.append({"case": label, "exit": run.returncode, "output": run.stdout + run.stderr})
    passed = all(run["exit"] == 0 and "PASS: production SCV inventory resolver" in run["output"] for run in runs)
    evidence.update(status="PASS" if passed else "FAIL", runs=runs)
    (args.work / "result.json").write_text(json.dumps(evidence, indent=2))
    print(evidence["status"] + ": native inventory root agreement/default/overrides/containment/revision")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())

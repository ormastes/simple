#!/usr/bin/env python3
"""Real Git + shell guard fixtures; retains every private fixture and receipt.

No Simple compiler/runtime is used. Pass --output NEW_DIRECTORY and --shell SH.
"""
import argparse
import hashlib
import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


def run(argv, cwd):
    return subprocess.run(argv, cwd=cwd, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=30)


def git(repo, *args, data=None):
    result = subprocess.run(["git", *args], cwd=repo, input=data,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=15, check=True)
    return result.stdout.strip()


def junction(target, alias):
    if os.name == "nt":
        import _winapi
        _winapi.CreateJunction(str(target), str(alias))
    else:
        alias.symlink_to(os.path.relpath(target, alias.parent), target_is_directory=True)


def deadline_probe(kind, source, output):
    """Execute the real supervisor with a blocked child/read boundary.

    The child is a retained Python fixture, not a claim that Git itself hung.
    No production test switch or duplicate deadline implementation is used.
    """
    spec = importlib.util.spec_from_file_location("alias_classifier", source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.WALL_SECONDS = 0.2
    children = []
    original = subprocess.Popen
    if kind in ("child", "exception"):
        def blocked_child(argv, **kwargs):
            child = original([sys.executable, "-c", "import time; time.sleep(60)"], **kwargs)
            children.append(child)
            return child
        module.subprocess.Popen = blocked_child
        if kind == "exception":
            def fail_after_spawn(logical):
                blocked_child([], stdin=subprocess.DEVNULL,
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                raise RuntimeError("controlled exception after owned child spawn")
            module.classify = fail_after_spawn
    else:
        def blocked_read(root, logical):
            time.sleep(60)
            return True
        module.unchanged = blocked_read
    started = time.monotonic()
    accepted = False
    error = ""
    cleanup_errors = []
    supervisor_reaped = False
    try:
        accepted = module.classify("src/app/tool/leaf.spl")
    except BaseException as failure:
        error = type(failure).__name__ + ": " + str(failure)
    finally:
        elapsed = time.monotonic() - started
        module.subprocess.Popen = original
        # Snapshot the production result BEFORE harness cleanup: cleanup must
        # never turn a leaked production child into a successful deadline test.
        supervisor_reaped = all(child.returncode is not None for child in children)
        for child in children:
            try:
                if child.poll() is None:
                    child.kill()
                child.wait(timeout=2)
            except (OSError, subprocess.SubprocessError) as failure:
                cleanup_errors.append(type(failure).__name__ + ": " + str(failure))
    reaped = all(child.returncode is not None and child.poll() is not None for child in children)
    ok = (not error and not cleanup_errors and not accepted
          and 0.15 <= elapsed < 2.0 and supervisor_reaped and reaped
          and (kind != "child" or len(children) == 1))
    # Error messages are SDN strings, not unescaped exception text.
    def quoted(value):
        return '"' + value.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\r', '\\r') + '"'
    lines = [f'kind: "{kind}"', f'accepted: {str(accepted).lower()}',
             f'elapsed_seconds: {elapsed:.6f}', f'children: {len(children)}',
             f'error: {quoted(error)}',
             f'supervisor_children_reaped: {str(supervisor_reaped).lower()}',
             f'all_children_reaped: {str(reaped).lower()}', f'passed: {str(ok).lower()}']
    lines += ['cleanup_errors: [' + ', '.join(quoted(e) for e in cleanup_errors) + ']']
    for child in children:
        lines += [f'child_pid: {child.pid}', f'child_exit: {child.returncode}']
    Path(output).write_text("\n".join(lines) + "\n", encoding="utf-8")
    os._exit(0 if ok else 1)


def exception_control(output):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).resolve().parents[2]
    result = run([sys.executable, str(Path(__file__).resolve()), "--deadline-probe", "exception",
                  str(source / "scripts/audit/unchanged-materialized-alias.py"),
                  str(output / "failed-probe.sdn")], source)
    (output / "probe.log").write_bytes(result.stdout)
    receipt = (output / "failed-probe.sdn").read_text(encoding="utf-8").splitlines()
    expected = {'error: "RuntimeError: controlled exception after owned child spawn"',
                'children: 1', 'supervisor_children_reaped: false',
                'all_children_reaped: true', 'cleanup_errors: []', 'passed: false'}
    ok = result.returncode == 1 and expected.issubset(set(receipt))
    digest = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (output / "receipt.sdn").write_text(
        'schema: "env-guard-exception-cleanup-control-v1"\n'
        f'probe_exit: {result.returncode}\ncase_count: 1\npassed: {str(ok).lower()}\n'
        'native_sspec_executed: 0\n'
        f'harness_sha256: "{digest}"\n', encoding="utf-8")
    print(f"exception-cleanup: probe_exit={result.returncode} {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--shell", required=True)
    parser.add_argument("--resource-only", action="store_true")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)  # never overwrite or clean a run
    source = Path(__file__).resolve().parents[2]
    names = ["unchanged", "modified", "new-descendant", "retargeted",
             "untracked-alias", "staged-alias", "staged-leaf", "missing-target",
             "escaping-target", "filter", "encoding", "ordinary-app",
             "allowed-owner", "nested-reparse", "forged-receipt", "crlf-difference"]
    if args.resource_only:
        names = ["source-ceiling", "oversized-current", "oversized-blob", "oversized-alias"]
    receipts = []
    for name in names:
        case = output / name
        repo = case / "repo"
        (repo / "scripts/audit").mkdir(parents=True)
        for filename in ("direct-env-runtime-guard.shs", "unchanged-materialized-alias.py"):
            shutil.copyfile(source / "scripts/audit" / filename,
                            repo / "scripts/audit" / filename)
        target = repo / "examples/tool"
        target.mkdir(parents=True)
        leaf = target / "leaf.spl"
        leaf.write_bytes(b'fn probe():\n    rt_env_get("OLD")\n')
        if name in ("source-ceiling", "oversized-blob"):
            size = 1024 * 1024 + (1 if name == "oversized-blob" else 0)
            prefix = leaf.read_bytes()
            leaf.write_bytes(prefix + b"#" * (size - len(prefix)))
        alias = repo / "src/app/tool"
        alias.parent.mkdir(parents=True)
        alias.write_bytes(b"../../examples/tool")
        git(repo, "init", "-q")
        git(repo, "config", "user.name", "Guard fixture")
        git(repo, "config", "user.email", "guard-fixture@example.invalid")
        git(repo, "config", "core.autocrlf", "false")
        git(repo, "config", "core.symlinks", "false")
        git(repo, "add", ".")
        declaration = b"../../examples/tool"
        if name == "oversized-alias":
            declaration += b"/." * 2048
        blob = git(repo, "hash-object", "-w", "--stdin", data=declaration).decode()
        git(repo, "update-index", "--cacheinfo", f"120000,{blob},src/app/tool")
        tree = git(repo, "write-tree").decode()
        commit = git(repo, "commit-tree", tree, "-m", "Private guard fixture").decode()
        git(repo, "update-ref", "HEAD", commit)
        alias.unlink()  # private regular placeholder, never a recursive removal
        destination = target
        expected_guard = 0
        expected_classifier = 0
        if name not in ("unchanged", "allowed-owner", "source-ceiling"):
            expected_guard = expected_classifier = 1
        if name == "modified":
            leaf.write_bytes(leaf.read_bytes() + b'    rt_env_get("NEW")\n')
        elif name == "new-descendant":
            (target / "new.spl").write_bytes(b'rt_env_get("NEW")\n')
        elif name == "retargeted":
            destination = repo / "examples/other"
            destination.mkdir()
            (destination / "leaf.spl").write_bytes(leaf.read_bytes())
        elif name == "untracked-alias":
            alias = repo / "src/app/new-tool"
        elif name == "staged-alias":
            other = git(repo, "hash-object", "-w", "--stdin", data=b"../../examples/other").decode()
            git(repo, "update-index", "--cacheinfo", f"120000,{other},src/app/tool")
        elif name == "staged-leaf":
            other = git(repo, "hash-object", "-w", "--stdin", data=b'rt_env_get("STAGED")\n').decode()
            git(repo, "update-index", "--cacheinfo", f"100644,{other},examples/tool/leaf.spl")
        elif name == "missing-target":
            leaf.unlink()
            expected_guard = 0  # no file/call remains; classifier must refuse
        elif name == "escaping-target":
            destination = case / "outside"
            destination.mkdir()
            (destination / "leaf.spl").write_bytes(leaf.read_bytes())
        elif name in ("filter", "encoding"):
            attr = "filter=ambiguous" if name == "filter" else "working-tree-encoding=UTF-8"
            (repo / ".gitattributes").write_text(f"examples/tool/*.spl {attr}\n", encoding="utf-8")
        elif name == "ordinary-app":
            (alias.parent / "new.spl").write_bytes(b'rt_env_get("NEW")\n')
            expected_classifier = 0  # unchanged alias remains a valid duplicate
        elif name == "allowed-owner":
            owner = alias.parent / "io/process_ops.spl"
            owner.parent.mkdir()
            owner.write_bytes(b'rt_env_get("OWNER")\n')
        elif name == "nested-reparse":
            # A descendant alias must never be mistaken for a committed leaf.
            nested = target / "nested"
            junction(target, nested)
        elif name == "forged-receipt":
            (repo / "fake-receipt.sdn").write_text('result: "complete"\n', encoding="utf-8")
            leaf.write_bytes(b'rt_env_get("CHANGED")\n')
        elif name == "crlf-difference":
            leaf.write_bytes(leaf.read_bytes().replace(b"\n", b"\r\n"))
        elif name == "oversized-current":
            leaf.write_bytes(b'rt_env_get("NEW")\n' + b"#" * (1024 * 1024))
        elif name == "oversized-blob":
            leaf.write_bytes(b'rt_env_get("OLD")\n')
        junction(destination, alias)
        logical = alias.relative_to(repo).as_posix() + "/leaf.spl"
        if name == "new-descendant":
            logical = alias.relative_to(repo).as_posix() + "/new.spl"
        elif name == "nested-reparse":
            logical = alias.relative_to(repo).as_posix() + "/nested/leaf.spl"
        classifier = run([sys.executable, "scripts/audit/unchanged-materialized-alias.py", logical], repo)
        # The nested link is a loop; do not ask Git to recursively enumerate it.
        guard = None if name == "nested-reparse" else run(
            [args.shell, "scripts/audit/direct-env-runtime-guard.shs", "--working"], repo)
        (case / "classifier.log").write_bytes(classifier.stdout)
        if guard is not None:
            (case / "guard.log").write_bytes(guard.stdout)
        ok = classifier.returncode == expected_classifier and (
            guard is None or guard.returncode == expected_guard)
        receipts.append((name, classifier.returncode,
                         -1 if guard is None else guard.returncode, ok))
        print(f"{name}: classifier={classifier.returncode} guard={'NOT_RUN' if guard is None else guard.returncode} {'PASS' if ok else 'FAIL'}", flush=True)
    if args.resource_only:
        for kind in ("child", "read"):
            case = output / ("deadline-" + kind)
            case.mkdir()
            result = run([sys.executable, str(Path(__file__).resolve()), "--deadline-probe", kind,
                          str(source / "scripts/audit/unchanged-materialized-alias.py"),
                          str(case / "probe.sdn")], source)
            (case / "probe.log").write_bytes(result.stdout)
            receipts.append(("deadline-" + kind, result.returncode, -1, result.returncode == 0))
            print(f"deadline-{kind}: probe_exit={result.returncode} {'PASS' if result.returncode == 0 else 'FAIL'}", flush=True)
    lines = ['schema: "env-guard-alias-fixtures-v1"', 'native_sspec_executed: 0',
             f'case_count: {len(receipts)}', f'passed: {sum(r[3] for r in receipts)}',
             'cases: [']
    for name, classifier, guard, ok in receipts:
        lines.append(f'  {{ name: "{name}", classifier_exit: {classifier}, guard_exit: {guard}, passed: {str(ok).lower()} }},')
    lines.append(']')
    lines.append('source_sha256: [')
    for relative in ("scripts/audit/direct-env-runtime-guard.shs",
                     "scripts/audit/unchanged-materialized-alias.py",
                     "scripts/check/check-env-guard-materialized-aliases.py"):
        digest = hashlib.sha256((source / relative).read_bytes()).hexdigest()
        lines.append(f'  {{ path: "{relative}", sha256: "{digest}" }},')
    lines.append(']')
    (output / "receipt.sdn").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return 0 if all(r[3] for r in receipts) else 1


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--exception-control":
        sys.exit(exception_control(sys.argv[2]))
    if len(sys.argv) == 5 and sys.argv[1] == "--deadline-probe":
        deadline_probe(*sys.argv[2:])
    sys.exit(main())

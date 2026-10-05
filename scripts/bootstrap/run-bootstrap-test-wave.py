#!/usr/bin/env python3
"""Retained 40-slot callback: Phase1 whole tests and six Phase2 products.

Invoke only as a hash-bound task of the canonical managed owner, with its
resource row reserving 40 CPU slots and both children in the owner's process
tree. This callback creates no detached process, reservation or alternate
scheduler. It reserves 20 for Phase1 and 20 for the sequential product owner.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import time
from pathlib import Path


def digest(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError('regular input required: ' + str(path))
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def publish(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')
    temporary.replace(path)


def ensure_phase1_terminal(output, child_exit, request_sha):
    """A callback startup crash is terminal infrastructure failure, not a hang."""
    receipt = output / 'result.json'
    if receipt.exists():
        return
    for name in ('stdout.log', 'stderr.log'):
        if not (output / name).exists():
            (output / name).touch(exist_ok=False)
    publish(receipt, dict(schema='simple-phase1-whole-tests-result-v1', phase='phase1',
        status='INFRASTRUCTURE_FAILED', process_exit=child_exit, runner_summary=None,
        reason='Phase1 callback terminated without its runner completion receipt',
        request_sha256=request_sha, stdout_sha256=digest(output / 'stdout.log'),
        stderr_sha256=digest(output / 'stderr.log'),
        qualification='callback infrastructure failure; zero test acceptance'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('source-root', 'output-root', 'seed', 'shell', 'compiler-llvm',
                 'compiler-cranelift', 'producer-receipt-llvm', 'producer-receipt-cranelift'):
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('--seed-sha256', required=True)
    parser.add_argument('--tool-root', type=Path)
    parser.add_argument('--tool-manifest', type=Path)
    parser.add_argument('--tool-manifest-sha256')
    parser.add_argument('--admitted-jobs', required=True, type=int)
    parser.add_argument('--rss-cap-kib', required=True, type=int)
    # Full bootstrap preserves the existing qualified-product resource policy.
    # Diagnostic monitor-only products remain distinct, never matrix admission.
    parser.add_argument('--rss-mode', choices=('enforce',), default='enforce')
    parser.add_argument('--build-timeout-seconds', type=int, default=1800)
    parser.add_argument('--test-timeout-seconds', type=int, default=7200)
    args = parser.parse_args()
    if (args.admitted_jobs != 40 or args.rss_cap_kib < 1
            or args.build_timeout_seconds < 1 or args.test_timeout_seconds < 1):
        parser.error('one aggregate 40-slot reservation is required; each child uses 20')
    source, output = args.source_root.resolve(), args.output_root.resolve()
    if args.source_root.is_symlink() or not source.is_dir() or output.is_relative_to(source):
        parser.error('separate physical source/output roots required')
    if digest(args.seed) != args.seed_sha256:
        parser.error('Phase1 seed bytes differ')
    source_head = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'],
                                          text=True).strip()
    tool_root = (args.tool_root or source).resolve()
    scripts = tool_root / 'scripts/bootstrap'
    tool_authority = None
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    if tool_root != source:
        if not args.tool_manifest or not args.tool_manifest_sha256:
            parser.error('separate tool root requires a pinned complete tool manifest')
        authority_spec = importlib.util.spec_from_file_location(
            'tool_code_authority', scripts / 'tool-code-authority.py')
        tool_authority = importlib.util.module_from_spec(authority_spec)
        authority_spec.loader.exec_module(tool_authority)
        tool_authority.validate(tool_root, args.tool_manifest,
                                args.tool_manifest_sha256, Path(__file__))
        environment.update(SIMPLE_BOOTSTRAP_TOOL_ROOT=str(tool_root),
            SIMPLE_BOOTSTRAP_TOOL_MANIFEST=str(args.tool_manifest.resolve()),
            SIMPLE_BOOTSTRAP_TOOL_MANIFEST_SHA256=args.tool_manifest_sha256,
            SIMPLE_BOOTSTRAP_TOOL_PYTHON=sys.executable)
    elif any(os.environ.get(key) for key in ('SIMPLE_BOOTSTRAP_TOOL_ROOT',
             'SIMPLE_BOOTSTRAP_TOOL_MANIFEST', 'SIMPLE_BOOTSTRAP_TOOL_MANIFEST_SHA256')):
        parser.error('inherited tool authority requires explicit separate tool arguments')
    callback = scripts / 'phase1-whole-tests.py'
    product = scripts / 'run-compiler-subsystem-test-products.shs'
    gate_path = scripts / 'phase1-terminal-gate.py'
    pins = {str(p): digest(p) for p in (callback, product, gate_path, args.seed, args.shell,
        args.compiler_llvm, args.compiler_cranelift, args.producer_receipt_llvm,
        args.producer_receipt_cranelift)}
    if tool_authority:
        pins[str(args.tool_manifest.resolve())] = args.tool_manifest_sha256
    output.mkdir(parents=True, exist_ok=False)
    phase1 = output / 'phase1'
    products = output / 'products'
    common = [sys.executable, str(callback), '--seed', str(args.seed.resolve()),
        '--seed-sha256', args.seed_sha256, '--source-root', str(source),
        '--output-root', str(phase1), '--jobs', '20']
    # Request preparation executes no seed/test process. Its immutable digest
    # is available before either child starts and is the product gate identity.
    subprocess.run(common + ['--prepare-only'], cwd=source, env=environment, check=True)
    phase1_sha = digest(phase1 / 'request.json')
    product_command = [str(args.shell.resolve()), str(product), '--producer-phase=phase2',
        '--source-root=' + str(source), '--output-root=' + str(products), '--threads=20',
        '--rss-cap-kib=' + str(args.rss_cap_kib), '--rss-mode=' + args.rss_mode,
        '--build-timeout-seconds=' + str(args.build_timeout_seconds),
        '--test-timeout-seconds=' + str(args.test_timeout_seconds),
        '--await-phase1-receipt=' + str(phase1 / 'result.json'),
        '--phase1-request-sha256=' + phase1_sha, '--phase1-python=' + sys.executable]
    for backend in ('llvm', 'cranelift'):
        for field in ('compiler', 'producer-receipt'):
            path = getattr(args, (field + '-' + backend).replace('-', '_')).resolve()
            product_command.append('--' + field + '-' + backend + '=' + str(path))
    commands = {'phase1': common + ['--resume-prepared'], 'products': product_command}
    publish(output / 'request.json', dict(schema='simple-bootstrap-test-wave-v1',
        admitted_jobs=40, child_jobs={'phase1': 20, 'products': 20}, commands=commands,
        input_hashes=pins, phase1_request_sha256=phase1_sha,
        source_root=str(source), source_head=source_head, tool_root=str(tool_root),
        tool_manifest_sha256=args.tool_manifest_sha256,
        tool_head=tool_authority.validate(tool_root, args.tool_manifest,
            args.tool_manifest_sha256, Path(__file__))['tool_head'] if tool_authority else None,
        tool_environment={key: value for key, value in environment.items()
                          if key.startswith('SIMPLE_BOOTSTRAP_TOOL_')},
        full_product_dependency='exact Phase1 terminal; PASS not required',
        early_smoke='authentic one-case result, separate from fresh full-suite counts'))
    handles = []
    children = {}
    try:
        for name, command in commands.items():
            stdout = (output / (name + '-callback.stdout.log')).open('xb')
            stderr = (output / (name + '-callback.stderr.log')).open('xb')
            handles.extend((stdout, stderr))
            children[name] = subprocess.Popen(command, cwd=source, env=environment,
                                               stdout=stdout, stderr=stderr)
        publish(output / 'children.json', {name: child.pid for name, child in children.items()})
        phase1_closed = False
        while any(child.poll() is None for child in children.values()):
            if not phase1_closed and children['phase1'].poll() is not None:
                ensure_phase1_terminal(phase1, children['phase1'].returncode, phase1_sha)
                phase1_closed = True
            time.sleep(0.2)
        ensure_phase1_terminal(phase1, children['phase1'].returncode, phase1_sha)
    finally:
        for stream in handles:
            stream.close()
        # Unexpected owner failure exits to canonical parent containment. Never
        # detach surviving children or claim their leases closed here.
    spec = importlib.util.spec_from_file_location('phase1_terminal_gate', gate_path)
    gate = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gate)
    terminal = gate.validate_terminal(phase1 / 'result.json', phase1_sha)
    matrix = products / 'matrix.env'
    matrix_digest = digest(matrix) if matrix.is_file() else None
    matrix_pass = False
    if matrix_digest and matrix.stat().st_size <= 4 * 1024 * 1024:
        statuses = [line[7:] for line in matrix.read_text(encoding='utf-8').splitlines()
                    if line.startswith('status=')]
        matrix_pass = statuses == ['PASS']
    unchanged = all(digest(Path(path)) == sha for path, sha in pins.items())
    unchanged = unchanged and source_head == subprocess.check_output(
        ['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
    if tool_authority:
        tool_authority.validate(tool_root, args.tool_manifest,
                                args.tool_manifest_sha256, Path(__file__))
    passed = (unchanged and terminal['status'] == 'PASS' and matrix_pass
              and all(child.returncode == 0 for child in children.values()))
    publish(output / 'result.json', dict(schema='simple-bootstrap-test-wave-result-v1',
        status='PASS' if passed else 'FAIL', phase1_status=terminal['status'],
        child_exits={name: child.returncode for name, child in children.items()},
        matrix_sha256=matrix_digest, phase1_terminal_sha256=digest(phase1 / 'result.json'),
        unchanged=unchanged, admission='canonical parent receipt still required'))
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())

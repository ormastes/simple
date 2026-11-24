#!/usr/bin/env python3
"""One provisional full CLI from verified recovered Linux Phase3; stage only until parent proof."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from parent_gate import verify as verify_ce231_parent, SOURCE
PARENT_PROOF = {}
PARENT = ''
RUNTIME = {}


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def checked_env(path):
    fields = {}
    for line in path.read_text().splitlines():
        key, value = line.split('=', 1)
        if key in fields:
            raise RuntimeError('duplicate parent receipt field: '+key)
        fields[key] = value
    return fields




def main():
    global PARENT, RUNTIME, PARENT_PROOF
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--parent-sha256', required=True)
    parser.add_argument('--parent-artifact-id', required=True, type=int)
    parser.add_argument('--parent-evidence', required=True, type=Path)
    args = parser.parse_args()
    if not re.fullmatch(r'[0-9a-f]{64}', args.parent_sha256):
        raise RuntimeError('actual verified parent SHA-256 required')
    PARENT = args.parent_sha256
    source = args.source.resolve()
    root = source/'build/phase4-from-ce231-phase3'
    evidence = root/'evidence'
    evidence.mkdir(parents=True, exist_ok=False)
    product = root/'product'
    product.mkdir()
    for name in ('cache/frontend', 'cache/hir', 'tmp', 'storage', 'xdg-cache'):
        (root/name).mkdir(parents=True)
    parent = root/'parent/simple'
    runtime = root/'runtime'
    current = 'identity'
    result = {'status': 'in_progress', 'admission': 'none', 'scope': 'provisional-phase4-full-cli-from-recovered-phase3',
              'source': SOURCE, 'producer_sha256': PARENT, 'runtime_sha256': RUNTIME,
              'parent_run': None, 'parent_artifact': args.parent_artifact_id,
              'runtime_artifact': 14871469985, 'formal_authority': 'unavailable; no managed admission claimed'}
    env = dict(os.environ)
    for key in list(env):
        if key.startswith('SIMPLE_'):
            del env[key]
    env.update(SIMPLE_BINARY=str(parent), SIMPLE_RUNTIME_PATH=str(runtime),
        SIMPLE_NO_STUB_FALLBACK='1', SIMPLE_NATIVE_BUILD_RUST='0',
        SIMPLE_BOOTSTRAP_STAGE3='0', SIMPLE_BOOTSTRAP_STAGE4='0',
        SIMPLE_FILE_WORKERS='1', SIMPLE_FILE_WORKER_BATCH='4', SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY='1',
        SIMPLE_PARSE_SHARDING='1', SIMPLE_FRONTEND_CACHE='1', SIMPLE_HIR_CACHE='1',
        SIMPLE_SCV_INVENTORY_COLD_INIT='1', SIMPLE_NATIVE_BUILD_THREADS='1',
        SIMPLE_PROJECT_ROOT=str(source), SIMPLE_LIB=str(source/'src'),
        SIMPLE_CACHE_PROJECT='ce231-'+PARENT[:16]+'-early-full-cli',
        SIMPLE_USER_STORAGE_ROOT=str(root/'storage'), SIMPLE_CACHE=str(root/'cache'),
        SIMPLE_NATIVE_BUILD_CACHE_DIR=str(root/'cache'),
        SIMPLE_FRONTEND_CACHE_DIR=str(root/'cache/frontend'), SIMPLE_HIR_CACHE_DIR=str(root/'cache/hir'),
        SIMPLE_KEEP_NATIVE_OBJS='1', SIMPLE_COMPILER_PHASE_PROFILE='1',
        SIMPLE_PROCESS_TREE_RSS_DECLARED_JOBS='1', SIMPLE_BOOTSTRAP_RSS_CAP_MODE='enforce',
        SIMPLE_BUILD_MEMORY_RESERVE_BYTES='1073741824',
        XDG_CACHE_HOME=str(root/'xdg-cache'), TMPDIR=str(root/'tmp'), CC='clang')

    def identities():
        if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=source, text=True).strip() != SOURCE:
            raise RuntimeError('source commit mismatch')
        subprocess.run(['git', 'diff', '--exit-code', 'HEAD', '--', 'src', 'config'], cwd=source, check=True)
        if sha(parent) != PARENT:
            raise RuntimeError('parent compiler changed')
        for name, expected in RUNTIME.items():
            if sha(runtime/name) != expected:
                raise RuntimeError('runtime archive mismatch: '+name)

    def owner(name, argv, seconds, cap, expected_exit=0):
        nonlocal current
        current = name
        argv = list(map(str, argv))
        receipt = evidence/(name+'.owner.env')
        command = ['perl', str(source/'scripts/resource/process-tree-rss-watchdog.pl'),
                   '--rss-cap-mode=enforce', f'--max-rss-kib={cap}',
                   f'--timeout-seconds={seconds}', '--receipt='+str(receipt), '--'] + argv
        (evidence/(name+'.argv.json')).write_text(json.dumps(command, indent=2))
        with (evidence/(name+'.stdout')).open('wb') as stdout, (evidence/(name+'.stderr')).open('wb') as stderr:
            process = subprocess.run(command, cwd=source, env=env, stdout=stdout, stderr=stderr)
        (evidence/(name+'.exit')).write_text(str(process.returncode)+'\n')
        fields = {}
        for line in receipt.read_text().splitlines():
            key, value = line.split('=', 1)
            if key in fields:
                raise RuntimeError(name+': duplicate owner receipt field')
            fields[key] = value
        if fields.get('status') != 'complete' or fields.get('quiescent') != '1' or fields.get('rss_cap_enforced') != '1':
            raise RuntimeError(name+': owner did not complete quiescent under enforced cap')
        if fields.get('rss_limit_kib') != str(cap) or fields.get('exit_status') != str(process.returncode):
            raise RuntimeError(name+': owner identity/status mismatch')
        if process.returncode != expected_exit:
            raise RuntimeError(name+': unexpected exit '+str(process.returncode))
        identities()
        if 'product_sha256' in result and sha(product/'simple') != result['product_sha256']:
            raise RuntimeError(name+': qualified product changed')
        return (evidence/(name+'.stdout')).read_text(errors='replace')

    def counts(text, passed, failed):
        text = re.sub(r'\x1b\[[0-9;]*m', '', text)
        matches = re.findall(r'^Results: (\d+) total, (\d+) passed, (\d+) failed(?:, 0 skipped)?(?:, 0 pending)?\s*$', text, re.M)
        if len(matches) != 1 or tuple(map(int, matches[0])) != (passed+failed, passed, failed):
            raise RuntimeError('test CLI lacks exact positive execution counts')

    try:
        PARENT_PROOF = verify_ce231_parent(parent, args.parent_evidence.resolve(), runtime, PARENT, args.parent_artifact_id)
        RUNTIME = PARENT_PROOF['runtime_files']
        result['parent_run'] = PARENT_PROOF['parent_run']
        result['runtime_files'] = RUNTIME
        result['runtime_sha256'] = RUNTIME
        (evidence/'parent-proof.json').write_text(json.dumps(PARENT_PROOF, indent=2))
        identities()
        parent.chmod(0o755)
        tools = {}
        for name in ('clang', 'ld.lld', 'llvm-ar'):
            path = shutil.which(name)
            if not path:
                raise RuntimeError('native tool unavailable: '+name)
            tools[name] = {'path': path, 'sha256': sha(path),
                'version': subprocess.check_output([path, '--version'], text=True, timeout=10)}
        (evidence/'observed-tools.json').write_text(json.dumps(tools, indent=2))
        free_disk = shutil.disk_usage(source).free
        (evidence/'disk-before.json').write_text(json.dumps({'free_bytes': free_disk}))
        if free_disk < 8 * 1024**3:
            raise RuntimeError('insufficient private build/cache disk headroom')
        memory = Path('/proc/meminfo').read_text()
        (evidence/'memory-before.txt').write_text(memory)
        available = int(re.search(r'^MemAvailable:\s+(\d+)', memory, re.M).group(1))
        cap = available * 3 // 4
        if available < cap + 2 * 1024 * 1024:
            raise RuntimeError('host lacks required 2 GiB reserve outside owner cap')
        if cap < 6 * 1024 * 1024:
            raise RuntimeError('host lacks bounded single-unit CLI build headroom')
        env['SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB'] = str(cap)
        env['SIMPLE_PROCESS_TREE_RSS_CAP_KIB'] = str(cap)
        env['SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB'] = str(cap)
        (evidence/'reservation.json').write_text(json.dumps({'available_kib': available,
            'cap_kib': cap, 'fraction': '75%', 'outside_owner_reserve_kib': 2097152, 'threads': 1, 'route': 'explicit-single-unit-per-file',
            'worker_estimate': 'canonical unchanged', 'reserve_bytes': 1073741824}, indent=2))
        (evidence/'environment.json').write_text(json.dumps({k:v for k,v in env.items()
            if k.startswith('SIMPLE_') or k in ('TMPDIR', 'XDG_CACHE_HOME', 'CC')}, indent=2))
        result['source_tree'] = subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], cwd=source, text=True).strip()
        (evidence/'lineage.json').write_text(json.dumps(result, indent=2))
        binary = product/'simple'
        args = [parent, 'native-build', '--backend', 'llvm', '--target', 'x86_64-unknown-linux-gnu',
                '--runtime-path', runtime, '--runtime-bundle', 'core-c-bootstrap', '--threads', '1',
                '--profile=prod', '--release', '--strip', '--managed-build-phase=phase4', '--opt-level=standard',
                '--low-memory', '--entry-closure', '--entry', 'src/app/cli/_CliMain/main_and_help.spl',
                '--mode', 'dynload', '--cache-dir', root/'cache', '--output', binary]
        for path in ('src/compositions/cuda_disabled', 'src/compositions/kernel_llvm_cranelift',
                     'src/compiler', 'src/app', 'src/lib', 'src/os', 'src/plugins',
                     'src/package_ownership', 'src/compositions'):
            args += ['--source', path]
        owner('build', args, 14400, cap)
        if not binary.is_file() or binary.stat().st_size == 0:
            raise RuntimeError('build produced no full CLI')
        result['product_sha256'] = sha(binary)
        (evidence/'linked-product-files.json').write_text(json.dumps(
            {str(p.relative_to(product)):sha(p) for p in product.rglob('*') if p.is_file()}, indent=2))
        (evidence/'linked-product.json').write_text(json.dumps(result, indent=2))
        # Qualification runs the new product only; the parent cannot stand in.
        env['SIMPLE_BINARY'] = str(binary)
        smoke_root = root/'product-smoke'
        for name in ('cache', 'storage', 'tmp', 'xdg-cache'):
            (smoke_root/name).mkdir(parents=True, exist_ok=False)
        env.update(SIMPLE_CACHE=str(smoke_root/'cache'),
            SIMPLE_NATIVE_BUILD_CACHE_DIR=str(smoke_root/'cache'),
            SIMPLE_CACHE_PROJECT='ce231-full-cli-smoke-'+result['product_sha256'],
            SIMPLE_USER_STORAGE_ROOT=str(smoke_root/'storage'),
            XDG_CACHE_HOME=str(smoke_root/'xdg-cache'), TMPDIR=str(smoke_root/'tmp'))
        env['SIMPLE_BOOTSTRAP_WHOLE_PROGRAM'] = '1'
        for key in ('SIMPLE_FILE_WORKERS', 'SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY', 'SIMPLE_PARSE_SHARDING',
                    'SIMPLE_FRONTEND_CACHE_DIR', 'SIMPLE_HIR_CACHE_DIR'):
            env.pop(key, None)
        smoke_cap = min(cap, 4 * 1024 * 1024)
        for key in ('SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB', 'SIMPLE_PROCESS_TREE_RSS_CAP_KIB',
                    'SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB'):
            env[key] = str(smoke_cap)
        if 'simple' not in owner('version', [binary, '--version'], 60, smoke_cap).lower():
            raise RuntimeError('unexpected version output')
        help_text = owner('help', [binary, '--help'], 60, smoke_cap)
        if not help_text.strip():
            raise RuntimeError('help command produced no output')
        fixtures = source/'test/fixtures/phase4_cli_from_ce231_phase3'
        fixtures.mkdir(parents=True, exist_ok=False)
        hello = fixtures/'hello.spl'
        hello.write_text('fn main():\n    print "early-full-cli-ok"\n    print 19 + 23\n')
        positive = fixtures/'positive_spec.spl'
        positive.write_text('describe "early full CLI execution":\n    it "executes arithmetic and text":\n        expect(19 + 23).to_equal(42)\n        expect("full-cli".len()).to_equal(8)\n')
        negative = fixtures/'negative_spec.spl'
        negative.write_text('describe "early full CLI failure control":\n    it "reports a real failing assertion":\n        expect(19 + 23).to_equal(43)\n')
        (evidence/'fixture-hashes.json').write_text(json.dumps({str(p.relative_to(source)):sha(p)
            for p in (hello, positive, negative)}, indent=2))
        stdout = owner('run', [binary, 'run', hello], 300, smoke_cap)
        if stdout != 'early-full-cli-ok\n42\n':
            raise RuntimeError('run command output mismatch')
        counts(owner('test-positive', [binary, 'test', positive, '--mode=interpreter', '--max-workers=1'], 600, smoke_cap), 1, 0)
        counts(owner('test-negative', [binary, 'test', negative, '--mode=interpreter', '--max-workers=1'], 600, smoke_cap, 1), 0, 1)
        native = product/'hello'
        owner('native-hello-build', [binary, 'native-build', '--backend', 'llvm', '--target', 'x86_64-unknown-linux-gnu',
              '--runtime-path', runtime, '--runtime-bundle', 'core-c-bootstrap', '--threads', '1',
              '--entry-closure', '--mode', 'one-binary', '--entry', hello, '--output', native], 600, smoke_cap)
        if owner('native-hello-run', [native], 30, 262144) != 'early-full-cli-ok\n42\n':
            raise RuntimeError('native Hello output mismatch')
        result.update(status='PASS', test_passed=1, negative_control_failed=1,
                      run_executed=1, native_hello_sha256=sha(native))
        print('PASS: recovered-Phase3 full CLI build, version/help, run, counted positive/negative tests and native Hello')
    except Exception as error:
        result.update(status='FAILED', failed_stage=current, error=str(error))
        print('FAIL: '+current+': '+str(error), file=sys.stderr)
    finally:
        (evidence/'terminal.json').write_text(json.dumps(result, indent=2)+'\n')
    return 0 if result['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())

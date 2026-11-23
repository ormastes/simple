#!/usr/bin/env python3
"""One provisional full CLI from an existing Linux Phase2; no compiler rebuild."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import importlib.util

_rss_spec = importlib.util.spec_from_file_location('rss_ring', Path(__file__).with_name('process-rss-ring.py'))
_rss_module = importlib.util.module_from_spec(_rss_spec)
_rss_spec.loader.exec_module(_rss_module)

SOURCE = 'fd366d2a3068e9fc0d2ba7af0b915432d56b88c9'
PARENT = 'f130dde9f91955186ae5e9121917e121d99542871f80e5dc7dd6b8a718c447a3'
RUNTIME = {'libsimple_native_all.a': '7ceed2e9b0edbf719a6fb4422578d2e322e7ea33f71a9cf700fc8f16df2208ae',
           'libsimple_compiler_backfill.a': '637d252e535f0773347af467335918133b2d83c52759eff64c33ac7932d2a41e'}


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path)
    args = parser.parse_args()
    source = args.source.resolve()
    if str(source) != '/home/runner/work/simple/simple/source':
        raise RuntimeError('retained cache absolute source path mismatch')
    root = source/'build/early-full-cli-fd366'
    run_id = os.environ['GITHUB_RUN_ID']
    evidence = root/('evidence-'+run_id)
    evidence.mkdir(parents=True, exist_ok=False)
    product = root/('product-'+run_id)
    product.mkdir()
    for name in ('cache/frontend', 'cache/hir', 'tmp', 'storage', 'xdg-cache'):
        (root/name).mkdir(parents=True, exist_ok=True)
    parent = root/'parent/simple_stage2'
    runtime = root/'runtime'
    current = 'identity'
    result = {'status': 'in_progress', 'admission': 'none', 'scope': 'early-phase4-full-cli-from-phase2',
              'source': SOURCE, 'producer_sha256': PARENT, 'runtime_sha256': RUNTIME,
              'parent_run': 45205044707, 'parent_artifact': 14839362739,
              'runtime_artifact': 14833542613, 'formal_authority': 'unavailable; no managed admission claimed'}
    env = dict(os.environ)
    for key in list(env):
        if key.startswith('SIMPLE_'):
            del env[key]
    env.update(SIMPLE_BINARY=str(parent), SIMPLE_RUNTIME_PATH=str(runtime),
        SIMPLE_NO_STUB_FALLBACK='1', SIMPLE_NATIVE_BUILD_RUST='0',
        SIMPLE_BOOTSTRAP_STAGE3='0', SIMPLE_BOOTSTRAP_STAGE4='0',
        SIMPLE_FILE_WORKERS='1', SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY='1',
        SIMPLE_FILE_WORKER_BATCH='4',
        SIMPLE_PARSE_SHARDING='1', SIMPLE_FRONTEND_CACHE='1', SIMPLE_HIR_CACHE='1',
        SIMPLE_SCV_INVENTORY_COLD_INIT='1', SIMPLE_NATIVE_BUILD_THREADS='1',
        SIMPLE_PROJECT_ROOT=str(source), SIMPLE_LIB=str(source/'src'),
        SIMPLE_CACHE_PROJECT='fd366-'+PARENT[:16]+'-early-full-cli',
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
        if result.get('product_sha256') and sha(product/'simple') != result['product_sha256']:
            raise RuntimeError('full CLI changed during qualification')
        for name, expected in RUNTIME.items():
            if sha(runtime/name) != expected:
                raise RuntimeError('runtime archive mismatch: '+name)

    def owner(name, argv, seconds, cap, expected_success=True):
        nonlocal current
        current = name
        argv = list(map(str, argv))
        receipt = evidence/(name+'.owner.env')
        command = ['perl', str(source/'scripts/resource/process-tree-rss-watchdog.pl'),
                   '--rss-cap-mode=enforce', f'--max-rss-kib={cap}',
                   f'--timeout-seconds={seconds}', '--receipt='+str(receipt), '--'] + argv
        (evidence/(name+'.argv.json')).write_text(json.dumps(command, indent=2))
        with (evidence/(name+'.stdout')).open('wb') as stdout, (evidence/(name+'.stderr')).open('wb') as stderr:
            process = subprocess.Popen(command, cwd=source, env=env, stdout=stdout, stderr=stderr)
            sampler = None
            try:
                if name == 'build':
                    sampler = _rss_module.ProcessRssRing(process.pid, evidence/(name+'.process-rss.json'))
                    sampler.start()
                process.wait()
            except BaseException:
                process.terminate()
                try:
                    process.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
                raise
            finally:
                if sampler is not None:
                    try:
                        sampler.stop()
                    except Exception as error:
                        print(name+': telemetry cleanup: '+str(error), file=sys.stderr)
        (evidence/(name+'.exit')).write_text(str(process.returncode)+'\n')
        fields = {}
        for line in receipt.read_text().splitlines():
            key, value = line.split('=', 1)
            if key in fields:
                raise RuntimeError(name+': duplicate owner receipt field')
            fields[key] = value
        if fields.get('status') != 'complete' or fields.get('quiescent') != '1' or fields.get('rss_cap_enforced') != '1':
            raise RuntimeError(name+': owner status='+str(fields.get('status'))+
                               ' quiescent='+str(fields.get('quiescent'))+
                               ' enforced='+str(fields.get('rss_cap_enforced')))
        if fields.get('rss_limit_kib') != str(cap) or fields.get('exit_status') != str(process.returncode):
            raise RuntimeError(name+': owner identity/status mismatch')
        if (process.returncode == 0) != expected_success:
            raise RuntimeError(name+': unexpected exit '+str(process.returncode))
        identities()
        return (evidence/(name+'.stdout')).read_text(errors='replace')

    def counts(text, passed, failed):
        text = re.sub(r'\x1b\[[0-9;]*m', '', text)
        matches = re.findall(r'^Results: (\d+) total, (\d+) passed, (\d+) failed(?:, 0 skipped)?(?:, 0 pending)?\s*$', text, re.M)
        if len(matches) != 1 or tuple(map(int, matches[0])) != (passed+failed, passed, failed):
            raise RuntimeError('test CLI lacks exact positive execution counts')

    try:
        identities()
        prior = json.loads((root/'evidence/terminal.json').read_text())
        if (prior['source'], prior['producer_sha256'], prior['runtime_sha256'], prior['failed_stage']) != (SOURCE, PARENT, RUNTIME, 'build'):
            raise RuntimeError('retained terminal tuple mismatch')
        prior_owner = dict(line.split('=', 1) for line in (root/'evidence/build.owner.env').read_text().splitlines())
        if (prior_owner.get('status'), prior_owner.get('exit_status'), prior_owner.get('quiescent')) != ('rss-cap-exceeded', '88', '1'):
            raise RuntimeError('retained failure is not the reviewed quiescent RSS incident')
        if list((root/'cache').rglob('*.terminal')) or list((root/'cache').rglob('*.o')):
            raise RuntimeError('unexpected completed module/object in prior frontend-only cache')
        old_queues = sorted(str(p.relative_to(root/'cache')) for p in (root/'cache').rglob('queue-*') if p.is_dir())
        (evidence/'cache-reuse.json').write_text(json.dumps({
            'prior_run': 45238478116, 'artifact': 14851292242,
            'artifact_digest': 'sha256:c4b52ef70ccd83cf33c77ededdf412de642139167082b318e93a812ffe02df77',
            'old_queue_namespaces': old_queues, 'completed_modules_reused': 0,
            'scope': 'frontend candidates only; normal compiler identity validation; old picks are not results',
            'batch': 4, 'prior_requested_batch': 16, 'cycle_peers_may_expand_pick': True}, indent=2))
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
        if cap < 6 * 1024 * 1024:
            raise RuntimeError('host lacks bounded single-unit CLI build headroom')
        env['SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB'] = str(cap)
        env['SIMPLE_PROCESS_TREE_RSS_CAP_KIB'] = str(cap)
        env['SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB'] = str(cap)
        (evidence/'reservation.json').write_text(json.dumps({'available_kib': available,
            'cap_kib': cap, 'fraction': '75%', 'threads': 1, 'route': 'explicit-single-unit-per-file',
            'worker_estimate': 'canonical unchanged', 'reserve_bytes': 1073741824,
            'requested_batch': 4, 'cycle_peers_may_expand_pick': True}, indent=2))
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
        build_log = (evidence/'build.stdout').read_text(errors='replace')
        new_queues = [p for p in (root/'cache').rglob('queue-*') if p.is_dir()
                      and str(p.relative_to(root/'cache')) not in old_queues]
        if '[coordinator-route] per-file worker pool + per-module link' not in build_log or not new_queues:
            raise RuntimeError('successful build lacks actual per-file route and fresh queue evidence')
        if not binary.is_file() or binary.stat().st_size == 0:
            raise RuntimeError('build produced no full CLI')
        result['product_sha256'] = sha(binary)
        (evidence/'linked-product-files.json').write_text(json.dumps(
            {str(p.relative_to(product)):sha(p) for p in product.rglob('*') if p.is_file()}, indent=2))
        (evidence/'linked-product.json').write_text(json.dumps(result, indent=2))
        # Qualification runs the new product only; the parent cannot stand in.
        env['SIMPLE_BINARY'] = str(binary)
        smoke_root = root/('product-smoke-'+run_id)
        for name in ('cache', 'storage', 'tmp', 'xdg-cache'):
            (smoke_root/name).mkdir(parents=True, exist_ok=False)
        env.update(SIMPLE_CACHE=str(smoke_root/'cache'),
            SIMPLE_NATIVE_BUILD_CACHE_DIR=str(smoke_root/'cache'),
            SIMPLE_CACHE_PROJECT='fd366-full-cli-smoke-'+result['product_sha256'],
            SIMPLE_USER_STORAGE_ROOT=str(smoke_root/'storage'),
            XDG_CACHE_HOME=str(smoke_root/'xdg-cache'), TMPDIR=str(smoke_root/'tmp'))
        env['SIMPLE_BOOTSTRAP_WHOLE_PROGRAM'] = '1'
        for key in ('SIMPLE_FILE_WORKERS', 'SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY', 'SIMPLE_PARSE_SHARDING',
                    'SIMPLE_FILE_WORKER_BATCH',
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
        fixtures = source/'test/fixtures/early_full_cli_fd366'
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
        if stdout.strip() != 'early-full-cli-ok\n42':
            raise RuntimeError('run command output mismatch')
        counts(owner('test-positive', [binary, 'test', positive, '--mode=interpreter', '--max-workers=1'], 600, smoke_cap), 1, 0)
        counts(owner('test-negative', [binary, 'test', negative, '--mode=interpreter', '--max-workers=1'], 600, smoke_cap, False), 0, 1)
        native = product/'hello'
        owner('native-hello-build', [binary, 'native-build', '--backend', 'llvm', '--target', 'x86_64-unknown-linux-gnu',
              '--runtime-path', runtime, '--runtime-bundle', 'core-c-bootstrap', '--threads', '1',
              '--entry-closure', '--mode', 'one-binary', '--entry', hello, '--output', native], 600, smoke_cap)
        if owner('native-hello-run', [native], 30, 262144).strip() != 'early-full-cli-ok\n42':
            raise RuntimeError('native Hello output mismatch')
        result.update(status='PASS', test_passed=1, negative_control_failed=1,
                      run_executed=1, native_hello_sha256=sha(native))
        print('PASS: early full CLI build, version/help, run, counted positive/negative tests and native Hello')
    except Exception as error:
        result.update(status='FAILED', failed_stage=current, error=str(error))
        print('FAIL: '+current+': '+str(error), file=sys.stderr)
    finally:
        if 'old_queues' in locals():
            current_queues = sorted(str(p.relative_to(root/'cache')) for p in (root/'cache').rglob('queue-*') if p.is_dir())
            (evidence/'current-queues.json').write_text(json.dumps({'run': run_id,
                'new_namespaces': [name for name in current_queues if name not in old_queues]}, indent=2))
        if (evidence/'build.stdout').exists():
            log = (evidence/'build.stdout').read_text(errors='replace')
            picked = re.findall(r'\[file-worker\] unit picked=(\d+)', log)
            (evidence/'observed-batches.json').write_text(json.dumps({
                'requested_batch': 4, 'actual_picked_counts': list(map(int, picked)),
                'actual_single_unit_route': '[coordinator-route] per-file worker pool + per-module link' in log}, indent=2))
        (evidence/'terminal.json').write_text(json.dumps(result, indent=2)+'\n')
    return 0 if result['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())

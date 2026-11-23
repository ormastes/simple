"""One source-bound Phase2 using the canonical compile owner and explicit P1."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import re
from mir_phase2_restore import restore_cache

SOURCE = 'ce231b5b898d797c98d44a9b59a4859a7d792a7b'
PARENT = 'ed5e03685a3c9233395306f6fcb2c7c5fa9a6ada36fc1158c20e6d3be91fcf73'

def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def main():
    source = Path('source').resolve()
    evidence = source/'build/ladder/evidence'
    evidence.mkdir(parents=True, exist_ok=False)
    parent = source/'build/ladder/in/linux-x86_64-p1/simple'
    assert sha(parent) == PARENT and parent.stat().st_size == 57470728
    assert parent.with_name('PHASE').read_bytes() == b'1\n'
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=source, text=True).strip() == SOURCE
    subprocess.run(['git', 'diff', '--exit-code', 'HEAD', '--', 'src', 'config'], cwd=source, check=True)
    parent.chmod(0o755)
    reuse = restore_cache(source, evidence)
    available = int(next(row.split()[1] for row in Path('/proc/meminfo').read_text().splitlines() if row.startswith('MemAvailable:')))
    cap = available * 3 // 4
    assert cap >= 10*1024*1024, 'insufficient real headroom for the single-worker canonical route'
    env = {key:value for key,value in os.environ.items() if not key.startswith('SIMPLE_')}
    env.update(SIMPLE_BOOTSTRAP_COMPILER=str(parent), SIMPLE_BOOTSTRAP_COMPILER_PHASE='1',
               SIMPLE_PROJECT_ROOT=str(source), SIMPLE_LIB=str(source/'src'),
               SIMPLE_NATIVE_FILE_TIMING='1', SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY='1',
               SIMPLE_FILE_WORKER_BATCH='4', SIMPLE_HOST_MAX_THREADS='1',
               SIMPLE_HOST_MAX_BUILD_JOBS='1', SIMPLE_BOOTSTRAP_MAX_BUILD_JOBS='1',
               SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=str(cap),
               SIMPLE_PROCESS_TREE_RSS_CAP_KIB=str(cap),
               SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=str(cap),
               GITHUB_ENV=str(evidence/'compile-owner.environment'),
               GITHUB_OUTPUT=str(evidence/'compile-owner.outputs'))
    result = {'source':SOURCE, 'parent_sha256':PARENT, 'parent_run':45254614898,
              'parent_artifact':14858799081, 'admission':'none', 'status':'FAILED',
              'available_kib':available, 'cap_kib':cap, 'fraction':'75%',
              'threads':1, 'batch':4, 'prior_cache':reuse, 'phase':2, 'fallback':'none; exact absolute parent',
              'source_runtime_pairing':'candidate Hello establishes only the exercised path'}
    (evidence/'lineage.json').write_text(json.dumps(result, indent=2))
    (evidence/'environment.json').write_text(json.dumps({key:value for key,value in env.items() if key.startswith('SIMPLE_')}, indent=2))

    def owned(name, argv, seconds, rss, child_env):
        command = ['perl', str(source/'scripts/resource/process-tree-rss-watchdog.pl'),
                   '--rss-cap-mode=enforce', f'--max-rss-kib={rss}',
                   f'--timeout-seconds={seconds}', '--receipt='+str(evidence/(name+'.owner.env')), '--'] + argv
        (evidence/(name+'.argv.json')).write_text(json.dumps(command, indent=2))
        with (evidence/(name+'.stdout')).open('wb') as out, (evidence/(name+'.stderr')).open('wb') as err:
            code = subprocess.run(command, cwd=source, env=child_env, stdout=out, stderr=err).returncode
        (evidence/(name+'.exit')).write_text(str(code)+'\n')
        fields = dict(row.split('=',1) for row in (evidence/(name+'.owner.env')).read_text().splitlines() if '=' in row)
        assert code == 0 and fields.get('status') == 'complete' and fields.get('exit_status') == '0' and fields.get('quiescent') == '1' and fields.get('rss_cap_enforced') == '1', name+': owner failed'
        assert fields.get('rss_limit_kib') == str(rss), name+': owner cap mismatch'

    try:
        result['stage'] = 'canonical-phase2'
        build_argv = ['sh', 'scripts/bootstrap/build-next-phase-ci.shs', 'linux-x86_64', '1']
        assert build_argv[-1] == '1'
        owned('phase2', build_argv, 14400, cap, env)
        expected_parent_line = f'Building phase 2 with {parent} (phase 1)'
        assert expected_parent_line in (evidence/'phase2.stdout').read_text(errors='replace').splitlines(), 'canonical owner selected a different compiler'
        result['canonical_parent_line'] = expected_parent_line
        assert sha(parent) == PARENT
        compiler = source/'build/bootstrap/stage2/simple'
        assert compiler.is_file() and compiler.stat().st_size > 0
        result['compiler_sha256'] = sha(compiler)
        result['compiler_bytes'] = compiler.stat().st_size
        (evidence/'linked-candidate.json').write_text(json.dumps(result, indent=2))
        hello = evidence/'hello'
        hello.mkdir()
        (hello/'hello.spl').write_text('fn main():\n    print "phase-ladder-2-ok"\n')
        hello_env = env.copy()
        hello_env.pop('SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY', None)
        hello_env.pop('SIMPLE_FILE_WORKER_BATCH', None)
        hello_env['SIMPLE_BOOTSTRAP_WHOLE_PROGRAM'] = '1'
        hello_env['SIMPLE_CACHE'] = str(hello/'cache')
        hello_env['SIMPLE_NATIVE_BUILD_CACHE_DIR'] = str(hello/'cache')
        result['stage'] = 'candidate-native-hello'
        owned('hello-compile', [str(compiler), 'native-build', str(hello/'hello.spl'), '-o', str(hello/'hello')], 600, min(cap,4*1024*1024), hello_env)
        owned('hello-run', [str(hello/'hello')], 30, 262144, hello_env)
        assert (evidence/'hello-run.stdout').read_bytes() in (b'phase-ladder-2-ok\n', b'phase-ladder-2-ok\r\n')
        assert sha(compiler) == result['compiler_sha256'] and sha(parent) == PARENT
        result.update(status='PASS', hello_sha256=sha(hello/'hello'), qualification='native compiler plus exact native Hello; no formal stage admission')
    except Exception as error:
        result['error'] = str(error)
    finally:
        observed = {'configured_threads':1, 'configured_batch':4,
                    'scope':'observed log records, not inferred successful admission',
                    'scc_note':'picked count may exceed batch for an indivisible SCC',
                    'route_lines':[], 'unit_specs':[], 'picked_counts':[]}
        for stream in ['phase2.stdout', 'phase2.stderr']:
            log = evidence/stream
            if not log.exists(): continue
            for line in log.read_text(errors='replace').splitlines():
                if '[coordinator-route]' in line or 'admission worker estimate=' in line or 'worker_count=' in line:
                    if len(observed['route_lines']) < 96: observed['route_lines'].append(line[:1000])
                match = re.search(r'unit=([^ ]+)', line)
                if match and match[1] not in observed['unit_specs'] and len(observed['unit_specs']) < 512:
                    observed['unit_specs'].append(match[1])
                match = re.search(r'\[file-worker\] unit picked=(\d+)', line)
                if match: observed['picked_counts'].append(int(match[1]))
        (evidence/'observed-topology.json').write_text(json.dumps(observed, indent=2))
        with (evidence/'scv-capture.log').open('wb') as out:
            capture = subprocess.run(['python3', 'scripts/bootstrap/capture-ladder-scv-evidence.py', str(source), str(evidence/'scv-failure')], cwd=source, stdout=out, stderr=subprocess.STDOUT)
        result['scv_capture_exit'] = capture.returncode
        result['parent_unchanged'] = sha(parent) == PARENT
        (evidence/'terminal.json').write_text(json.dumps(result, indent=2))
    raise SystemExit(0 if result['status'] == 'PASS' else 1)

if __name__ == '__main__':
    main()

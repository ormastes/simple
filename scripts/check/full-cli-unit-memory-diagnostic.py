#!/usr/bin/env python3
"""Incident-only reconstructed single unit; never a compiler/product admission."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

SOURCE = 'fd366d2a3068e9fc0d2ba7af0b915432d56b88c9'
PARENT = 'f130dde9f91955186ae5e9121917e121d99542871f80e5dc7dd6b8a718c447a3'
TARGETS = sorted(['src/lib/common/io/types.spl', 'src/lib/common/encoding/unicode_scalar.spl',
                  'src/lib/common/types.spl', 'src/lib/nogc_sync_mut/sffi/system_env_core.spl'])


def sha(p):
    with Path(p).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def main():
    source = Path('source').resolve()
    assert str(source) == '/home/runner/work/simple/simple/source'
    root = source/'build/early-full-cli-fd366'
    evidence = source/'build/unit-memory-diagnostic'
    evidence.mkdir(exist_ok=False)
    old = root/'evidence-45255561665'
    original = root/'cache/hir/queue-3034-0'
    queue = evidence/'hir-queue'
    queue.mkdir()
    # Explicit reconstructed prestate: same sealed full index, fresh picks/cursor.
    shutil.copy2(original/'unit_order.idx', queue/'unit_order.idx')
    (queue/'.pick_cursor').write_text('0')
    mir = evidence/'mir-queue'
    mir.mkdir()
    parent = root/'parent/simple_stage2'
    parent.chmod(0o755)
    assert sha(parent) == PARENT
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=source, text=True).strip() == SOURCE
    subprocess.run(['git', 'diff', '--exit-code', 'HEAD', '--', 'src', 'config'], cwd=source, check=True)
    request = root/'cache/default/frontend/closure-request-3034-275607/request.v1'
    assert sha(request) == 'ff18cf370c0c9e16713471a6cbfae700b93519d28b327b3908abe6bb4c27ee67'
    rows = request.read_text().splitlines()
    snapshot = Path(rows[2])
    assert sha(rows[12]) == rows[13] == 'f6bb3b706885e0fc32a5aa2436e2fb854793fafb902e9c90b817647cf3cb3ef8'
    picked = sorted(str(Path(p.read_text().strip()).relative_to(snapshot)) for p in (original/'owner_picks').rglob('*.pick'))
    assert picked == TARGETS
    runtime_hashes = json.loads((old/'terminal.json').read_text())['runtime_sha256']
    for name, digest in runtime_hashes.items():
        assert sha(root/'runtime'/name) == digest
    # Check every frozen authored file against its retained inventory before replay.
    for line in (snapshot/'SCV_COMPILE_INVENTORY').read_text().splitlines():
        path, digest, size = line.split('|')
        p = snapshot/path
        assert p.stat().st_size == int(size) and sha(p) == digest.removeprefix('sha256_')
    env = {k: v for k, v in os.environ.items() if not k.startswith('SIMPLE_')}
    env.update(json.loads((old/'environment.json').read_text()))
    env.update(SIMPLE_FILE_WORKER_UNIT='1', SIMPLE_NATIVE_FILE_WORKERS='1',
               SIMPLE_HIR_SHARD_QUEUE=str(queue), SIMPLE_HIR_SHARD_OWNER='0/1@0~h0',
               SIMPLE_HIR_SHARD_CLAIM_LIMIT='4', SIMPLE_MIR_SHARD='0/1',
               SIMPLE_MIR_SHARD_QUEUE=str(mir), SIMPLE_MIR_SHARD_OWNER='0/1@0+fork-m0',
               SIMPLE_UNIT_TLDR_ROOT=str(root/'cache/default/frontend'),
               SIMPLE_FRONTEND_CACHE_DIR=str(root/'cache/default/frontend'),
               SIMPLE_PARSE_CLOSURE_REQUEST=str(request), SIMPLE_PARSE_CLOSURE_REQUEST_DIGEST=sha(request),
               SIMPLE_PARSE_CLOSURE_CONSUMER='1', SIMPLE_PARSE_CLOSURE_SELECTED_COUNT='4175',
               SIMPLE_SCV_SNAPSHOT_ROOT=str(snapshot), SIMPLE_SCV_REVISION_ID=rows[3],
               SIMPLE_SCV_COMMIT_ID=rows[4], SIMPLE_SCV_TREE_ID=rows[5],
               SIMPLE_SCV_INVENTORY_DIGEST=rows[6], SIMPLE_SCV_SOURCE_INVENTORY_DIGEST=rows[7],
               SIMPLE_SCV_INVENTORY_GENERATION=rows[8], SIMPLE_SCV_SOURCE_DRIFTED='0',
               SIMPLE_GLOBAL_DATASET_MAX_BYTES=str(3145728*1024))
    available = int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
    cap = min(11268234, available*3//4)
    assert cap >= 10*1024*1024, 'insufficient hosted memory for finite attribution'
    for key in ['SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB', 'SIMPLE_PROCESS_TREE_RSS_CAP_KIB', 'SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB']:
        env[key] = str(cap)
    argv = json.loads((old/'build.argv.json').read_text())
    argv = argv[argv.index('--')+1:] + ['--hir-shard=0/1']
    argv[argv.index('--output')+1] = str(evidence/'never-admitted-output')
    config = {'queue': str(queue), 'snapshot': str(snapshot), 'targets': TARGETS,
              'events': str(evidence/'boundaries.jsonl')}
    (evidence/'gdb-config.json').write_text(json.dumps(config))
    env['UNIT_DIAGNOSTIC_CONFIG'] = str(evidence/'gdb-config.json')
    (evidence/'environment.json').write_text(json.dumps({k:v for k,v in env.items()
        if k.startswith('SIMPLE_') or k in ['TMPDIR', 'XDG_CACHE_HOME', 'CC', 'UNIT_DIAGNOSTIC_CONFIG']}, indent=2))
    (evidence/'reconstruction.json').write_text(json.dumps({
        'admission': 'none', 'source': SOURCE, 'producer_sha256': PARENT,
        'runtime_sha256': runtime_hashes, 'recorded_targets': TARGETS,
        'changed_prestate': 'fresh disposable queue; same sealed unit index; cursor reset to zero; no prior picks/leases',
        'scope': 'one reconstructed HIR/MIR unit only, no pool or full CLI',
        'read_only_instrumentation': 'GDB symbol entry/return with /proc RSS; stop inferior after promotion',
        'normalized_environment': 'source-derived authority and unit role; frontend default binding; static 3GiB dataset estimate',
        'cap_kib': cap, 'available_kib': available, 'timeout_seconds': 900}, indent=2))
    debugger = Path(__file__).with_name('full-cli-unit-memory-gdb.py').resolve()
    command = ['perl', str(source/'scripts/resource/process-tree-rss-watchdog.pl'),
               '--rss-cap-mode=enforce', f'--max-rss-kib={cap}', '--timeout-seconds=900',
               '--receipt='+str(evidence/'owner.env'), '--', 'gdb', '-q', '-batch',
               '-ex', 'set pagination off', '-ex', 'set confirm off', '-ex', 'set disable-randomization off',
               '-ex', 'source '+str(debugger), '--args'] + argv
    (evidence/'command.json').write_text(json.dumps(command, indent=2))
    with (evidence/'stdout').open('wb') as out, (evidence/'stderr').open('wb') as err:
        code = subprocess.run(command, cwd=source, env=env, stdout=out, stderr=err).returncode
    events = [json.loads(x) for x in (evidence/'boundaries.jsonl').read_text().splitlines()] if (evidence/'boundaries.jsonl').exists() else []
    owner = dict(x.split('=', 1) for x in (evidence/'owner.env').read_text().splitlines() if '=' in x)
    targets_equal = any(x.get('target_equality') is True for x in events)
    full_graph = 'phase2:surface:admitted-graph:done scanned=7114 inventory=7114' in (evidence/'stdout').read_text(errors='replace')
    valid = targets_equal and full_graph
    stages = [x['stage'] for x in events if x.get('comparable')]
    expected = ['finish:entry', 'freeze:entry', 'freeze:return', 'finish:return', 'promote:entry', 'promote:return']
    ordered = stages == expected
    complete = code == 0 and owner.get('status') == 'complete' and owner.get('exit_status') == '0' and owner.get('quiescent') == '1' and owner.get('rss_cap_enforced') == '1'
    result = {'admission': 'none', 'owner': owner, 'exit': code, 'target_equality': targets_equal,
              'full_graph_observed': full_graph,
              'ordered_validated_boundaries': ordered, 'complete_owned_diagnostic': complete,
              'interpretation': 'reconstructed workload only' if valid else 'BLOCKED: target equality not established'}
    assert sha(parent) == PARENT
    (evidence/'result.json').write_text(json.dumps(result, indent=2))
    raise SystemExit(0 if valid and ordered and complete else 1)


if __name__ == '__main__':
    main()

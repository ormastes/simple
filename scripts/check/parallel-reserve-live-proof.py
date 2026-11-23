import hashlib, json, os, pathlib, re, subprocess, sys
root = pathlib.Path.cwd()
seed = pathlib.Path(sys.argv[1]).resolve()
out = root / 'reserve-evidence'
out.mkdir(exist_ok=False)
spec = 'test/01_unit/app/cli/build_parallel_perf_mem_regression_spec.spl'
base = '70abce766732839f0bf8cd073a6cca25dd6190fd'
sources = {'baseline': subprocess.check_output(['git', 'show', base + ':' + spec]).decode('utf-8'),
           'repaired': (root / spec).read_text(encoding='utf-8')}
assert hashlib.sha256(seed.read_bytes()).hexdigest() == 'bd20b7e1378e1d1f45eb5c5d8139d1044145832644db9a2083ae5b15427de4d3'
results = {}
manifest = {'seed': hashlib.sha256(seed.read_bytes()).hexdigest(), 'baseline': base,
            'source': subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip()}
for label, source in sources.items():
    header = '''use std.spec.{step}
use app.io.env_ops.{env_get}
use app.cli.shard_mem_clamp.{shard_standalone_host_cap_v1, shard_commit_spawn_admit_v1,
    shard_tree_headroom_kib_v1, shard_tree_headroom_kib_for_v1, build_host_memory_total_kib}
use app.cli.file_worker_pool_refusal.{FILE_WORKER_UNIT_TLDR_FLOOR_KB_V1}
use std.nogc_sync_mut.host_limits.{host_limit_mem_reserve_free_kib}
val GIB: i64 = 1048576
'''
    start = re.search(r'^    it "admits >= 2 workers[^\n]*\n', source, re.M).start()
    next_case = re.search(r'^    it ', source[start+1:], re.M)
    end = start + 1 + next_case.start() if next_case else len(source)
    block = source[start:end]
    extracted = header + 'describe "configured host reserve":\n' + block
    assert len(re.findall(r'^    it ', extracted, re.M)) == 1
    fixture = out / label
    (fixture / 'config/host').mkdir(parents=True)
    test = fixture / 'reserve_live_spec.spl'
    test.write_text(extracted, encoding='utf-8')
    defaults = fixture / 'config/host/host_config.sdn'
    host = fixture / 'config/host/reserve-fixture.sdn'
    user = fixture / 'user.sdn'
    defaults.write_text('host_config:\n  mem_reserve_free_mib: 32768\n', encoding='utf-8')
    host.write_text('host_env:\n  hostname: reserve-fixture\n  mem_reserve_free_mib: 40960\n', encoding='utf-8')
    user.write_text('host_config:\n  schema: simple-host-config-v1\n  mem_reserve_free_mib: 49152\n', encoding='utf-8')
    subprocess.run(['git','init','-q',str(fixture)],check=True)
    subprocess.run(['git','-C',str(fixture),'add','.'],check=True)
    subprocess.run(['git','-C',str(fixture),'-c','user.name=ReserveFixture','-c','user.email=fixture@invalid',
                    '-c','commit.gpgsign=false','commit','-qm','configured host fixture'],check=True)
    inputs = {str(p.relative_to(fixture)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [test,defaults,host,user]}
    manifest[label] = {'tracked_spec_sha256': hashlib.sha256(source.encode()).hexdigest(),
                       'exact_example_sha256':hashlib.sha256(block.encode()).hexdigest(), 'inputs':inputs}
    env = dict(os.environ, SIMPLE_LIB=str(root/'src'), SIMPLE_PROJECT_ROOT=str(fixture),
               SIMPLE_TEST_RUNNER_RUST='1', SIMPLE_HOST_CONFIG=str(user),
               COMPUTERNAME='reserve-fixture', HOSTNAME='reserve-fixture')
    env.pop('SIMPLE_HOST_MEM_RESERVE_FREE_MIB',None)
    env.pop('SIMPLE_BUILD_MEMORY_RESERVE_BYTES',None)
    (out/'inputs.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
    result = subprocess.run(['timeout','--kill-after=5','180',str(seed),'test',str(test),'--mode=interpreter'],cwd=fixture,
                            env=env,capture_output=True,timeout=195)
    (out/(label+'.stdout')).write_bytes(result.stdout)
    (out/(label+'.stderr')).write_bytes(result.stderr)
    clean = re.sub(r'\x1b\[[0-9;]*m','',result.stdout.decode(errors='replace'))
    counts = {'exit': result.returncode}
    for key in ['Passed','Failed']:
        match = re.search(rf'{key}:\s*(\d+)',clean)
        counts[key.lower()] = int(match[1]) if match else None
    results[label] = counts
    child_errors = list(fixture.glob('build/test-artifacts/**/stderr.log'))
    child_error_text = '\n'.join(p.read_text(encoding='utf-8',errors='replace') for p in child_errors)
    assert 'memory allocation of ' not in child_error_text, 'dependency loading exhausted bound: ' + label
    assert all(hashlib.sha256((fixture/p).read_bytes()).hexdigest()==digest for p,digest in inputs.items())
    (out/'results.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
    (out/'inputs.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
assert results['baseline']=={'exit':1,'passed':0,'failed':1}, results
assert results['repaired']=={'exit':0,'passed':1,'failed':0}, results
print(json.dumps(results))

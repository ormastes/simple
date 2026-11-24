"""Prepare argv files only after parent verification. Never execute a build."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

SOURCE = 'ce231b5b898d797c98d44a9b59a4859a7d792a7b'
CONTROL = '79f7e678d48d35e1319e12fdae52cea01d2e0352'
P1 = 'ed5e03685a3c9233395306f6fcb2c7c5fa9a6ada36fc1158c20e6d3be91fcf73'
ENTRIES = {'full-cli':'src/app/cli/_CliMain/main_and_help.spl',
           'mcp':'src/app/mcp/main.spl', 'interpreter':'src/app/cli/interpreter_main.spl',
           'lsp':'src/app/simple_lsp_mcp/main.spl', 'test-runner':'src/app/test_runner_new/main.spl'}
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('contract', type=Path)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
c = json.loads(a.contract.read_text(encoding='utf-8'))
assert c['execution_isolation'] == 'separate-hosted-linux-jobs'
assert c['source_revision'] == SOURCE and c['phase2_control_revision'] == CONTROL
assert c['phase2_run'] == 45275222826 and isinstance(c['phase2_artifact_id'], int)
assert c['phase2_artifact_name'] == 'pinned-candidate-phase2-single-worker-45275222826'

def sha(path):
    with path.open('rb') as f: return hashlib.file_digest(f, 'sha256').hexdigest()

def verified(path, digest):
    path = Path(path)
    assert not path.is_symlink()
    path = path.resolve(strict=True)
    assert path.is_file()
    assert re.fullmatch('[0-9a-f]{64}', digest) and sha(path) == digest
    return path

verified(c['phase2_artifact_zip'], c['phase2_artifact_zip_sha256'])
producer = verified(c['phase2_producer'], c['phase2_producer_sha256'])
terminal_path = verified(c['phase2_terminal'], c['phase2_terminal_sha256'])
t = json.loads(terminal_path.read_text())
assert t['status'] == 'PASS' and t['source'] == SOURCE and t['phase'] == 2
assert t['parent_sha256'] == P1 and t['parent_unchanged'] is True
assert t['compiler_sha256'] == c['phase2_producer_sha256'] and t['compiler_bytes'] == producer.stat().st_size
evidence = Path(c['phase2_evidence_directory']).resolve(strict=True)
bound = {str(terminal_path): sha(terminal_path), str(producer): sha(producer)}
for name in ['phase2', 'hello-compile', 'hello-run']:
    receipt = evidence/(name+'.owner.env')
    fields = dict(line.split('=',1) for line in receipt.read_text().splitlines() if '=' in line)
    assert fields.get('status') == 'complete' and fields.get('exit_status') == '0'
    assert fields.get('quiescent') == '1' and fields.get('rss_cap_enforced') == '1'
    assert (evidence/(name+'.exit')).read_text().strip() == '0'
    bound[str(receipt)] = sha(receipt)
assert (evidence/'hello-run.stdout').read_bytes() in [b'phase-ladder-2-ok\n', b'phase-ladder-2-ok\r\n']
assert sha(evidence/'hello/hello') == t['hello_sha256']
assert (evidence/'hello/hello.spl').read_text() == 'fn main():\n    print "phase-ladder-2-ok"\n'
for name in ['hello-run.stdout', 'hello/hello', 'hello/hello.spl', 'hello-compile.argv.json', 'hello-run.argv.json']:
    bound[str(evidence/name)] = sha(evidence/name)
assert c['phase2_original_producer_path'] == '/home/runner/work/simple/simple/source/build/bootstrap/stage2/simple'
assert c['phase2_original_producer_path'] in json.loads((evidence/'hello-compile.argv.json').read_text()), 'Hello argv did not invoke the recorded producer'
source = Path(c['source_root']).resolve(strict=True)
assert subprocess.check_output(['git','-C',str(source),'rev-parse','HEAD'],text=True).strip() == SOURCE
subprocess.run(['git','-C',str(source),'diff','--exit-code','HEAD','--','src','config'],check=True)
# Existing authorization; require actual published native pairing evidence below.
selection = verified(c['runtime_selection_evidence'], c['runtime_selection_evidence_sha256'])
bound[str(selection)] = sha(selection)
pair=json.loads(selection.read_text())
assert pair['status']=='NATIVE_PAIRING_PASS' and pair['source']==SOURCE
assert pair['producer_sha256']==c['phase2_producer_sha256']
assert pair['runtime_artifact_id']==14871469985
assert pair['runtime_artifact_sha256']=='5f24b108c986147526e7edf732346af4bb25f90d5d3bc260449841aed2c01fe9'
assert pair['runtime_files']==c['runtime_files']
assert pair['stdout']=='bootstrap-compiler-probe\n'
for name,digest in pair['files'].items():
    checked=verified(selection.parent/name,digest)
    assert checked.is_relative_to(selection.parent)
assert (selection.parent/'run.log').read_bytes() in [b'bootstrap-compiler-probe\n',b'bootstrap-compiler-probe\r\n']
assert (selection.parent/'run-exit-status').read_text().strip()=='0'
assert sha(selection.parent/'hello')==pair['hello_sha256']
fd=json.loads(Path(c['fd366_run_metadata']).read_text())
assert fd['id']==45241703685 and fd['status']=='completed' and fd['conclusion']!='success'

runtime = Path(c['runtime_root']).resolve(strict=True)
assert c['runtime_bundle'] == 'core-c-bootstrap'
assert set(c['runtime_files']).intersection(['libsimple_native_all.a','libsimple_runtime.a']), 'actual runtime input not yet retained/bound'
for relative, digest in c['runtime_files'].items():
    path = verified(runtime/relative, digest)
    assert path.is_relative_to(runtime)
    bound[str(path)] = digest
product = c['early_product']
assert product in ENTRIES
output = Path(c['output_root'])/('ce231-'+c['phase2_producer_sha256'][:16])
assert output.is_absolute() and not output.exists(), 'use fresh, isolated child outputs'
plans = []
common_sources = ['src/compositions/kernel_llvm_cranelift','src/compositions/cuda_disabled','src/compiler','src/app','src/lib']
for role in ['early-phase4']:
    child_root = output/role
    cap = c['phase3_memory_kib' if role == 'phase3' else 'phase4_memory_kib']
    seconds = c['phase3_timeout_seconds' if role == 'phase3' else 'phase4_timeout_seconds']
    assert isinstance(cap,int) and cap > 0 and isinstance(seconds,int) and 0 < seconds <= 86400
    entry = 'src/app/cli/bootstrap_main.spl' if role == 'phase3' else ENTRIES[product]
    sources = common_sources+(['src/plugins'] if role == 'phase3' else ['src/os','src/plugins','src/package_ownership','src/compositions'])
    args = [str(producer),'native-build','--backend','llvm','--target','x86_64-unknown-linux-gnu',
            '--runtime-path',str(runtime),'--runtime-bundle','core-c-bootstrap','--threads','1']
    for path in sources: args += ['--source',path]
    if role == 'early-phase4': args += ['--profile=prod','--release','--strip','--managed-build-phase=phase4','--opt-level=standard']
    args += ['--entry-closure','--entry',entry,'--mode','dynload','--low-memory',
             '--cache-dir',str(child_root/'cache'),'--output',str(child_root/'product/simple')]
    env = {'SIMPLE_BINARY':str(producer),'SIMPLE_NATIVE_BUILD_RUST':'0','SIMPLE_NO_STUB_FALLBACK':'1',
           'SIMPLE_RUNTIME_PATH':str(runtime),'SIMPLE_PROJECT_ROOT':str(source),'SIMPLE_LIB':str(source/'src'),
           'SIMPLE_FILE_WORKERS':'1','SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY':'1','SIMPLE_FILE_WORKER_BATCH':'4',
           'SIMPLE_PARSE_SHARDING':'1','SIMPLE_SCV_INVENTORY_COLD_INIT':'1',
           'SIMPLE_BUILD_MEMORY_RESERVE_BYTES':str(c['phase4_resource_policy']['reserve_kib']*1024),
           'SIMPLE_PROCESS_TREE_RSS_CAP_KIB':str(cap),'SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB':str(cap),
           'SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB':str(cap),'SIMPLE_BOOTSTRAP_RSS_CAP_MODE':'enforce',
           'SIMPLE_FRONTEND_CACHE_DIR':str(child_root/'cache/frontend'),'SIMPLE_HIR_CACHE_DIR':str(child_root/'cache/hir'),
           'SIMPLE_CACHE_PROJECT':'ce231-'+c['phase2_producer_sha256'][:16]+'-'+role,
           'SIMPLE_CACHE':str(child_root/'cache'),'SIMPLE_USER_STORAGE_ROOT':str(child_root/'storage'),
           'TMPDIR':str(child_root/'tmp'),'XDG_CACHE_HOME':str(child_root/'xdg-cache'),'CC':'clang'}
    if role == 'phase3': env.update(SIMPLE_BOOTSTRAP='1', SIMPLE_BOOTSTRAP_STAGE3='1')
    else: env.update(SIMPLE_BOOTSTRAP_STAGE3='0', SIMPLE_BOOTSTRAP_STAGE4='0')
    wrapper = ['perl',str(source/'scripts/resource/process-tree-rss-watchdog.pl'),'--rss-cap-mode=enforce',
               '--max-rss-kib='+str(cap),'--timeout-seconds='+str(seconds),'--receipt='+str(child_root/'owner.env'),'--']
    plans.append({'role':role,'source':SOURCE,'cwd':str(source),'clear_inherited_simple_environment':True,
                  'environment':env,'argv':wrapper+args,'mkdir_before_start':[str(child_root/x) for x in ['product','tmp','storage','cache/frontend','cache/hir','xdg-cache']],
                  'parent':str(producer),'parent_sha256':c['phase2_producer_sha256'],'verified_inputs':bound,
                  'qualification':'provisional build-only; no formal admission and no automatic dispatch',
                  'post_build':'Fresh child Hello/product behavior required. Never substitute parent Hello for child proof.'})
a.output.mkdir(parents=True, exist_ok=False)
for plan in plans: (a.output/(plan['role']+'.json')).write_text(json.dumps(plan,indent=2),encoding='utf-8')

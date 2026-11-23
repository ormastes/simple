"""Parent-gated canonical Phase3 with one resolver pairing proof; Linux only."""
import os, time, shutil
from pathlib import Path
import importlib.util
_cleanup_spec=importlib.util.spec_from_file_location("owner_cleanup",Path(__file__).with_name("owner-cleanup.py"))
_cleanup=importlib.util.module_from_spec(_cleanup_spec);_cleanup_spec.loader.exec_module(_cleanup)
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
assert os.name == 'posix'
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
# Runtime artifact identity is fixed independently of the eventual Phase2 archive.
verified(c['runtime_artifact_zip'], '5f24b108c986147526e7edf732346af4bb25f90d5d3bc260449841aed2c01fe9')
runtime = Path(c['runtime_root']).resolve(strict=True)
expected_runtime = {
 'libsimple_native_all.a':'297751e19d6e95b26a214dd325b6e59ec5d956713c57541928a97c717bae7990',
 'libsimple_runtime.a':'0c72026833a4ed17b4233c7905ef5cb2075f9fa450e1befde6d235349b11dc05',
 'libsimple_compiler_backfill.a':'8ae349d93ce20dd3156a15f595a2d99abee3575601630c4efe900a319d44788c',
 'deps/libspl_hosted_runtime.rlib':'faea9c3c0ecb24695bf175d6e5dc57f423c2fa397c75a5da4de6ee0e564251c2'}
for name, digest in expected_runtime.items():
    bound[str(verified(runtime/name, digest))] = digest
# This is an observed-lineage gate, not a new discretionary approval.
fd = json.loads(Path(c['fd366_run_metadata']).read_text())
assert fd['id'] == 45241703685 and fd['status'] == 'completed', 'fd366 still active; avoid duplicate generation'
assert fd['conclusion'] != 'success', 'fd366 succeeded; do not start replacement automatically'
p2 = json.loads(Path(c['phase2_run_metadata']).read_text())
assert p2['id'] == 45275222826 and p2['head_sha'] == CONTROL
assert p2['status'] == 'completed' and p2['conclusion'] == 'success'
assert not (source/'build/bootstrap/stage3').exists(), 'fresh Stage3 output required'
assert not (source/'build/ladder/cache/phase3').exists(), 'no unbound cache reuse'
out = a.output.resolve()
out.mkdir(parents=True, exist_ok=False)
for part in ['tmp','storage','cache','pairing']:
    (out/part).mkdir()
cap = c['phase3_memory_kib']
assert isinstance(cap,int) and 4*1024*1024 <= cap <= 24*1024*1024
available = int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
assert cap <= available*3//4 and available >= cap + 2*1024*1024, 'hosted cap plus 2GiB reserve unavailable'
assert shutil.disk_usage(source).free >= 20*1024**3
seconds = c.get('phase3_timeout_seconds',14400)
assert 0 < seconds <= 14400
env = {k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')}
env.update(SIMPLE_BOOTSTRAP_COMPILER=str(producer), SIMPLE_BOOTSTRAP_COMPILER_PHASE='2',
 SIMPLE_RUNTIME_PATH=str(runtime), SIMPLE_NATIVE_RUNTIME_BUNDLE='core-c-bootstrap',
 SIMPLE_NATIVE_BUILD_RUST='0', SIMPLE_NO_STUB_FALLBACK='1', SIMPLE_BINARY=str(producer),
 SIMPLE_PROJECT_ROOT=str(source), SIMPLE_LIB=str(source/'src'),
 SIMPLE_FILE_WORKERS='1', SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY='1', SIMPLE_FILE_WORKER_BATCH='4',
 SIMPLE_SCV_INVENTORY_COLD_INIT='1', SIMPLE_PARSE_SHARDING='1',
 SIMPLE_CACHE=str(out/'cache'), SIMPLE_USER_STORAGE_ROOT=str(out/'storage'), TMPDIR=str(out/'tmp'),
 SIMPLE_CACHE_PROJECT='ce231-'+sha(producer)[:16]+'-canonical-phase3',
 SIMPLE_PROCESS_TREE_RSS_CAP_KIB=str(cap), SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=str(cap),
 SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=str(cap), SIMPLE_BOOTSTRAP_RSS_CAP_MODE='enforce', CC='clang',
 GITHUB_ENV=str(out/'wrapper.environment'),GITHUB_OUTPUT=str(out/'wrapper.outputs'))
# WHOLE_PROGRAM remains unset: otherwise it would change the canonical Phase3 route.
command = ['perl',str(source/'scripts/resource/process-tree-rss-watchdog.pl'),'--rss-cap-mode=enforce',
 '--max-rss-kib='+str(cap),'--timeout-seconds='+str(seconds),'--receipt='+str(out/'owner.env'),'--',
 'sh','scripts/bootstrap/build-next-phase-ci.shs','linux-x86_64','1']
record = {'status':'RUNNING','source':SOURCE,'producer_sha256':sha(producer),'runtime_files':expected_runtime,
 'argv':command,'environment':{k:v for k,v in env.items() if k.startswith('SIMPLE_') or k in ['TMPDIR','CC']},
 'available_kib':available,'rss_cap_kib':cap,'verified_inputs':bound,
 'qualification':'provisional; no canonical admission receipt synthesized'}
(out/'launch.json').write_text(json.dumps(record,indent=2))
stdout=out/'wrapper.stdout'
try:
 with stdout.open('wb') as log, (out/'wrapper.stderr').open('wb') as err:
     with _cleanup.acquired_owner(command,out/'controller-cleanup.json',cwd=source,env=env,stdout=log,stderr=err) as child:
         (out/'owner.pid').write_text(str(child.pid)+'\n')
         expected_line=f'Building phase 3 with {producer} (phase 2)'
         paired=False
         pairing_error=None
         log_offset=0
         log_tail=""
         selected=False
         while True:
             with stdout.open('r',errors='replace') as current:
                 current.seek(log_offset)
                 chunk=current.read()
                 log_offset=current.tell()
             lines=(log_tail+chunk).split('\n')
             log_tail=lines.pop()
             selected=selected or expected_line in [x.rstrip('\r') for x in lines]
             if not paired and pairing_error is None and selected:
                 try:
                     probes=list((out/'tmp/simple-bootstrap-compiler').glob('probe.*'))
                     assert len(probes)==1, 'ambiguous resolver evidence'
                     probe=probes[0]
                     assert (probe/'run-exit-status').read_text().strip()=='0'
                     assert (probe/'run.log').read_bytes() in [b'bootstrap-compiler-probe\n',b'bootstrap-compiler-probe\r\n']
                     hello_source=Path((probe/'source-path').read_text().strip()).resolve(strict=True)
                     assert hello_source.is_relative_to(source/'build/bootstrap/compiler-probes')
                     assert hello_source.read_text()=='fn main():\n    print "bootstrap-compiler-probe"\n'
                     assert sha(producer)==record['producer_sha256']
                     for name,digest in expected_runtime.items(): assert sha(runtime/name)==digest
                     for name in ['hello','build.log','run.log','run.stderr','run-exit-status','source-path']:
                         shutil.copy2(probe/name,out/'pairing'/name)
                     shutil.copy2(hello_source,out/'pairing/hello.spl')
                     proof={'status':'NATIVE_PAIRING_PASS','source':SOURCE,'producer_sha256':sha(producer),
                       'runtime_files':expected_runtime,'runtime_artifact_id':14871469985,
                       'runtime_artifact_sha256':'5f24b108c986147526e7edf732346af4bb25f90d5d3bc260449841aed2c01fe9',
                       'resolver_sha256':sha(source/'scripts/bootstrap/resolve-bootstrap-compiler.shs'),
                       'wrapper_sha256':sha(source/'scripts/bootstrap/build-next-phase-ci.shs'),
                       'hello_sha256':sha(probe/'hello'),'stdout':'bootstrap-compiler-probe\n',
                       'selection_line':expected_line,'scope':'exact native Hello; canonical resolver returned synchronously; enclosing Phase3 owner remains live',
                       'qualification':'provisional runtime ABI evidence, no formal admission',
                       'files':{x.name:sha(x) for x in (out/'pairing').iterdir() if x.is_file()}}
                     pending=out/'pairing/pairing.json.tmp'
                     pending.write_text(json.dumps(proof,indent=2))
                     pending.replace(out/'pairing/pairing.json')
                     paired=True
                 except Exception as error:
                     pairing_error=str(error)
                     (out/"pairing-error.json").write_text(json.dumps({"error":pairing_error}))
                     raise
             if child.poll() is not None: break
             time.sleep(2)
         code=child.wait()
 receipt=dict(x.split('=',1) for x in (out/'owner.env').read_text().splitlines() if '=' in x)
 record.update(status='BUILT_UNQUALIFIED' if code==0 and receipt.get('status')=='complete' and receipt.get('exit_status')=='0' and receipt.get('quiescent')=='1' and receipt.get('rss_cap_enforced')=='1' and int(receipt.get('rss_limit_kib','0'))==cap and paired else 'FAILED',
  exit_status=code,owner=receipt,pairing_published=paired,pairing_error=pairing_error)
 product=source/'build/bootstrap/stage3/simple'
 if product.is_file() and os.access(product,os.X_OK):
  record['product_sha256']=sha(product)
  record['product_bytes']=product.stat().st_size
 else: record.update(status='FAILED',error='missing executable Phase3 product')
 record['inputs_unchanged']=all(sha(Path(path))==digest for path,digest in bound.items())
 if not record['inputs_unchanged']: record['status']='FAILED'
 (out/'terminal.json').write_text(json.dumps(record,indent=2))
except BaseException as error:
 record.update(status='FAILED',controller_error=str(error))
 if (out/'owner.env').exists():record['owner_raw']=(out/'owner.env').read_text()
 (out/'terminal.json').write_text(json.dumps(record,indent=2))
 raise
raise SystemExit(0 if record['status']=='BUILT_UNQUALIFIED' else 1)

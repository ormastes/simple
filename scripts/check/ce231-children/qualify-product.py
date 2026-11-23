"""Bounded product behavior, adapted from the pinned existing native smoke criteria."""
import argparse,hashlib,importlib.util,json,os,re,subprocess
from pathlib import Path
s=importlib.util.spec_from_file_location('cleanup',Path(__file__).with_name('owner-cleanup.py'))
cleanup=importlib.util.module_from_spec(s);s.loader.exec_module(cleanup)
p=argparse.ArgumentParser();p.add_argument('--role',choices=['phase3','full-cli','mcp'],required=True)
p.add_argument('--binary',type=Path,required=True);p.add_argument('--source',type=Path,required=True)
p.add_argument('--runtime',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
p.add_argument('--source-revision',default='ce231b5b898d797c98d44a9b59a4859a7d792a7b')
a=p.parse_args();source=a.source.resolve();binary=a.binary.resolve(strict=True);runtime=a.runtime.resolve(strict=True)
out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
def sha(path):
 with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
assert binary.is_file() and os.access(binary,os.X_OK)
identity=sha(binary)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()==a.source_revision
runtime_hashes={str(x.relative_to(runtime)):sha(x) for x in runtime.rglob('*') if x.is_file()}
for n in ['tmp','cache','storage']:(out/n).mkdir()
env={k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')}
env.update(SIMPLE_BINARY=str(binary),SIMPLE_RUNTIME_PATH=str(runtime),SIMPLE_NATIVE_RUNTIME_BUNDLE='core-c-bootstrap',
 SIMPLE_NATIVE_BUILD_RUST='0',SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_PROJECT_ROOT=str(source),SIMPLE_LIB=str(source/'src'),
 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM='1',SIMPLE_SCV_INVENTORY_COLD_INIT='1',SIMPLE_CACHE=str(out/'cache'),
 SIMPLE_NATIVE_BUILD_CACHE_DIR=str(out/'cache'),SIMPLE_USER_STORAGE_ROOT=str(out/'storage'),TMPDIR=str(out/'tmp'),CC='clang')
result={'status':'FAILED','source':a.source_revision,'role':a.role,'product_sha256':identity,'runtime_files':runtime_hashes,'claims':{},
 'scope':'new product behavior only; not formal stage admission',
 'criteria_source':{'full-cli':'phase4-from-recovered-phase3.py SHA256449e71ee27484dd8d3cf5d3aa61ba6a38e7aae92bf3b2b2b5e77123dedd61c2f qualification',
 'mcp':'239f3b2c364352ba5b23e4ef2b4e18559be40c13:.github/workflows/mcp-lazy-newline-native-proof.yml'}}
current='identity'
def owned(name,argv,seconds,cap=4194304,expected=0,stdin=None):
 global current
 current=name
 available=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
 assert cap<=available*3//4 and available>=cap+2097152
 childenv=env.copy()
 for k in ['SIMPLE_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB']:childenv[k]=str(cap)
 command=['perl',str(source/'scripts/resource/process-tree-rss-watchdog.pl'),'--rss-cap-mode=enforce',
  f'--max-rss-kib={cap}',f'--timeout-seconds={seconds}','--receipt='+str(out/(name+'.owner.env')),'--']+list(map(str,argv))
 (out/(name+'.argv.json')).write_text(json.dumps(command))
 with (out/(name+'.stdout')).open('wb') as stdout,(out/(name+'.stderr')).open('wb') as stderr:
  with cleanup.acquired_owner(command,out/(name+'.cleanup.json'),cwd=source,env=childenv,stdin=stdin,stdout=stdout,stderr=stderr) as process:code=process.wait()
 receipt=dict(x.split('=',1) for x in (out/(name+'.owner.env')).read_text().splitlines() if '=' in x)
 assert code==expected and receipt.get('status')=='complete' and int(receipt['exit_status'])==expected,receipt
 assert receipt.get('quiescent')=='1' and receipt.get('rss_cap_enforced')=='1' and int(receipt['rss_limit_kib'])==cap,receipt
 assert sha(binary)==identity
 return (out/(name+'.stdout')).read_text()
def counts(text,passed,failed):
 text=re.sub(r'\x1b\[[0-9;]*m','',text)
 found=re.findall(r'^Results: (\d+) total, (\d+) passed, (\d+) failed(?:, 0 skipped)?(?:, 0 pending)?\s*$',text,re.M)
 assert len(found)==1 and tuple(map(int,found[0]))==(passed+failed,passed,failed)
try:
 if a.role=='mcp':
  blob=subprocess.check_output(['git','hash-object','src/app/mcp/main_lazy_protocol.spl'],cwd=source,text=True).strip()
  assert blob=='060954507ec74e4efced6a14f6b59c14d79cacd6','11124 source prerequisite absent; no overlay permitted'
  requests=[{'jsonrpc':'2.0','id':1,'method':'initialize','params':{'protocolVersion':'2025-06-18','capabilities':{},'clientInfo':{'name':'native-regression','version':'1'}}},
   {'jsonrpc':'2.0','method':'initialized','params':{}},{'jsonrpc':'2.0','id':2,'method':'resources/read','params':{'uri':'project:///info'}},
   {'jsonrpc':'2.0','id':3,'method':'ping'},{'jsonrpc':'2.0','id':4,'method':'shutdown','params':{}}]
  request=out/'requests.jsonl';request.write_text(''.join(json.dumps(x)+'\n' for x in requests))
  with request.open('rb') as stream:text=owned('mcp-protocol',[binary],60,262144,stdin=stream)
  messages=[json.loads(x) for x in text.splitlines() if x.strip()];byid={x.get('id'):x for x in messages}
  assert 'error' not in byid[1] and isinstance(byid[1]['result'],dict)
  assert byid[2]['result']['contents'][0]['uri']=='project:///info'
  assert byid[2]['result']['contents'][0]['text']=='Simple MCP (main_lazy)\nWorking Dir: '+str(source)
  assert byid[3]['result']=={}
  result['claims']={'initialize':True,'project_resource_exact':True,'ping':True}
 else:
  fixtures=source/'test/fixtures'/('ce231-'+a.role+'-'+identity[:12]);fixtures.mkdir(parents=True,exist_ok=False)
  hello=fixtures/'hello.spl';hello.write_text('fn main():\n    print "early-full-cli-ok"\n    print 19 + 23\n')
  if a.role=='full-cli':
   assert 'simple' in owned('version',[binary,'--version'],60).lower()
   assert owned('help',[binary,'--help'],60).strip()
   assert owned('run',[binary,'run',hello],300)=='early-full-cli-ok\n42\n'
   positive=fixtures/'positive_spec.spl';positive.write_text('describe "early full CLI execution":\n    it "executes arithmetic and text":\n        expect(19 + 23).to_equal(42)\n        expect("full-cli".len()).to_equal(8)\n')
   negative=fixtures/'negative_spec.spl';negative.write_text('describe "early full CLI failure control":\n    it "reports a real failing assertion":\n        expect(19 + 23).to_equal(43)\n')
   counts(owned('test-positive',[binary,'test',positive,'--mode=interpreter','--max-workers=1'],600),1,0)
   counts(owned('test-negative',[binary,'test',negative,'--mode=interpreter','--max-workers=1'],600,expected=1),0,1)
   result['claims'].update(version=True,help=True,run=True,positive={'total':1,'passed':1,'failed':0},negative={'total':1,'passed':0,'failed':1})
  (out/'fixtures.json').write_text(json.dumps({str(x.relative_to(source)):sha(x) for x in fixtures.iterdir()},indent=2))
  native=out/'hello'
  owned('native-hello-build',[binary,'native-build','--backend','llvm','--target','x86_64-unknown-linux-gnu','--runtime-path',runtime,'--runtime-bundle','core-c-bootstrap','--threads','1','--entry-closure','--mode','one-binary','--entry',hello,'--output',native],600)
  assert native.is_file() and os.access(native,os.X_OK)
  assert owned('native-hello-run',[native],30,262144)=='early-full-cli-ok\n42\n'
  result['claims'].update(native_hello=True,native_hello_sha256=sha(native))
 assert sha(binary)==identity
 assert all(sha(runtime/name)==digest for name,digest in runtime_hashes.items())
 result['status']='BEHAVIOR_PASS'
except Exception as error:result.update(failed_stage=current,error=str(error))
finally:(out/'qualification.json').write_text(json.dumps(result,indent=2))
raise SystemExit(0 if result['status']=='BEHAVIOR_PASS' else 1)

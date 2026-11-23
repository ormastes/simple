"""Wait or execute the prepared child; never rerun parent Hello."""
import hashlib,json,os,subprocess,sys,time,zipfile,stat,importlib.util
from pathlib import Path,PurePosixPath
_s=importlib.util.spec_from_file_location("owner_cleanup",Path(__file__).with_name("owner-cleanup.py"))
_cleanup=importlib.util.module_from_spec(_s);_s.loader.exec_module(_cleanup)
mode=sys.argv[1]
root=Path('ce231-phase3')
if mode in ['wait-pairing','wait-terminal']:
 target=root/('pairing/pairing.json' if mode=='wait-pairing' else 'terminal.json')
 end=time.monotonic()+14500
 while not target.exists():
  pidfile=Path('ce231-controller.pid')
  if pidfile.exists():
   process=Path('/proc')/pidfile.read_text().strip()/'stat'
   if not process.exists() or process.read_text().split(') ',1)[1].startswith('Z '):
    raise SystemExit('controller exited without requested evidence; inspect ce231-controller.log')
  if (root/'terminal.json').exists():raise SystemExit('wrapper terminal without pairing')
  if time.monotonic()>end:raise SystemExit('durable owner collection deadline exceeded')
  time.sleep(5)
 result=json.loads(target.read_text())
 assert result['status']==('NATIVE_PAIRING_PASS' if mode=='wait-pairing' else 'BUILT_UNQUALIFIED'),result
 raise SystemExit(0)
if mode=='qualify-phase3':
 contract=json.loads(Path('ce231-contract.json').read_text())
 binary=Path(contract['source_root'])/'build/bootstrap/stage3/simple'
 build=json.loads((root/'terminal.json').read_text())
 assert build['status']=='BUILT_UNQUALIFIED'
 for name,digest in contract['runtime_files'].items():
  with (Path(contract['runtime_root'])/name).open('rb') as stream:assert hashlib.file_digest(stream,'sha256').hexdigest()==digest
 with binary.open('rb') as stream: assert hashlib.file_digest(stream,'sha256').hexdigest()==build['product_sha256']
 raise SystemExit(subprocess.run([sys.executable,str(Path(__file__).with_name('qualify-product.py')),'--role','phase3',
  '--binary',str(binary),'--source',contract['source_root'],'--runtime',contract['runtime_root'],
  '--output',str(root/'qualification')]).returncode)
assert mode=='early-phase4'
repo=os.environ['GITHUB_REPOSITORY'];run=int(os.environ['PAIRING_RUN'])
def api(route):return json.loads(subprocess.check_output(['gh','api',f'repos/{repo}/'+route]))
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
r=api('actions/runs/'+str(run))
assert r['head_sha']==os.environ['GITHUB_SHA'],'pairing controller differs'
arts=api(f'actions/runs/{run}/artifacts')['artifacts']
a=[x for x in arts if x['name']==f'ce231-native-pairing-{run}'];assert len(a)==1
artifact=api('actions/artifacts/'+str(a[0]['id']));assert not artifact['expired']
pairdir=Path('pairing-intake');pairdir.mkdir()
archive=pairdir/'pairing.zip'
with archive.open('wb') as f:subprocess.run(['gh','api',f"repos/{repo}/actions/artifacts/{artifact['id']}/zip"],stdout=f,check=True)
assert artifact['digest']=='sha256:'+sha(archive)
with zipfile.ZipFile(archive) as z:
 seen=set();assert sum(x.file_size for x in z.infolist())<1024**3
 for i in z.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and ':' not in i.filename
  assert not stat.S_ISLNK(i.external_attr>>16) and p.as_posix().casefold() not in seen
  seen.add(p.as_posix().casefold())
 z.extractall(pairdir)
proof=list(pairdir.rglob('pairing.json'));assert len(proof)==1
contract=json.loads(Path('ce231-contract.json').read_text())
contract.update(runtime_selection_evidence=str(proof[0].resolve()),runtime_selection_evidence_sha256=sha(proof[0]))
Path('early-contract.json').write_text(json.dumps(contract,indent=2))
subprocess.run([sys.executable,str(Path(__file__).with_name('prepare-early-phase4.py')),'early-contract.json','--output','early-plan'],check=True)
plan=json.loads(Path('early-plan/early-phase4.json').read_text())
for p,digest in plan['verified_inputs'].items():assert sha(Path(p))==digest
cap=int(plan['environment']['SIMPLE_PROCESS_TREE_RSS_CAP_KIB'])
avail=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
assert cap<=avail*3//4 and avail>=cap+2*1024*1024,'hosted reserve unavailable'
for p in plan['mkdir_before_start']:Path(p).mkdir(parents=True,exist_ok=False)
env={k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')};env.update(plan['environment'])
output=Path(plan['mkdir_before_start'][0]).parent
with (output/'stdout').open('wb') as out,(output/'stderr').open('wb') as err:
 with _cleanup.acquired_owner(plan['argv'],output/'controller-cleanup.json',cwd=plan['cwd'],env=env,stdout=out,stderr=err) as child:
  code=child.wait()
receipt=dict(x.split('=',1) for x in (output/'owner.env').read_text().splitlines() if '=' in x)
unchanged=all(sha(Path(p))==digest for p,digest in plan['verified_inputs'].items())
product=output/'product/simple'
product_exists=product.is_file() and os.access(product,os.X_OK)
result={'product_sha256':sha(product) if product_exists else None,'product_bytes':product.stat().st_size if product_exists else 0,'status':'BUILT_UNQUALIFIED' if product_exists and code==0 and receipt.get('status')=='complete' and receipt.get('exit_status')=='0' and receipt.get('quiescent')=='1' and receipt.get('rss_cap_enforced')=='1' and int(receipt.get('rss_limit_kib','0'))==cap and unchanged else 'FAILED',
 'exit_status':code,'owner':receipt,'product_exists':product_exists,'inputs_unchanged':unchanged,'pairing_artifact':artifact,
 'scope':'early Phase4 from exact Phase2; independent from Phase3; product behavior unrun'}
(output/'terminal.json').write_text(json.dumps(result,indent=2))
if result['status']!='BUILT_UNQUALIFIED':raise SystemExit(1)
# Qualification invokes the new product, never its Phase2 producer.
raise SystemExit(subprocess.run([sys.executable,str(Path(__file__).with_name('qualify-product.py')),
 '--role',contract['early_product'],'--binary',str(product),'--source',contract['source_root'],
 '--runtime',contract['runtime_root'],'--output',str(output/'qualification')]).returncode)

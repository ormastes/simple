"""Exact-source provisional intake and independent Linux child owners; no promotion."""
import argparse,hashlib,importlib.util,json,os,re,shutil,stat,subprocess,zipfile
from pathlib import Path,PurePosixPath
SOURCE='656fa39e28a7775da0172a4e8eeeea1ac0ea59f0';RUN=45320641691;REPO='ormastes/simple'
FIXED={'seed':(14887483552,'c6802db38d67e89b5c74b454bcca992425be79425110178cf3e83a5579c430b7'),
 'startup':(14887673126,'b72e0731292c16011fc2e723d2ea6794faf65f4e9b5dcd7393ef4a4402da2886'),
 'runtime':(14888456926,'f469dbc2246f6667a9c1f8d893611b6fecd51b4cb6eb2c3d7abb1b51f68784bd')}
def module(name):
 s=importlib.util.spec_from_file_location(name,Path(__file__).with_name(name+'.py'));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
budget=module('runner-budget');cleanup=module('owner-cleanup')
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def save(p,x):Path(p).write_text(json.dumps(x,indent=2))
def api(path):return json.loads(subprocess.check_output(['gh','api','repos/'+REPO+'/'+path],timeout=90))
def elf(p):
 with Path(p).open('rb') as f:h=f.read(20)
 assert h[:6]==b'\x7fELF\x02\x01' and int.from_bytes(h[18:20],'little')==62
def source_guard(source,allowed=None):
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True,timeout=30).strip()==SOURCE
 changes=subprocess.check_output(['git','diff','--name-status','HEAD','--'],cwd=source,text=True,timeout=60).splitlines()
 allowed=allowed or {}
 for line in changes:
  status,name=line.split('\t');assert status=='A' and name in allowed and sha(source/name)==allowed[name]
def tools_snapshot(out):
 values={}
 for name in ('clang','ld.lld','llvm-ar'):
  path=Path(shutil.which(name)).resolve();values[str(path)]=sha(path)
  subprocess.run([str(path),'--version'],stdout=(out/(name+'.version')).open('wb'),check=True,timeout=30)
 save(out/'tool-files.json',values);return values
def download(kind,number,digest,out):
 meta=api('actions/artifacts/'+str(number));assert not meta['expired']
 assert meta['workflow_run']['id']==RUN and meta['workflow_run']['head_sha']==SOURCE
 assert meta['digest']=='sha256:'+digest
 expected=('binary-linux-x86_64-' if kind=='parent' else 'seed-startup-linux-' if kind=='startup' else kind+'-linux-x86_64-')+SOURCE
 assert meta['name']==expected
 archive=out/(kind+'.zip')
 with archive.open('wb') as f:subprocess.run(['gh','api','repos/'+REPO+'/actions/artifacts/'+str(number)+'/zip'],stdout=f,check=True,timeout=180)
 assert sha(archive)==digest and archive.stat().st_size==meta['size_in_bytes']
 dest=out/kind;dest.mkdir();seen=set()
 with zipfile.ZipFile(archive) as z:
  for item in z.infolist():
   p=PurePosixPath(item.filename);key=str(p).casefold()
   assert not p.is_absolute() and '..' not in p.parts and '\\' not in item.filename and ':' not in item.filename and '\x00' not in item.filename
   assert key not in seen and not stat.S_ISLNK(item.external_attr>>16);seen.add(key)
   target=dest.joinpath(*p.parts)
   if item.is_dir():target.mkdir(parents=True,exist_ok=True)
   else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(item))
 save(out/(kind+'-artifact.json'),meta);return dest
def qualify(role,binary,source,runtime,out):
 command=['python3',str(Path(__file__).with_name('qualify-product.py')),'--role',role,'--binary',str(binary),'--source',str(source),'--runtime',str(runtime),'--output',str(out),'--source-revision',SOURCE]
 with cleanup.acquired_owner(command,out.parent/(out.name+'.controller-cleanup.json')) as process:code=process.wait(timeout=2400)
 assert code==0
 q=json.loads((out/'qualification.json').read_text());assert q['status']=='BEHAVIOR_PASS' and q['product_sha256']==sha(binary) and q['claims']['native_hello'];return q
def intake(a):
 out=a.output.resolve();out.mkdir(parents=True,exist_ok=False);source=a.source.resolve()
 source_guard(source);tools=tools_snapshot(out)
 run=api('actions/runs/'+str(RUN));assert run['head_sha']==SOURCE
 jobs=api('actions/runs/'+str(RUN)+'/jobs?per_page=100')['jobs']
 job=next(j for j in jobs if j['name']=='Stage 2 — Linux x86_64')
 assert job['conclusion']=='success'
 assert next(s for s in job['steps'] if s['name']=='Qualify Stage 2 Hello compilation and execution (Linux)')['conclusion']=='success'
 save(out/'original-run.json',run);save(out/'original-linux-stage2-job.json',job)
 dirs={k:download(k,n,d,out) for k,(n,d) in FIXED.items()}
 parentdir=download('parent',a.parent_artifact,a.parent_digest,out)
 seed=dirs['seed']/'simple';parent=parentdir/'simple_stage2';elf(seed);elf(parent)
 startup=json.loads((dirs['startup']/'seed-startup.json').read_text())
 assert startup['status']=='PASS' and startup['exit_code']==0 and startup['seed_sha256']==startup['seed_sha256_after']==sha(seed)
 runtime=dirs['runtime'];expected={}
 for line in (runtime/'runtime-authority.sha256').read_text().splitlines():
  digest,name=line.split();assert name in ('libsimple_native_all.a','libsimple_compiler_backfill.a') and name not in expected
  with (runtime/name).open('rb') as f:header=f.read(8)
  assert sha(runtime/name)==digest and header==b'!<arch>\n';expected[name]=digest
 assert len(expected)==2
 parent.chmod(0o755)
 proof=qualify('parent',parent,source,runtime,out/'parent-native-hello')
 source_guard(source);assert all(sha(p)==h for p,h in tools.items())
 result={'status':'QUALIFIED_PROVISIONAL_PARENT','source':SOURCE,'original_run':RUN,'parent_sha256':sha(parent),'seed_sha256':sha(seed),'runtime_files':expected,'parent_artifact':a.parent_artifact,'parent_zip_digest':a.parent_digest,'fresh_hello':proof,'scope':'exact new Phase2/runtime exercised ABI; no formal stage admission'}
 save(out/'parent.json',result)
 # A sealed per-file manifest binds the actual fresh Hello receipts/logs and
 # inputs for both isolated child runners. ZIPs are transport, not authorities.
 save(out/'files.json',{str(p.relative_to(out)):sha(p) for p in out.rglob('*') if p.is_file()})
def child(a):
 source=a.source.resolve();parentroot=a.parent.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 source_guard(source);tools=tools_snapshot(out)
 disk_free=shutil.disk_usage(out).free
 save(out/'disk.json',{'free_bytes':disk_free,'scope':'measured runner disk; no uninvoked generic-preflight floor imported'})
 manifest=json.loads((parentroot/'files.json').read_text())
 for name,digest in manifest.items():assert sha(parentroot/name)==digest
 pin=json.loads((parentroot/'parent.json').read_text());assert pin['status']=='QUALIFIED_PROVISIONAL_PARENT' and pin['source']==SOURCE and pin['original_run']==RUN
 binary=parentroot/'parent/simple_stage2';binary.chmod(0o755);runtime=parentroot/'runtime'
 assert sha(binary)==pin['parent_sha256']
 q=json.loads((parentroot/'parent-native-hello/qualification.json').read_text());assert q['status']=='BEHAVIOR_PASS' and q['product_sha256']==pin['parent_sha256'] and q['claims']['native_hello']
 policy=budget.sample(a.role);save(out/'resource-policy.json',policy);cap=policy['cap_kib'];budget.recheck(cap)
 env={k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')}
 for leaf in ('cache','tmp','storage','product'):(out/leaf).mkdir()
 env.update(SIMPLE_BINARY=str(binary),SIMPLE_RUNTIME_PATH=str(runtime),SIMPLE_NATIVE_BUILD_RUST='0',SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_PROJECT_ROOT=str(source),SIMPLE_LIB=str(source/'src'),SIMPLE_CACHE=str(out/'cache'),SIMPLE_NATIVE_BUILD_CACHE_DIR=str(out/'cache'),SIMPLE_USER_STORAGE_ROOT=str(out/'storage'),TMPDIR=str(out/'tmp'),CC='clang',SIMPLE_SCV_INVENTORY_COLD_INIT='1',SIMPLE_FILE_WORKER_BATCH='4')
 env.update(SIMPLE_FRONTEND_CACHE_DIR=str(out/'cache/frontend'),SIMPLE_HIR_CACHE_DIR=str(out/'cache/hir'))
 for key in ('SIMPLE_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB'):env[key]=str(cap)
 if a.role=='phase3':
  assert cap>=10*1024*1024,'two-worker per-file Phase3 requires admitted10GiB floor'
  argv=['bash','scripts/bootstrap/build-phase3-phase4.sh','--phase=p3a','--compile-mode=file','--backend=llvm','--target=x86_64-unknown-linux-gnu','--threads=2','--source-root='+str(source),'--build-root='+str(out/'phased'),'--runtime-path='+str(runtime),'--p2-bin='+str(binary),'--non-interactive'];seconds=18500;product=out/'phased/phase3-a/simple'
 else:
  env.update(SIMPLE_FILE_WORKERS='1',SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY='1',SIMPLE_PARSE_SHARDING='1')
  product=out/'product/simple';seconds=14400
  argv=[str(binary),'native-build','--backend','llvm','--target','x86_64-unknown-linux-gnu','--runtime-path',str(runtime),'--runtime-bundle','core-c-bootstrap','--threads','1','--profile=prod','--release','--strip','--managed-build-phase=phase4','--opt-level=standard','--low-memory','--entry-closure','--entry','src/app/cli/_CliMain/main_and_help.spl','--mode','dynload','--cache-dir',str(out/'cache'),'--output',str(product)]
  for path in ('src/compositions/cuda_static','src/compositions/kernel_llvm_cranelift','src/compiler','src/app','src/lib','src/os','src/plugins','src/package_ownership','src/compositions'):argv+=['--source',path]
 command=['perl',str(source/'scripts/resource/process-tree-rss-watchdog.pl'),'--rss-cap-mode=enforce','--max-rss-kib='+str(cap),'--timeout-seconds='+str(seconds),'--receipt='+str(out/'build.owner.env'),'--']+argv
 save(out/'build.argv.json',command);result={'status':'FAILED','role':a.role,'source':SOURCE,'parent_sha256':pin['parent_sha256'],'runtime_files':pin['runtime_files'],'scope':'provisional only, no admission/deployment'}
 try:
  with (out/'build.stdout').open('wb') as stdout,(out/'build.stderr').open('wb') as stderr:
   with cleanup.acquired_owner(command,out/'cleanup.json',cwd=source,env=env,stdout=stdout,stderr=stderr) as process:code=process.wait(timeout=seconds+120)
  receipt=dict(x.split('=',1) for x in (out/'build.owner.env').read_text().splitlines() if '=' in x)
  assert code==0 and receipt['status']=='complete' and receipt['exit_status']=='0' and receipt['quiescent']==receipt['rss_cap_enforced']=='1' and int(receipt['rss_limit_kib'])==cap
  elf(product);result.update(status='BUILT_UNQUALIFIED',product_sha256=sha(product));save(out/'terminal.json',result)
  if a.role=='phase3':
   hello=out/'phased/phase3-a/hello';assert (hello/'stdout').read_bytes()==b'hello\n';elf(hello/'hello')
   assert (hello/'compile.log').is_file();result['native_hello_sha256']=sha(hello/'hello')
  else:result['qualification']=qualify('full-cli',product,source,runtime,out/'qualification')
  assert sha(binary)==pin['parent_sha256'] and all(sha(runtime/n)==h for n,h in pin['runtime_files'].items())
  result['status']='BEHAVIOR_PASS'
 except Exception as error:result['error']=str(error)
 finally:
  try:
   allowed=json.loads((out/'qualification/fixtures.json').read_text()) if (out/'qualification/fixtures.json').exists() else {}
   source_guard(source,allowed);assert all(sha(p)==h for p,h in tools.items());result['immutable_inputs_after']='PASS'
  except Exception as error:result.update(status='FAILED',immutable_inputs_after='FAIL',identity_error=str(error))
  save(out/'terminal.json',result)
 assert result['status']=='BEHAVIOR_PASS',result
p=argparse.ArgumentParser();p.add_argument('mode',choices=['intake','child']);p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--parent',type=Path);p.add_argument('--role',choices=['phase3','full-cli']);p.add_argument('--parent-artifact',type=int);p.add_argument('--parent-digest');a=p.parse_args()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=a.source,text=True).strip()==SOURCE
(intake if a.mode=='intake' else child)(a)

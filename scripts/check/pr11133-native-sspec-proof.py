"""One bounded unchanged SSpec through the real native runner owner; no bootstrap build."""
import hashlib,json,os,re,shutil,stat,subprocess,zipfile
from pathlib import Path,PurePosixPath
SOURCE='432b62c7eec1c7bc2c9e0c43d79f0d5b07c068c0'
PRODUCER_SOURCE='3b6c589b18ffee3bf5bca3b72a3187082df2f9c6'
PRODUCER='d4005d9264b4ba89a9d126080e43d062b4edd29bb33d0ae08f7a42c95050e30c'
RUNTIME_SOURCE='ce231b5b898d797c98d44a9b59a4859a7d792a7b'
SPEC='test/01_unit/compiler/hir/generic_method_semantic_return_spec.spl'
SPEC_BLOB='c76ceb9ed8f178937a55d0db15cd945466468d58'
RUNTIME={'libsimple_native_all.a':'297751e19d6e95b26a214dd325b6e59ec5d956713c57541928a97c717bae7990',
 'libsimple_runtime.a':'0c72026833a4ed17b4233c7905ef5cb2075f9fa450e1befde6d235349b11dc05',
 'libsimple_compiler_backfill.a':'8ae349d93ce20dd3156a15f595a2d99abee3575601630c4efe900a319d44788c',
 'deps/libspl_hosted_runtime.rlib':'faea9c3c0ecb24695bf175d6e5dc57f423c2fa397c75a5da4de6ee0e564251c2'}
source=Path('source').resolve();out=Path('native-sspec-proof').resolve();out.mkdir(exist_ok=False)
result={'status':'FAILED','source':SOURCE,'spec':SPEC,'producer_source':PRODUCER_SOURCE,'producer_sha256':PRODUCER,
 'runtime_source':RUNTIME_SOURCE,'runtime_files':RUNTIME,'scope':'one original SSpec on test-only merged head; mixed-source diagnostic tuple, not original/bootstrap admission'}
stage='intake'
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def save(name,value):(out/name).write_text(json.dumps(value,indent=2))
def api(route):return json.loads(subprocess.check_output(['gh','api','repos/ormastes/simple/'+route]))
def git(*args):return subprocess.check_output(['git',*args],cwd=source,text=True).strip()
def archive(artifact_id,run_id,digest,name):
 a=api(f'actions/artifacts/{artifact_id}');assert a['workflow_run']['id']==run_id and a['digest']=='sha256:'+digest and not a['expired']
 save(name+'-artifact.json',a);p=out/(name+'.zip')
 with p.open('xb') as f:subprocess.run(['gh','api',f'repos/ormastes/simple/actions/artifacts/{artifact_id}/zip'],stdout=f,check=True,timeout=900)
 assert sha(p)==digest
 root=out/name;root.mkdir()
 with zipfile.ZipFile(p) as z:
  seen=set();total=0
  for i in z.infolist():
   n=PurePosixPath(i.filename)
   assert not n.is_absolute() and '..' not in n.parts and '\\' not in i.filename and ':' not in i.filename
   assert n.as_posix().rstrip('/')==i.filename.rstrip('/') and n.as_posix().casefold() not in seen
   seen.add(n.as_posix().casefold());assert not stat.S_ISLNK(i.external_attr>>16)
   total+=i.file_size;assert total<2*1024**3
   if i.is_dir():continue
   target=root.joinpath(*n.parts);target.parent.mkdir(parents=True,exist_ok=True)
   with z.open(i) as src,target.open('xb') as dst:shutil.copyfileobj(src,dst)
 return root
try:
 assert git('rev-parse','HEAD')==SOURCE and git('hash-object',SPEC)==SPEC_BLOB
 run=api('actions/runs/45274376191');assert run['head_sha']==PRODUCER_SOURCE and run['conclusion']=='success';save('producer-run.json',run)
 p1=archive(14870797190,45274376191,'1b24c734d8e0841e63d38fee4ac80420fae41951017ad7e7a35c5072ff05e6d0','producer')
 candidates=[p for p in p1.rglob('simple') if p.is_file() and sha(p)==PRODUCER];assert len(candidates)==1
 producer=candidates[0];producer.chmod(0o755)
 rr=archive(14871469985,45286831153,'5f24b108c986147526e7edf732346af4bb25f90d5d3bc260449841aed2c01fe9','runtime-intake')
 manifests=[p for p in rr.rglob('manifest.json') if json.loads(p.read_text()).get('source_revision')==RUNTIME_SOURCE];assert len(manifests)==1
 runtime=manifests[0].parent/'runtime'
 assert {n:v['sha256'] for n,v in json.loads(manifests[0].read_text())['files'].items()}==RUNTIME
 for n,digest in RUNTIME.items():assert sha(runtime/n)==digest
 owners={}
 for leaf,blob in [('declaration_lowering.spl','d79b5369b74146400faadb630e175e7fe363f045'),('trait_impl_lowering.spl','3c30567331b93722911a027b1d1933d65b48a13d')]:
  path='src/compiler/20.hir/hir_lowering/_Items/'+leaf
  assert git('rev-parse',SOURCE+':'+path)==git('rev-parse',PRODUCER_SOURCE+':'+path)==blob
  owners[path]=blob
 save('source-bindings.json',{'spec_blob':SPEC_BLOB,'spec_sha256':sha(source/SPEC),'owners':owners})
 comparison=subprocess.check_output(['git','diff',PRODUCER_SOURCE,RUNTIME_SOURCE,'--','src/compiler_rust','src/runtime'],cwd=source)
 (out/'mixed-runtime-source.diff').write_bytes(comparison)
 result['runtime_compatibility']='Actual one-test compatibility only. Manifests, native_all/backfill/driver/hosted source and backfill includes unchanged; compiler internals differ. Public rt_any_cast_int additive, timestamp weakening Windows-only; no observed existing Linux ABI signature/layout removal.'
 entry=source/'test/fixtures/pr11133_native_sspec_owner.spl';entry.parent.mkdir(parents=True,exist_ok=True)
 assert not entry.exists();shutil.copyfile(Path(__file__).with_suffix('.spl').with_name('pr11133-native-sspec-owner.spl'),entry)
 for name in ['cache','tmp','storage','xdg-cache']:(out/name).mkdir()
 env={k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')}
 env.update(SIMPLE_BINARY=str(producer),SIMPLE_RUNTIME_PATH=str(runtime),SIMPLE_NATIVE_RUNTIME_BUNDLE='core-c-bootstrap',
  SIMPLE_NATIVE_BUILD_RUST='0',SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_PROJECT_ROOT=str(source),SIMPLE_LIB=str(source/'src'),
  SIMPLE_FILE_WORKERS='1',SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY='1',SIMPLE_FILE_WORKER_BATCH='4',SIMPLE_PARSE_SHARDING='1',
  SIMPLE_NATIVE_BUILD_THREADS='1',SIMPLE_SCV_INVENTORY_COLD_INIT='1',SIMPLE_CACHE=str(out/'cache'),
  SIMPLE_NATIVE_BUILD_CACHE_DIR=str(out/'cache'),SIMPLE_USER_STORAGE_ROOT=str(out/'storage'),TMPDIR=str(out/'tmp'),
  XDG_CACHE_HOME=str(out/'xdg-cache'),SIMPLE_CACHE_PROJECT='pr11133-original-sspec-'+SOURCE,CC='clang',SIMPLE_TRACE_CASE_EVENTS='1')
 def identities():
  assert sha(producer)==PRODUCER and git('hash-object',SPEC)==SPEC_BLOB
  for n,digest in RUNTIME.items():assert sha(runtime/n)==digest
  subprocess.run(['git','diff','--exit-code','HEAD','--','src','test'],cwd=source,check=True)
 def owned(name,args,seconds):
  global stage
  stage=name;available=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
  cap=min(available*3//4,available-2097152);assert cap>=4194304
  for k in ['SIMPLE_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB']:env[k]=str(cap)
  command=['perl',str(source/'scripts/resource/process-tree-rss-watchdog.pl'),'--rss-cap-mode=enforce',f'--max-rss-kib={cap}',f'--timeout-seconds={seconds}','--receipt='+str(out/(name+'.owner.env')),'--']+list(map(str,args))
  save(name+'.argv.json',command);save(name+'.reservation.json',{'available_kib':available,'cap_kib':cap,'outside_reserve_kib':2097152,'timeout_seconds':seconds})
  with (out/(name+'.stdout')).open('wb') as stdout,(out/(name+'.stderr')).open('wb') as stderr:
   code=subprocess.run(command,cwd=source,env=env,stdout=stdout,stderr=stderr).returncode
  fields=dict(x.split('=',1) for x in (out/(name+'.owner.env')).read_text().splitlines() if '=' in x)
  assert code==0 and fields['status']=='complete' and fields['exit_status']=='0' and fields['quiescent']=='1' and fields['rss_cap_enforced']=='1' and int(fields['rss_limit_kib'])==cap,fields
  identities();return (out/(name+'.stdout')).read_text()
 identities();save('environment.json',{k:v for k,v in env.items() if k.startswith('SIMPLE_') or k in ('TMPDIR','CC','XDG_CACHE_HOME')})
 adapter=out/'native-sspec-owner'
 owned('adapter-build',[producer,'native-build','--backend','llvm','--target','x86_64-unknown-linux-gnu','--runtime-path',runtime,'--runtime-bundle','core-c-bootstrap','--threads','1','--source','src/compositions/kernel_llvm_cranelift','--source','src','--entry-closure','--entry',entry,'--output',adapter],1800)
 assert adapter.is_file();result['adapter_sha256']=sha(adapter)
 text=owned('original-sspec',[adapter],2100)
 assert 'passed=1 failed=0 skipped=0 pending=0 blocked=0 unsupported=0 outcome=OK' in text
 assert 'exit=0 tree_reaped=true timed_out=false cancelled=false' in text
 traces=list((out/'tmp').rglob('*.trace-events.sdnstream'))
 case='publishes the owned zero-method-binder result and preserves an ordinary signature'
 trace_lines=[line for p in traces for line in p.read_text().splitlines() if case in line]
 assert any(re.search(r'phase\s*:\s*"finished"',line) and re.search(r'outcome\s*:\s*"passed"',line) for line in trace_lines),trace_lines
 completions=list((out/'tmp').rglob('*.complete'));assert completions
 save('native-evidence-files.json',{str(p.relative_to(out)):sha(p) for p in traces+completions})
 result.update(status='PASS',passed=1,failed=0,skipped=0,pending=0,case_name=case,inputs_unchanged=True)
except Exception as error:result.update(failed_stage=stage,error=str(error))
finally:save('terminal.json',result)
raise SystemExit(0 if result['status']=='PASS' else 1)

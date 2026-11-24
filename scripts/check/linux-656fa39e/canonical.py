"""Conditional canonical Linux P3b -> P4, separate wrapper and frozen source."""
import argparse,importlib.util,json,os,pathlib,shutil,subprocess,tarfile,traceback,zipfile
P=pathlib.Path
s=importlib.util.spec_from_file_location('parent_gate',P(__file__).with_name('phase3-parent.py'));g=importlib.util.module_from_spec(s);s.loader.exec_module(g);c=g.c
WRAPPER='ed9c404d54065443ed5da8403a07dbaa1d2395fb'
PARENT_RUN=45340259012

def fields(p):return dict(x.split('=',1) for x in p.read_text().splitlines() if '=' in x)
def hashes(root):return {str(p.relative_to(root)):c.sha(p) for p in root.rglob('*') if p.is_file()}
def check(root,manifest):
 for name,digest in manifest.items():
  p=pathlib.PurePosixPath(name);assert not p.is_absolute() and '..' not in p.parts and ':' not in name and '\\' not in name
  assert c.sha(root/p)==digest

def wrapper(root,out):
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True,timeout=30).strip()==WRAPPER
 assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True,timeout=30).strip()
 paths=subprocess.check_output(['git','ls-files','-z','scripts/bootstrap','scripts/check/lib/bootstrap-stage3','config'],cwd=root,timeout=60).decode().split('\0')
 identity={str(root/p):c.sha(root/p) for p in paths if p and (root/p).is_file()}
 c.save(out/'wrapper.json',{'sha':WRAPPER,'compiled_source':c.SOURCE,'files':identity});return identity

def parent_b(a,out):
 run=int(os.environ['GITHUB_RUN_ID']);head=os.environ['GITHUB_SHA'];aid=int(os.environ['P3B_ARTIFACT'])
 jobs=c.api(f'actions/runs/{run}/jobs?per_page=100')['jobs'];rows=[j for j in jobs if j['name']=='Linux 656 canonical P3b'];assert len(rows)==1 and rows[0]['conclusion']=='success'
 meta=c.api(f'actions/artifacts/{aid}');assert meta['workflow_run']['id']==run and meta['workflow_run']['head_sha']==head
 assert meta['name']==f'linux-656-canonical-p3b-{run}' and not meta['expired']
 archive=out/'p3b.zip'
 with archive.open('wb') as f:subprocess.run(['gh','api',f'repos/{c.REPO}/actions/artifacts/{aid}/zip'],stdout=f,check=True,timeout=1200)
 assert archive.stat().st_size==meta['size_in_bytes'] and 'sha256:'+c.sha(archive)==meta['digest']
 with zipfile.ZipFile(archive) as z:
  assert z.namelist()==['handoff.tar'],'one explicitly staged transport, no cache or checkout'
  tar=out/'handoff.tar';tar.write_bytes(z.read('handoff.tar'))
 root=out/'p3b-parent';root.mkdir()
 with tarfile.open(tar) as t:
  seen=set()
  for member in t.getmembers():
   p=pathlib.PurePosixPath(member.name)
   assert not p.is_absolute() and '..' not in p.parts and ':' not in member.name and '\\' not in member.name
   assert str(p).casefold() not in seen and (member.isfile() or member.isdir());seen.add(str(p).casefold())
  t.extractall(root,filter='data')
 manifest=json.loads((root/'files.json').read_text());check(root,manifest)
 actual=hashes(root);actual.pop('files.json');assert actual==manifest
 proof=json.loads((root/'terminal.json').read_text())
 assert proof['status']=='P3B_NATIVE_HELLO_PASS' and proof['source']==c.SOURCE and proof['wrapper']==WRAPPER and proof['control']==head and proof['run']==run
 assert proof['parent_run']==PARENT_RUN and proof['admitted'] is False
 owner=fields(root/'build.owner.env');policy=json.loads((root/'resource-policy.json').read_text())
 assert all(owner.get(k)==v for k,v in {'status':'complete','exit_status':'0','quiescent':'1','rss_cap_enforced':'1'}.items())
 assert int(owner['rss_limit_kib'])==policy['cap_kib']==proof['cap_kib'] and policy['cap_kib']<=policy['available_kib']*3//4 and policy['available_kib']-policy['cap_kib']>=2*1024*1024
 argv=json.loads((root/'build.argv.json').read_text())
 for arg in ('--phase=p3b','--compile-mode=file','--backend=llvm','--target=x86_64-unknown-linux-gnu','--threads=2','--p3a-sha256='+proof['parent_sha256'],'--timeout-seconds=18500'):assert arg in argv
 parent=json.loads((root/'phase3-parent.json').read_text());assert parent['phase3_sha256']==proof['parent_sha256'] and parent['source']==c.SOURCE and parent['parent_run']==PARENT_RUN and parent['runtime_files']==proof['runtime_files']
 binary=root/'product/simple';hello=root/'product/hello/hello';c.elf(binary);c.elf(hello)
 assert c.sha(binary)==proof['product_sha256'] and c.sha(hello)==proof['hello_sha256']
 assert (hello.parent/'stdout').read_bytes()==(hello.parent/'expected').read_bytes()==b'hello\n' and (hello.parent/'compile.log').is_file()
 assert proof['immutable_inputs_after']=='PASS'
 runtime=root/'runtime';check(runtime,proof['runtime_files']);binary.chmod(0o755)
 c.save(out/'parent-intake.json',{'artifact':meta,'job':rows[0],'terminal':proof,'files':manifest})
 return binary,runtime,proof['runtime_files'],proof['parent_sha256'],root,manifest

def main():
 p=argparse.ArgumentParser();p.add_argument('--role',choices=['p3b','p4'],required=True);p.add_argument('--source',type=P,required=True);p.add_argument('--wrapper',type=P,required=True);p.add_argument('--output',type=P,required=True);a=p.parse_args()
 source=a.source.resolve();w=a.wrapper.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 c.source_guard(source);wid=wrapper(w,out);tools=c.tools_snapshot(out)
 result={'status':'FAILED','role':a.role,'source':c.SOURCE,'wrapper':WRAPPER,'control':os.environ['GITHUB_SHA'],'run':int(os.environ['GITHUB_RUN_ID']),'parent_run':PARENT_RUN,'admitted':False}
 try:
  if a.role=='p3b':
   intake=out/'parent-intake';intake.mkdir();proof=g.gate(PARENT_RUN,intake)
   binary=P(proof['binary']);runtime=P(proof['runtime']);runtime_files=proof['runtime_files'];parent_root=binary.parent;parent_files=proof['product_files'];ancestor=proof['phase3_sha256'];c.save(out/'phase3-parent.json',proof)
  else:binary,runtime,runtime_files,ancestor,parent_root,parent_files=parent_b(a,out)
  binary.chmod(0o755);parent_sha=c.sha(binary);c.elf(binary)
  check(runtime,runtime_files);check(parent_root,parent_files)
  policy=c.budget.sample(a.role);cap=policy['cap_kib'];c.save(out/'resource-policy.json',policy)
  c.save(out/'disk.json',{'free_bytes':shutil.disk_usage(out).free,'minimum_bytes':None,'scope':'measured standalone owner capacity; actual I/O failures remain fatal'})
  for leaf in ('cache','tmp','storage'):(out/leaf).mkdir()
  env={k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')}
  env.update(SIMPLE_BINARY=str(binary),SIMPLE_RUNTIME_PATH=str(runtime),SIMPLE_NATIVE_BUILD_RUST='0',SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_PROJECT_ROOT=str(source),SIMPLE_LIB=str(source/'src'),SIMPLE_CACHE=str(out/'cache'),SIMPLE_NATIVE_BUILD_CACHE_DIR=str(out/'cache'),SIMPLE_USER_STORAGE_ROOT=str(out/'storage'),TMPDIR=str(out/'tmp'),CC='clang',SIMPLE_SCV_INVENTORY_COLD_INIT='1',SIMPLE_FILE_WORKER_BATCH='4',SIMPLE_BUILD_MEMORY_RESERVE_BYTES=str(2*1024**3))
  for key in ('SIMPLE_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB'):env[key]=str(cap)
  build=out/'phased';assert not build.exists()
  args=['bash',str(w/'scripts/bootstrap/build-phase3-phase4.sh'),'--phase='+a.role,'--compile-mode=file','--backend=llvm','--target=x86_64-unknown-linux-gnu','--threads=2','--source-root='+str(source),'--build-root='+str(build),'--runtime-path='+str(runtime),'--non-interactive']
  args+=['--p3a-bin='+str(binary),'--p3a-sha256='+parent_sha] if a.role=='p3b' else ['--p3b-bin='+str(binary)]
  seconds=18500 if a.role=='p3b' else 16200
  cmd=['perl',str(source/'scripts/resource/process-tree-rss-watchdog.pl'),'--rss-cap-mode=enforce','--max-rss-kib='+str(cap),'--timeout-seconds='+str(seconds),'--receipt='+str(out/'build.owner.env'),'--']+args
  c.save(out/'build.argv.json',cmd);c.save(out/'scope.json',{'entry':'src/app/cli/bootstrap_main.spl' if a.role=='p3b' else 'src/app/cli/main.spl','earlier_direct_cli_entry':'src/app/cli/_CliMain/main_and_help.spl','canonical_p4':'release/debug CLI and four essentials, unchanged wrapper CUDA policy','scope':'provisional generation proof, not formal admission'})
  result.update(parent_sha256=parent_sha,runtime_files=runtime_files,cap_kib=cap)
  c.budget.recheck(cap)
  with (out/'build.stdout').open('wb') as stdout,(out/'build.stderr').open('wb') as stderr:
   with c.cleanup.acquired_owner(cmd,out/'cleanup.json',cwd=source,env=env,stdout=stdout,stderr=stderr) as proc:code=proc.wait(timeout=seconds+120)
  owner=fields(out/'build.owner.env');assert code==0 and all(owner.get(k)==v for k,v in {'status':'complete','exit_status':'0','quiescent':'1','rss_cap_enforced':'1'}.items()) and int(owner['rss_limit_kib'])==cap
  if a.role=='p3b':
   product=build/'phase3-b/simple';hello=build/'phase3-b/hello/hello';c.elf(product);c.elf(hello)
   assert (hello.parent/'stdout').read_bytes()==(hello.parent/'expected').read_bytes()==b'hello\n' and (hello.parent/'compile.log').is_file()
   result.update(status='P3B_NATIVE_HELLO_PASS',product_sha256=c.sha(product),hello_sha256=c.sha(hello))
  else:
   product=build/'p4-from-p3b/bin/simple';c.elf(product)
   result.update(status='BUILT_UNQUALIFIED',product_sha256=c.sha(product));c.save(out/'terminal.json',result)
   product_files={str(p.relative_to(build/'p4-from-p3b')):c.sha(p) for p in (build/'p4-from-p3b').rglob('*') if p.is_file() and 'cache' not in p.parts and 'tmp' not in p.parts}
   result['qualification']=c.qualify('full-cli',product,source,runtime,out/'qualification');check(build/'p4-from-p3b',product_files);result['status']='P4_BEHAVIOR_PASS'
   result['product_files']=product_files
  check(parent_root,parent_files);check(runtime,runtime_files);assert c.sha(binary)==parent_sha
  allowed=json.loads((out/'qualification/fixtures.json').read_text()) if (out/'qualification/fixtures.json').exists() else {}
  c.source_guard(source,allowed);assert all(c.sha(p)==h for p,h in {**wid,**tools}.items());result['immutable_inputs_after']='PASS'
  c.save(out/'terminal.json',result)
  if a.role=='p3b':
   payload=out/'handoff';payload.mkdir();shutil.copytree(runtime,payload/'runtime')
   shutil.copytree(product.parent,payload/'product',ignore=shutil.ignore_patterns('cache','tmp'))
   for name in ('terminal.json','build.owner.env','build.argv.json','resource-policy.json','phase3-parent.json','wrapper.json','build.stdout','build.stderr'):shutil.copy2(out/name,payload/name)
   c.save(payload/'files.json',hashes(payload))
   with tarfile.open(out/'handoff.tar','w') as t:
    for item in sorted(payload.rglob('*')):
     assert not item.is_symlink()
     if item.is_file():t.add(item,arcname=str(item.relative_to(payload)),recursive=False)
 except BaseException as exc:
  result.update(status='FAILED',error=str(exc),traceback=traceback.format_exc());c.save(out/'terminal.json',result);raise
 finally:
  try:
   if 'parent_files' in locals():check(parent_root,parent_files);check(runtime,runtime_files)
   allowed=json.loads((out/'qualification/fixtures.json').read_text()) if (out/'qualification/fixtures.json').exists() else {}
   c.source_guard(source,allowed);assert all(c.sha(p)==h for p,h in {**wid,**tools}.items())
   c.save(out/'immutable-inputs.json',{'status':'PASS'})
  except BaseException as exc:
   result.update(status='FAILED',immutable_inputs_after='FAIL',identity_error=str(exc));c.save(out/'terminal.json',result);c.save(out/'immutable-inputs.json',{'status':'FAIL','error':str(exc)});raise
if __name__=='__main__':main()

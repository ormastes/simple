"""One native Windows proof; original same-run PE, no rebuild or admission claim."""
import ctypes, hashlib, json, os, pathlib, re, shutil, subprocess, sys, traceback, urllib.request, zipfile
P = pathlib.Path
SOURCE = '656fa39e28a7775da0172a4e8eeeea1ac0ea59f0'
RUN = 45326410090
REPO = 'ormastes/simple'
ARTIFACTS = {
 'compiler': (14893476808, 22788885, 'a515f47708946393151a8cd9e0dd4324611e1f833758a71ec9bb3c0650396414', 'binary-windows-mingw-x86_64-'),
 'native': (14891520003, 19927595, 'aef34adf1310bf75ab6bbcf7054062f8d3c14cedf7c525fd22990bdfb86a0de0', 'native-authority-mingw-x86_64-'),
 'runtime': (14890009781, 19261550, '2d5b6b4d1e3e9f7a8dd59921691e2cf21e23ac6b9c2cfea1e90cd389463e34f68', 'runtime-mingw-x86_64-'),
}
ROOT = P.cwd().resolve()
OUT = ROOT/'build/windows-656-proof'
OUT.mkdir(parents=True, exist_ok=True)
BASH = P('C:/Program Files/Git/bin/bash.exe')
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1048576),b''): h.update(b)
 return h.hexdigest()
def save(name,value): (OUT/name).write_text(json.dumps(value,indent=2),encoding='utf-8')
def fields(p): return dict(line.split('=',1) for line in p.read_text().splitlines() if '=' in line)
def command(argv, **kw): return subprocess.run([str(x) for x in argv],check=True,timeout=kw.pop('timeout',120),**kw)
def api(path): return json.loads(command(['gh','api',f'repos/{REPO}/{path}'],capture_output=True,text=True).stdout)
def posix(p):
 s=str(P(p).resolve()).replace('\\','/')
 return '/'+s[0].lower()+s[2:]
def unzip(archive,dest):
 with zipfile.ZipFile(archive) as z:
  seen=set()
  for m in z.infolist():
   p=pathlib.PurePosixPath(m.filename)
   assert not p.is_absolute() and '..' not in p.parts and '\\' not in m.filename and ':' not in m.filename
   assert str(p).casefold() not in seen
   seen.add(str(p).casefold())
   assert (m.external_attr>>16)&0o170000 != 0o120000
  z.extractall(dest)
def one(root,name):
 rows=list(root.rglob(name)); assert len(rows)==1,(name,rows)
 return rows[0]
def intake():
 assert command(['git','rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()==SOURCE
 run=api(f'actions/runs/{RUN}')
 assert run['head_sha']==SOURCE and run['event']=='workflow_dispatch'
 jobs=api(f'actions/runs/{RUN}/jobs?per_page=100')['jobs']
 job=next(x for x in jobs if x['id']==138224476921)
 assert job['conclusion']=='success'
 save('upstream.json',{'run':run,'job':job})
 for label,(aid,size,digest,prefix) in ARTIFACTS.items():
  meta=api(f'actions/artifacts/{aid}')
  assert meta['name']==prefix+SOURCE and meta['workflow_run']['id']==RUN and meta['workflow_run']['head_sha']==SOURCE
  assert meta['size_in_bytes']==size and meta['digest']=='sha256:'+digest and not meta['expired']
  archive=OUT/(label+'.zip')
  with archive.open('wb') as f: command(['gh','api',f'repos/{REPO}/actions/artifacts/{aid}/zip'],stdout=f,timeout=300)
  assert archive.stat().st_size==size and sha(archive)==digest
  unzip(archive,OUT/label); save(label+'-artifact.json',meta)
 native=one(OUT/'native','libsimple_native_all.a'); runtime=one(OUT/'runtime','libsimple_runtime.a')
 n=fields(one(OUT/'native','authority.env')); r=fields(one(OUT/'runtime','runtime-identity.env'))
 for receipt in (n,r): assert receipt['source_revision']==SOURCE and receipt['target']=='x86_64-pc-windows-gnullvm'
 assert n['native_all_sha256']==sha(native) and r['runtime_sha256']==sha(runtime)
 bundle=OUT/'bundle'; bundle.mkdir()
 shutil.copy2(native,bundle/native.name); shutil.copy2(runtime,bundle/runtime.name)
 return one(OUT/'compiler','simple_stage2.exe'),bundle
def toolchain():
 name='llvm-mingw-20260922-ucrt-x86_64'
 archive=OUT/(name+'.zip')
 command(['gh','release','download','20260922','--repo','mstorsjo/llvm-mingw','--pattern',name+'.zip','--dir',OUT],timeout=300)
 assert sha(archive)=='e3ad77d117a4bea19a7a3b333341824d79a5a371004a10e25b8504e7b3047666'
 unzip(archive,OUT/'tools')
 return OUT/'tools'/name/'bin'
def provider():
 packages=json.loads((P(__file__).parent/'provider-packages.json').read_text(encoding='utf-8-sig'))
 dest=OUT/'llvm-provider'; dest.mkdir()
 # Immutable packages previously signature-verified by canonical pacman provider probe.
 for row in packages:
  file=OUT/row['file']
  with urllib.request.urlopen('https://repo.msys2.org/mingw/ucrt64/'+row['file'],timeout=120) as r, file.open('wb') as f: shutil.copyfileobj(r,f)
  assert file.stat().st_size==row['bytes'] and sha(file)==row['sha256']
  command(['tar','-xf',file,'-C',dest])
 save('provider-packages.json',packages)
 return dest/'ucrt64/bin'
class Memory(ctypes.Structure):
 _fields_=[('length',ctypes.c_ulong),('load',ctypes.c_ulong)]+[(n,ctypes.c_ulonglong) for n in ('total','available','page_total','page_available','virtual_total','virtual_available','extended')]
def budget():
 m=Memory(); m.length=ctypes.sizeof(m); assert ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m))
 available=min(m.available,m.page_available)//1024
 cap=min(available*3//4,available-2*1024*1024)
 assert cap>=2*1024*1024
 save('resource.json',{'available_physical_kib':m.available//1024,'available_commit_kib':m.page_available//1024,'cap_kib':cap,'reserve_kib':2*1024*1024})
 return cap
def owned(label,argv,cap,seconds,env):
 receipt=OUT/(label+'.owner.env')
 # Canonical cross-platform Perl owner selects the real Windows Job helper.
 full=[BASH,'-c','exec perl "$@"','owner',posix(ROOT/'scripts/resource/process-tree-rss-watchdog.pl'),f'--max-rss-kib={cap}',f'--timeout-seconds={seconds}',f'--receipt={posix(receipt)}','--',*argv]
 save(label+'.argv.json',{'child':argv,'owner':[str(x) for x in full]})
 with (OUT/(label+'.stdout')).open('wb') as out,(OUT/(label+'.stderr')).open('wb') as err:
  process=subprocess.Popen([str(x) for x in full],stdout=out,stderr=err,env=env)
  try:
   code=process.wait(timeout=seconds+120)
  except BaseException:
   # The acquired, still-live process handle prevents PID reuse during cleanup.
   try:
    if process.poll() is None:
     cleanup=subprocess.run(['taskkill','/PID',str(process.pid),'/T','/F'],capture_output=True,text=True,timeout=30)
     save(label+'.outer-cleanup.json',{'owner_pid':process.pid,'exit':cleanup.returncode,'stdout':cleanup.stdout,'stderr':cleanup.stderr,'scope':'outer failure; no quiescence/PASS claim'})
   except BaseException as cleanup_error:
    save(label+'.cleanup-failure.json',{'error':str(cleanup_error)})
   finally:
    try:
     if process.poll() is None: process.kill()
     process.wait(timeout=30)
    except BaseException as reap_error: save(label+'.reap-failure.json',{'error':str(reap_error)})
   raise
 f=fields(receipt); save(label+'.owner.json',f)
 assert code==0 and f.get('status')=='complete' and f.get('exit_status')=='0', (label,code,f)
 assert f.get('quiescent')=='1' and f.get('rss_cap_enforced')=='1' and int(f['max_rss_kib'])==cap,(label,f)
def main():
 save('control.json',{'script_sha256':sha(__file__),'workflow_head':os.environ.get('GITHUB_SHA'),'source':SOURCE,'upstream_run':RUN,'native_host':sys.platform})
 assert sys.platform=='win32', 'native Windows required'
 compiler,bundle=intake(); tools=toolchain(); llvm=provider()
 env=dict(os.environ)
 for key in list(env):
  if key.startswith('SIMPLE_'): del env[key]
 env.update(PATH=';'.join([str(llvm),str(tools),str(BASH.parent.parent/'usr/bin'),str(BASH.parent.parent/'mingw64/bin'),env['PATH']]),CC=str(tools/'clang.exe'),CXX=str(tools/'clang++.exe'),SIMPLE_MINGW_ROOT=posix(tools.parent),SIMPLE_WINDOWS_ABI='gnu',SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_RUNTIME_PATH=str(bundle),SIMPLE_BOOTSTRAP_WHOLE_PROGRAM='1',SIMPLE_SCV_INVENTORY_COLD_INIT='1',SIMPLE_KEEP_TEMP='1',SIMPLE_PROJECT_ROOT=str(ROOT),SIMPLE_LIB=str(ROOT/'src'),SIMPLE_FRONTEND_CACHE_DIR=str(OUT/'cache/frontend'),SIMPLE_HIR_CACHE_DIR=str(OUT/'cache/hir'))
 # Static imports and dynamically loaded LLVM are distinct dependency boundaries.
 imports=command([tools/'llvm-readobj.exe','--coff-imports',compiler],capture_output=True,text=True).stdout
 assert 'COFF-x86-64' in imports, 'compiler is not native AMD64 PE'
 (OUT/'compiler.imports').write_text(imports,encoding='utf-8')
 if 'libLLVM-23.dll' in imports:
  with (OUT/'dll-bundle.log').open('wb') as f:
   command([BASH,ROOT/'scripts/setup/bundle-llvm-runtime-dlls.shs',posix(compiler),posix(llvm)],stdout=f,stderr=subprocess.STDOUT,env=env)
 else:
  (OUT/'dll-bundle.log').write_text('No static LLVM import; full hash-bound LLVM provider selected on PATH for dynamic loading.\n')
 identities={str(p.relative_to(OUT)):sha(p) for base in (OUT/'compiler',bundle) for p in base.rglob('*') if p.is_file()}
 identities.update({str(p.relative_to(OUT)):sha(p) for base in (tools,llvm) for p in base.glob('*.dll')})
 identities[str((tools/'clang.exe').relative_to(OUT))]=sha(tools/'clang.exe')
 save('inputs.json',{'source':SOURCE,'compiler_sha256':sha(compiler),'files':identities,'clang_sha256':sha(tools/'clang.exe'),'llvm_dll_sha256':sha(llvm/'libLLVM-23.dll')})
 for name,path in [('clang',tools/'clang.exe')]:
  with (OUT/(name+'.imports')).open('wb') as f: command([tools/'llvm-readobj.exe','--coff-imports',path],stdout=f)
 cap=budget()
 owned('version',[str(compiler),'--version'],262144,30,env)
 assert (OUT/'version.stdout').read_text(encoding='utf-8').strip()
 fixture=ROOT/'test/04_smoke/bootstrap_hello_world.spl'
 save('fixture.json',{'path':str(fixture),'sha256':sha(fixture),'bytes':fixture.read_text(encoding='utf-8')})
 hello=OUT/'hello.exe'
 owned('compile',[str(compiler),'native-build','--backend','llvm','--target','x86_64-pc-windows-gnu','--runtime-bundle','core-c-bootstrap','--runtime-path',str(bundle),'--threads','1','--source','src/compiler','--source','src/app','--source','src/lib','--entry-closure','--mode','one-binary','--entry','test/04_smoke/bootstrap_hello_world.spl','--cache-dir',str(OUT/'cache'),'--output',str(hello)],cap,600,env)
 assert hello.is_file()
 owned('hello',[str(hello)],262144,30,env)
 assert (OUT/'hello.stdout').read_bytes().replace(b'\r\n',b'\n')==b'hello\n'
 assert all(sha(OUT/p)==h for p,h in identities.items()), 'input mutated'
 save('terminal.json',{'status':'NATIVE_HELLO_PASS','source':SOURCE,'run':RUN,'compiler_sha256':sha(compiler),'hello_sha256':sha(hello),'scope':'native Windows startup and one LLVM Hello; not formal admission'})
if __name__=='__main__':
 try: main()
 except BaseException as e:
  save('failure.json',{'type':type(e).__name__,'error':str(e),'traceback':traceback.format_exc()})
  raise

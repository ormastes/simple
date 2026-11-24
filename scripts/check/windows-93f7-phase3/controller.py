"""Stage-only provisional P3; consumes an independently successful native P2 proof."""
import importlib.util, json, os, pathlib, shutil, subprocess, sys, traceback, zipfile
P = pathlib.Path
HERE = P(__file__).resolve().parent
CONTRACT = json.loads((HERE/'handoff.json').read_text())
assert CONTRACT['native_proof'] is not None, 'pending actual native P2 proof: no dispatch'
spec = importlib.util.spec_from_file_location('native_intake', HERE/'proof.py')
n = importlib.util.module_from_spec(spec); spec.loader.exec_module(n)
ROLE=os.environ.get('PRODUCT_ROLE','phase3')
assert ROLE in ('phase3','early-full-cli')
n.OUT = n.ROOT/('build/windows-93f7-'+ROLE+'-evidence'); n.OUT.mkdir(parents=True, exist_ok=True)
early_spec=importlib.util.spec_from_file_location('early_cli',HERE/'early_cli.py')
early=importlib.util.module_from_spec(early_spec); early_spec.loader.exec_module(early)

def main():
    assert sys.platform == 'win32'
    pin = CONTRACT['native_proof']
    run = n.api(f"actions/runs/{pin['run']}")
    assert run['head_sha'] == pin['control_sha'] and run['conclusion'] == 'success'
    meta = n.api(f"actions/artifacts/{pin['artifact']}")
    assert meta['workflow_run']['id'] == pin['run'] and meta['workflow_run']['head_sha'] == pin['control_sha']
    assert meta['name'] == f"windows-93f7-native-{pin['run']}" and not meta['expired']
    assert meta['digest'] == 'sha256:'+pin['zip_sha256'] and meta['size_in_bytes'] == pin['zip_bytes']
    archive=n.OUT/'native-proof.zip'
    with archive.open('wb') as stream:
        n.command(['gh','api',f"repos/{n.REPO}/actions/artifacts/{pin['artifact']}/zip"],stdout=stream,timeout=300)
    assert n.sha(archive)==pin['zip_sha256'] and archive.stat().st_size==pin['zip_bytes']
    prior=n.OUT/'native-proof'; prior.mkdir()
    # Native proof caches are not child inputs. Validate the entire ZIP directory,
    # then retain only immediate proof evidence, avoiding long cache paths on Windows.
    with zipfile.ZipFile(archive) as zipped:
        seen=set()
        for member in zipped.infolist():
            path=pathlib.PurePosixPath(member.filename)
            assert not path.is_absolute() and '..' not in path.parts and '\\' not in member.filename and ':' not in member.filename
            assert str(path).casefold() not in seen and (member.external_attr>>16)&0o170000!=0o120000
            seen.add(str(path).casefold())
        terminals=[pathlib.PurePosixPath(m.filename) for m in zipped.infolist() if m.filename.endswith('/terminal.json') and pathlib.PurePosixPath(m.filename).parent.name=='windows-93f7-proof']
        if not terminals and 'terminal.json' in zipped.namelist(): terminals=[pathlib.PurePosixPath('terminal.json')]
        assert len(terminals)==1,'unique proof evidence root required'
        proof_root=terminals[0].parent
        for member in zipped.infolist():
            path=pathlib.PurePosixPath(member.filename)
            if not member.is_dir() and path.parent==proof_root and path.suffix in ('.json','.env','.stdout','.stderr','.log','.imports','.exe'):
                (prior/path.name).write_bytes(zipped.read(member))
    retained_binding=n.one(prior,'binding.json')
    binding_identity=json.loads(n.one(prior,'binding-identity.json').read_text())
    assert json.loads(retained_binding.read_text())==n.BINDING
    assert n.sha(retained_binding)==binding_identity['retained_binding_sha256']
    control=json.loads(n.one(prior,'control.json').read_text())
    assert control['workflow_head']==pin['control_sha'] and control['source']==n.SOURCE and control['upstream_run']==n.RUN and control['native_host']=='win32'
    terminal=json.loads(n.one(prior,'terminal.json').read_text())
    inputs=json.loads(n.one(prior,'inputs.json').read_text())
    assert terminal['status']=='NATIVE_HELLO_PASS' and terminal['source']==n.SOURCE and terminal['run']==n.RUN
    assert terminal['compiler_sha256']==pin['compiler_sha256'] and terminal['hello_sha256']==pin['hello_sha256']
    assert inputs['source']==n.SOURCE and inputs['compiler_sha256']==terminal['compiler_sha256']
    for role in ('version','compile','hello'):
        receipt=n.fields(n.one(prior,role+'.owner.env'))
        assert all(receipt.get(k)==v for k,v in {'status':'complete','exit_status':'0','quiescent':'1','rss_cap_enforced':'1'}.items())
    assert n.one(prior,'hello.stdout').read_bytes().replace(b'\r\n',b'\n')==b'hello\n'
    assert n.sha(n.one(prior,'hello.exe'))==terminal['hello_sha256']
    n.save('parent-proof.json',{'run':run,'artifact':meta,'terminal':terminal,'inputs':inputs,'binding':n.BINDING,'binding_identity':binding_identity,'native_control':control})
    compiler,bundle=n.intake(); tools=n.toolchain(); llvm=n.provider()
    assert n.sha(compiler)==terminal['compiler_sha256']
    env=dict(os.environ)
    for key in list(env):
        if key.startswith('SIMPLE_'): del env[key]
    env.update(PATH=';'.join([str(llvm),str(tools),str(n.BASH.parent.parent/'usr/bin'),str(n.BASH.parent.parent/'mingw64/bin'),env['PATH']]),CC=str(tools/'clang.exe'),CXX=str(tools/'clang++.exe'),SIMPLE_MINGW_ROOT=n.posix(tools.parent),SIMPLE_WINDOWS_ABI='gnu',SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_RUNTIME_PATH=str(bundle),SIMPLE_PROJECT_ROOT=str(n.ROOT),SIMPLE_LIB=str(n.ROOT/'src'),SIMPLE_SCV_INVENTORY_COLD_INIT='1',SIMPLE_FILE_WORKER_BATCH='4')
    imports=n.command([tools/'llvm-readobj.exe','--coff-imports',compiler],capture_output=True,text=True).stdout
    for symbol in ('Thread32First','Thread32Next','ResumeThread','CreateToolhelp32Snapshot','PeekNamedPipe'):
        assert 'Symbol: '+symbol+' (' in imports
    if 'libLLVM-23.dll' in imports:
        n.command([n.BASH,n.ROOT/'scripts/setup/bundle-llvm-runtime-dlls.shs',n.posix(compiler),n.posix(llvm)],env=env)
    # Recreate and compare every previously qualified payload/tool file; never infer identity from filenames.
    for relative,digest in inputs['files'].items(): assert n.sha(n.OUT/relative)==digest,(relative,'changed qualified tuple')
    assert not n.command(['git','status','--porcelain','--untracked-files=no'],capture_output=True,text=True).stdout.strip()
    if ROLE=='early-full-cli': early.fixtures(n)
    tracked=n.command(['git','ls-files','-z'],capture_output=True).stdout.decode().split('\0')
    source={p:n.sha(n.ROOT/p) for p in tracked if p and (n.ROOT/p).is_file()}
    assert n.command(['git','rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()==n.SOURCE
    n.save('source-files.json',source)
    cap=n.budget()
    n.save('build-resource.json',json.loads((n.OUT/'resource.json').read_text()))
    # No invented product-specific floor. Canonical worker admission retains its
    # own coordinator reserve, estimates and refusal; cap is the measured budget.
    free=shutil.disk_usage(n.ROOT).free
    n.save('disk.json',{'free_bytes':free,'minimum_bytes':None,'provenance':'Measured standalone output-volume free space; this entrypoint specifies no fixed disk floor. Actual I/O failures remain fatal under the bounded owner.'})
    for key in ('SIMPLE_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB'):
        env[key]=str(cap)
    env['SIMPLE_BUILD_MEMORY_RESERVE_BYTES']=str(2*1024**3)
    env.update(SIMPLE_USER_STORAGE_ROOT=str(n.OUT/'storage'),SIMPLE_CACHE=str(n.OUT/'cache'),SIMPLE_NATIVE_BUILD_CACHE_DIR=str(n.OUT/'cache'))
    (n.OUT/'tmp').mkdir()
    env.update(TMP=str(n.OUT/'tmp'),TEMP=str(n.OUT/'tmp'),TMPDIR=n.posix(n.OUT/'tmp'))
    product=n.ROOT/('build/windows-93f7-'+ROLE)
    assert not product.exists(),'fresh product namespace required'
    argv=[str(n.BASH),n.posix(n.ROOT/'scripts/bootstrap/build-phase3-phase4.sh'),'--phase=p3a','--compile-mode=file','--win-config=mingw','--target=x86_64-pc-windows-gnu','--backend=llvm','--threads=2','--non-interactive','--source-root='+n.posix(n.ROOT),'--build-root='+n.posix(product),'--p2-bin='+n.posix(compiler),'--runtime-path='+n.posix(bundle)]
    try:
        if ROLE=='early-full-cli':
            result=early.build_and_qualify(n,compiler,bundle,product,cap,env)
        else:
            n.owned('phase3',argv,cap,18000,env)
            candidate=product/'phase3-a/simple.exe'; hello=product/'phase3-a/hello/hello.exe'
            assert candidate.stat().st_size>1024 and hello.stat().st_size>1024
            assert (hello.parent/'stdout').read_bytes().replace(b'\r\n',b'\n')==b'hello\n'
            result={'status':'P3_NATIVE_HELLO_PASS','compiler_sha256':n.sha(candidate),'hello_sha256':n.sha(hello)}
        files={str(p.relative_to(product)):n.sha(p) for p in product.rglob('*') if p.is_file() and ('cache' not in p.parts and 'tmp' not in p.parts)}
        result.update(role=ROLE,admitted=False,source=n.SOURCE,parent_sha256=n.sha(compiler),product_files=files,cap_kib=cap,control_sha=os.environ['GITHUB_SHA'])
    finally:
        unchanged=all(n.sha(n.OUT/p)==h for p,h in inputs['files'].items()) and all(n.sha(n.ROOT/p)==h for p,h in source.items())
        n.save('immutable-inputs.json',{'unchanged':unchanged})
        assert unchanged,'qualified inputs/source changed'
    n.save('terminal.json',result)

if __name__=='__main__':
    try: main()
    except BaseException as exc:
        n.save('failure.json',{'error':str(exc),'traceback':traceback.format_exc()}); raise

"""Canonical P3b/P4 driver; compiled source and wrapper control stay distinct."""
import json,os,pathlib,zipfile

def wrapper(n,contract):
    pin=contract['wrapper'];assert pin is not None,'Pending landed canonical P3b wrapper'
    root=n.ROOT.parent/'wrapper'
    assert n.command(['git','-C',root,'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()==pin['sha']
    pr=n.api('pulls/11275');assert pin['sha']==pin['merge_sha']=='ed9c404d54065443ed5da8403a07dbaa1d2395fb'
    assert pr['merged'] and pr['head']['sha']==pin['pr_head'] and pr['merge_commit_sha']==pin['merge_sha']
    # Pin all actual wrapper-tree files referenced by the script, not a guessed subset.
    files=n.command(['git','-C',root,'ls-files','-z','scripts/bootstrap','scripts/check/lib/bootstrap-stage3','config'],capture_output=True).stdout.decode().split('\0')
    identities={str(root/p):n.sha(root/p) for p in files if p and (root/p).is_file()}
    n.save('wrapper.json',{'control_sha':pin['sha'],'merge_sha':pin['merge_sha'],'compiled_source':n.SOURCE,'files':identities})
    return root/'scripts/bootstrap/build-phase3-phase4.sh',identities

def build(n,role,script,parent,bundle,product,cap,env,qualify):
    args=[str(n.BASH),n.posix(script),'--phase='+('p3b' if role=='phase3b' else 'p4'),'--compile-mode=file','--win-config=mingw','--target=x86_64-pc-windows-gnu','--backend=llvm','--threads=2','--non-interactive','--source-root='+n.posix(n.ROOT),'--build-root='+n.posix(product),'--runtime-path='+n.posix(bundle)]
    if role=='phase3b':args+=['--p3a-bin='+n.posix(parent),'--p3a-sha256='+n.sha(parent)]
    else:args+=['--p3b-bin='+n.posix(parent)]
    n.save('canonical-scope.json',{'role':role,'source':n.SOURCE,'entry':'src/app/cli/bootstrap_main.spl' if role=='phase3b' else 'src/app/cli/main.spl','prior_early_entry':'src/app/cli/_CliMain/main_and_help.spl','scope':'canonical P4 includes release/debug CLIs and four essentials; unchanged wrapper CUDA/target/link policy','parent_sha256':n.sha(parent)})
    n.owned(role,args,cap,18000 if role=='phase3b' else 16200,env)
    if role=='phase3b':
        binary=product/'phase3-b/simple.exe';hello=product/'phase3-b/hello/hello.exe'
        assert binary.stat().st_size>1024 and hello.stat().st_size>1024
        assert (hello.parent/'stdout').read_bytes().replace(b'\r\n',b'\n')==b'hello\n'
        assert (hello.parent/'compile.log').is_file()
        return {'status':'P3B_NATIVE_HELLO_PASS','compiler_sha256':n.sha(binary),'hello_sha256':n.sha(hello)}
    output=product/'p4-from-p3b'
    result=qualify(n,output/'bin/simple.exe',bundle,output,cap,env,parent_phase=3)
    result['canonical_phase']='p4';result['parent_generation']='p3b';return result

def parent(n,contract,phase2):
    run_id=int(os.environ['GITHUB_RUN_ID']);head=os.environ['GITHUB_SHA'];aid=int(os.environ['P3B_ARTIFACT'])
    jobs=n.api(f'actions/runs/{run_id}/jobs?per_page=100')['jobs']
    candidates=[j for j in jobs if j['name']=='Windows 93f7 canonical Phase3b']
    assert len(candidates)==1 and candidates[0]['conclusion']=='success'
    meta=n.api(f'actions/artifacts/{aid}')
    assert meta['workflow_run']['id']==run_id and meta['workflow_run']['head_sha']==head and not meta['expired']
    assert meta['name']==f'windows-93f7-phase3b-{run_id}'
    archive=n.OUT/'phase3b-parent.zip'
    with archive.open('wb') as stream:n.command(['gh','api',f'repos/{n.REPO}/actions/artifacts/{aid}/zip'],stdout=stream,timeout=1200)
    assert archive.stat().st_size==meta['size_in_bytes'] and 'sha256:'+n.sha(archive)==meta['digest']
    dest=n.OUT/'phase3b-parent';dest.mkdir();identities={}
    with zipfile.ZipFile(archive) as z:
        seen=set()
        for row in z.infolist():
            path=pathlib.PurePosixPath(row.filename)
            assert not path.is_absolute() and '..' not in path.parts and '\\' not in row.filename and ':' not in row.filename
            assert str(path).casefold() not in seen and (row.external_attr>>16)&0o170000!=0o120000
            seen.add(str(path).casefold())
        roots=[pathlib.PurePosixPath(r.filename).parent for r in z.infolist() if pathlib.PurePosixPath(r.filename).name=='terminal.json' and pathlib.PurePosixPath(r.filename).parent.name=='windows-93f7-phase3b-evidence']
        assert len(roots)==1;evidence=roots[0];product=evidence.parent/'windows-93f7-phase3b'
        def read(name):return z.read(str(evidence/name))
        terminal=json.loads(read('terminal.json'))
        assert terminal['status']=='P3B_NATIVE_HELLO_PASS' and terminal['role']=='phase3b' and terminal['admitted'] is False
        assert terminal['source']==n.SOURCE and terminal['control_sha']==head and terminal['ancestor_phase2_sha256']==n.sha(phase2)
        assert terminal['parent_sha256']==contract['phase3_parent']['compiler_sha256']
        assert json.loads(read('immutable-inputs.json'))['unchanged'] is True
        owner=dict(line.split('=',1) for line in read('phase3b.owner.env').decode().splitlines() if '=' in line)
        assert all(owner.get(k)==v for k,v in {'status':'complete','exit_status':'0','quiescent':'1','rss_cap_enforced':'1','observer_backend':'win32-job-object'}.items())
        assert int(owner['max_rss_kib'])==terminal['cap_kib']
        policy=json.loads(read('build-resource.json'));available=min(policy['available_physical_kib'],policy['available_commit_kib'])
        assert policy['cap_kib']==terminal['cap_kib'] and policy['cap_kib']<=available*3//4 and available-policy['cap_kib']>=2*1024*1024
        recorded=json.loads(read('phase3b.argv.json'));args=recorded['child'];assert '--timeout-seconds=18000' in recorded['owner']
        for arg in ('--phase=p3b','--compile-mode=file','--win-config=mingw','--target=x86_64-pc-windows-gnu','--backend=llvm','--threads=2','--p3a-sha256='+terminal['parent_sha256']):assert arg in args
        prior=json.loads(read('parent-proof.json'))
        assert prior['binding']==n.BINDING and prior['inputs']==json.loads(n.one(n.OUT/'native-proof','inputs.json').read_text())
        assert json.loads(read('wrapper.json'))['control_sha']==contract['wrapper']['sha']
        for relative,digest in terminal['product_files'].items():
            path=pathlib.PurePosixPath(relative.replace('\\','/'))
            assert not path.is_absolute() and '..' not in path.parts and ':' not in str(path) and 'cache' not in path.parts and 'tmp' not in path.parts
            target=dest/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(str(product/path)))
            assert n.sha(target)==digest;identities[str(target)]=digest
        binary=dest/'phase3-b/simple.exe';hello=dest/'phase3-b/hello/hello.exe'
        assert n.sha(binary)==terminal['compiler_sha256'] and n.sha(hello)==terminal['hello_sha256']
        assert (hello.parent/'stdout').read_bytes().replace(b'\r\n',b'\n')==b'hello\n' and (hello.parent/'compile.log').is_file()
        for name in ('terminal.json','phase3b.owner.env','phase3b.argv.json','wrapper.json','immutable-inputs.json','phase3-intake.json','build-resource.json'):(dest/('parent-'+name)).write_bytes(read(name))
    n.save('phase3b-intake.json',{'artifact':meta,'job':candidates[0],'terminal':terminal,'files':identities})
    return binary,identities


def direct_release(n,script,parent,bundle,product,cap,env,qualify):
    """Actual P3a -> production release CLI, without claiming it is P3b."""
    # Exact landed run_stage4_all release configuration; no source extraction,
    # generation relabel, debug/tools replay, or P3a --p3b-bin substitution.
    smoke_env=dict(env)
    env=dict(env)
    assert n.sha(parent)==json.loads((n.OUT/'phase3-intake.json').read_text())['terminal']['compiler_sha256']
    production=script.read_text(encoding='utf-8')
    for token in ('--source src/compositions/cuda_disabled','--entry src/app/cli/main.spl','--profile=prod --release --strip'):
        assert token in production,'pinned canonical release contract changed'
    for key in ('SIMPLE_BOOTSTRAP_STAGE3','SIMPLE_LINKER','SIMPLE_HIR_SHARDING','SIMPLE_MIR_SHARDING','SIMPLE_BOOTSTRAP_WHOLE_PROGRAM'):
        env.pop(key,None)
    cache=product/'cli-release/cache';tmp=product/'cli-release/tmp';binary=product/'bin/simple.exe'
    for directory in (cache/'frontend',cache/'hir',tmp,binary.parent):directory.mkdir(parents=True,exist_ok=False)
    env.update(OS=env.get('OS','Windows_NT'),SIMPLE_WINDOWS_ABI='gnu',SIMPLE_LINKER_FLAVOR='gnu',
        SIMPLE_BINARY=str(parent),SIMPLE_BOOTSTRAP='1',SIMPLE_BOOTSTRAP_STAGE4='1',SIMPLE_STAGE4_STREAMING_SURFACES='1',
        SIMPLE_NATIVE_GO_TO_END='1',SIMPLE_CACHE_SCOPE='stage4',SIMPLE_FRONTEND_CACHE='1',SIMPLE_FRONTEND_CACHE_DIR=str(cache/'frontend'),
        SIMPLE_HIR_CACHE='1',SIMPLE_HIR_CACHE_DIR=str(cache/'hir'),SIMPLE_NATIVE_ARENA_DECLS='1',SIMPLE_NO_STUB_FALLBACK='1',
        SIMPLE_NO_DEPRECATED_WARNINGS='1',SIMPLE_PACKAGE_INDEX_COLD_INIT='1',LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING='1',
        SIMPLE_NATIVE_BUILD_TARGET='x86_64-pc-windows-gnu',SIMPLE_NATIVE_BUILD_THREADS='2',SIMPLE_NATIVE_BUILD_CACHE_DIR=str(cache),
        SIMPLE_RUNTIME_PATH=str(bundle),SIMPLE_FILE_WORKERS='1',TMPDIR=n.posix(tmp),TMP=str(tmp),TEMP=str(tmp))
    argv=[str(parent),'native-build','--target','x86_64-pc-windows-gnu','--backend','llvm','--runtime-bundle','core-c-bootstrap']
    for source in ('src/compositions/cuda_disabled','src/compiler','src/app','src/lib','src/os','src/plugins'):argv+=['--source',source]
    argv+=['--entry-closure','--timeout','14400','--profile=prod','--release','--strip','--threads','2','--cache-dir',str(cache),
        '--mode','dynload','--entry','src/app/cli/main.spl','--runtime-path',str(bundle),'-o',str(binary)]
    n.save('canonical-scope.json',{'role':'phase4-direct','producer_generation':'P3a','parent_sha256':n.sha(parent),
        'entry':'src/app/cli/main.spl','wrapper_control':'ed9c404d54065443ed5da8403a07dbaa1d2395fb',
        'scope':'Production release CLI from P3a, independent of P3b; not canonical P3b-to-P4 bundle or formal admission',
        'configuration':'landed canonical release source roots/CUDA-disabled/prod/dynload/LLVM/GNU/file-workers/threads2',
        'products':['release CLI'],'later_distinct_products':'actual P3b-to-P4 release/debug CLI and four essentials'})
    n.owned('phase4-direct',argv,cap,14400,env)
    result=qualify(n,binary,bundle,product,cap,smoke_env,parent_phase=3)
    result.update(producer_generation='P3a',product_generation='direct-P4-release',canonical_phase='P3a-to-P4-release')
    return result

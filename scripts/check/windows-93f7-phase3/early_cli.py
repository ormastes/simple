"""Existing provisional full-CLI scope and real executable checks, on Windows."""
import json, re
FIXTURE='test/bootstrap_qualification_93f7'
EXPECTED='early-full-cli-ok\n42\n'

def fixtures(n):
    root=n.ROOT/FIXTURE; root.mkdir()
    bodies={'hello.spl':'fn main():\n    print "early-full-cli-ok"\n    print 19 + 23\n'}
    for negative in (False,True):
        name='test-negative' if negative else 'test-positive'
        bodies[name+'_spec.spl']='use std.spec.*\ndescribe "full CLI":\n    it "counts assertion":\n        expect(19 + 23).to_equal('+('43' if negative else '42')+')\n'
    for name,body in bodies.items(): (root/name).write_text(body,encoding='utf-8')
    n.command(['git','add','--',FIXTURE])
    assert set(n.command(['git','diff','--cached','--name-only'],capture_output=True,text=True).stdout.splitlines())=={FIXTURE+'/'+name for name in bodies}
    n.save('fixtures.json',{FIXTURE+'/'+name:n.sha(root/name) for name in bodies})

def cuda(n):
    manifest=n.ROOT/'src/compiler/simple.sdn'; section=False; selected=False; values={}
    for line in manifest.read_text().splitlines():
        if re.fullmatch(r'compiler_backends:\s*',line): section=True; continue
        if re.match(r'[^\s#]',line): section=False; selected=False
        if section and re.fullmatch(r'  cuda:\s*',line): selected=True; continue
        if section and re.match(r'  [^\s#]',line): selected=False
        if section and selected:
            row=line.split()
            if row and row[0] in ('enabled:','placement:'):
                assert len(row)>=2 and row[0] not in values; values[row[0]]=row[1]
    assert values['enabled:'] in ('true','false') and values['placement:'] in ('static','dynamic')
    mode=values['placement:'] if values['enabled:']=='true' else 'disabled'
    root='src/compositions/cuda_'+mode
    chosen=n.ROOT/root/'plugins/backend_registry/selected_cuda_backend.spl'
    template=n.ROOT/('src' if mode=='static' else root)/'plugins/backend_registry/selected_cuda_backend.spl'
    assert n.sha(chosen)==n.sha(template)
    n.save('cuda.json',{'source_root':root,'manifest_sha256':n.sha(manifest),'selected_sha256':n.sha(chosen),'mode':mode})
    return root

def build_and_qualify(n,parent,bundle,product,cap,env):
    product.mkdir(); binary=product/'simple.exe'
    env.update(SIMPLE_BINARY=str(parent),SIMPLE_NATIVE_BUILD_RUST='0',SIMPLE_FILE_WORKERS='1',SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY='1',SIMPLE_PARSE_SHARDING='1',SIMPLE_FRONTEND_CACHE_DIR=str(n.OUT/'cache/frontend'),SIMPLE_HIR_CACHE_DIR=str(n.OUT/'cache/hir'))
    argv=[str(parent),'native-build','--backend','llvm','--target','x86_64-pc-windows-gnu','--runtime-path',str(bundle),'--runtime-bundle','core-c-bootstrap','--threads','1','--profile=prod','--release','--strip','--managed-build-phase=phase4','--opt-level=standard','--low-memory','--entry-closure','--entry','src/app/cli/_CliMain/main_and_help.spl','--mode','dynload','--cache-dir',str(n.OUT/'cache'),'--output',str(binary)]
    for path in (cuda(n),'src/compositions/kernel_llvm_cranelift','src/compiler','src/app','src/lib','src/os','src/plugins','src/package_ownership','src/compositions'): argv+=['--source',path]
    n.owned('build',argv,cap,14400,env)
    assert binary.stat().st_size>1024
    digest=n.sha(binary); n.save('build-result.json',{'status':'BUILT_UNQUALIFIED','product_sha256':digest,'parent_phase':2,'admitted':False})
    product_inputs={str(p.relative_to(product)):n.sha(p) for p in product.rglob('*') if p.is_file()}
    n.save('product-inputs.json',product_inputs)
    smoke=n.OUT/'smoke'; smoke.mkdir()
    (smoke/'tmp').mkdir()
    env.update(SIMPLE_BINARY=str(binary),SIMPLE_CACHE=str(smoke/'cache'),SIMPLE_NATIVE_BUILD_CACHE_DIR=str(smoke/'cache'),SIMPLE_FRONTEND_CACHE_DIR=str(smoke/'cache/frontend'),SIMPLE_HIR_CACHE_DIR=str(smoke/'cache/hir'),SIMPLE_USER_STORAGE_ROOT=str(smoke/'storage'),SIMPLE_CACHE_PROJECT='93f7-product-'+digest)
    env.update(TMP=str(smoke/'tmp'),TEMP=str(smoke/'tmp'),TMPDIR=n.posix(smoke/'tmp'))
    def run(name,args,seconds,limit,expected_code=0):
        live=n.budget(); limit=min(limit,cap,live)
        n.save(name+'.resource.json',{'sample':json.loads((n.OUT/'resource.json').read_text()),'selected_cap_kib':limit})
        local=dict(env)
        for key in ('SIMPLE_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB'): local[key]=str(limit)
        n.owned(name,[str(x) for x in args],limit,seconds,local,expected_code)
        return (n.OUT/(name+'.stdout')).read_text(encoding='utf-8').replace('\r\n','\n')
    for name in ('version','help'): assert run(name,[binary,'--'+name],120,1048576).strip()
    fixture=FIXTURE+'/hello.spl'
    assert run('run',[binary,'run',fixture],300,4194304)==EXPECTED
    for negative in (False,True):
        name='test-negative' if negative else 'test-positive'
        text=run(name,[binary,'test',FIXTURE+'/'+name+'_spec.spl','--mode=interpreter','--max-workers=1'],300,4194304,int(negative))
        assert re.findall(r'^Results: (\d+) total, (\d+) passed, (\d+) failed\s*$',text,re.M)==[('1',str(int(not negative)),str(int(negative)))]
        assert not re.search(r'^(Pending|Skipped|Blocked|Unverified):\s*[1-9]|UNVERIFIED',text,re.M)
    env['SIMPLE_BOOTSTRAP_WHOLE_PROGRAM']='1'
    for key in ('SIMPLE_FILE_WORKERS','SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY','SIMPLE_PARSE_SHARDING'): env.pop(key,None)
    hello=product/'hello.exe'
    run('native-hello-build',[binary,'native-build','--backend','llvm','--target','x86_64-pc-windows-gnu','--runtime-path',bundle,'--runtime-bundle','core-c-bootstrap','--threads','1','--source',FIXTURE,'--entry-closure','--mode','one-binary','--entry',fixture,'--output',hello],600,4194304)
    assert hello.stat().st_size>1024 and run('native-hello-run',[hello],30,262144)==EXPECTED
    assert n.sha(binary)==digest and all(n.sha(product/p)==h for p,h in product_inputs.items())
    return {'status':'FULL_CLI_BEHAVIOR_PASS','parent_phase':2,'product_sha256':digest,'hello_sha256':n.sha(hello),'claims':['version','help','run','test-positive-1/0','test-negative-0/1','native-hello']}

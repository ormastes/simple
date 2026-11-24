"""Previously unverified PR gates only; a qualified pure-Simple full CLI is mandatory."""
import argparse,hashlib,json,os,re,stat,subprocess,zipfile
from pathlib import Path,PurePosixPath

SOURCE='ce231b5b898d797c98d44a9b59a4859a7d792a7b'
CONTROLS={'early':'d18104ea541e35a2fdcbe3561461605c0e6d38ac','phase3':'4251185d95178ced5f102075c332096e18b74c91'}
def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def read(p):return json.loads(p.read_text())
def receipt(p,expected=0):
    fields={}
    for line in p.read_text().splitlines():
        k,v=line.split('=',1);assert k not in fields;fields[k]=v
    assert fields.get('status')=='complete' and fields.get('exit_status')==str(expected),fields
    assert fields.get('quiescent')=='1' and fields.get('rss_cap_enforced')=='1',fields
    return fields
def counts(text,passed=None,failed=0):
    text=re.sub(r'\x1b\[[0-9;]*m','',text)
    assert not re.search(r'\bUNVERIFIED\b|process[- ]error',text,re.I)
    for value in re.findall(r'^(?:Pending|Skipped|Blocked|Unverified|Process errors):\s*(\d+)\b',text,re.M|re.I):
        assert int(value)==0,'nonzero separate incomplete verdict'
    rows=re.findall(r'^Results: (\d+) total, (\d+) passed, (\d+) failed(?:, (\d+) skipped)?(?:, (\d+) pending)?\s*$',text,re.M)
    assert len(rows)==1,'missing/ambiguous counted test verdict'
    total,ok,bad,skip,pending=[int(x or 0) for x in rows[0]]
    if passed is None:assert total==ok+bad and ok>0
    else:assert total==passed+failed and ok==passed
    assert bad==failed and skip==pending==0
    return {'total':total,'passed':ok,'failed':bad,'skipped':skip,'pending':pending}
def intake(root,kind):
    run,artifact=read(root/'run.json'),read(root/'artifact.json')
    assert run['head_sha']==CONTROLS[kind] and run['status']=='completed' and run['conclusion']=='success'
    assert artifact['workflow_run']['id']==run['id'] and not artifact['expired']
    expected=('ce231-child-early-phase4-' if kind=='early' else 'provisional-ce231-phase4-from-phase3-')+str(run['id'])
    assert artifact['name']==expected and artifact['digest']=='sha256:'+sha(root/'artifact.zip')
    # Intake retains only products and evidence, never previous cache or queue authority.
    ex=root/'extracted';ex.mkdir(exist_ok=False)
    with zipfile.ZipFile(root/'artifact.zip') as z:
        seen=set();retained=0
        for info in z.infolist():
            n=info.filename;p=PurePosixPath(n)
            assert not p.is_absolute() and '..' not in p.parts and '\\' not in n and ':' not in n
            assert n.rstrip('/')==p.as_posix().rstrip('/') and n.casefold() not in seen
            assert not stat.S_ISLNK(info.external_attr>>16);seen.add(n.casefold())
            if info.is_dir() or any(x in p.parts for x in ('cache','tmp','storage','xdg-cache','scv')):continue
            retained+=info.file_size;assert retained<2*1024**3
            target=ex.joinpath(*p.parts);target.parent.mkdir(parents=True,exist_ok=True)
            with z.open(info) as src,target.open('xb') as dst:
                import shutil
                shutil.copyfileobj(src,dst)
    if kind=='early':
        matches=[p for p in ex.rglob('qualification.json') if read(p).get('role')=='full-cli' and read(p).get('status')=='BEHAVIOR_PASS']
        assert len(matches)==1;q=matches[0].parent;proof=read(matches[0]);product=q.parent/'product/simple'
        built=read(q.parent/'terminal.json');assert built['status']=='BUILT_UNQUALIFIED' and built['inputs_unchanged']
        receipt(q.parent/'owner.env');assert built['product_sha256']==proof['product_sha256']
        names={'version':0,'help':0,'run':0,'test-positive':0,'test-negative':1,'native-hello-build':0,'native-hello-run':0}
        suffix='.stdout';hello=q/'hello'
    else:
        matches=[p for p in ex.rglob('terminal.json') if read(p).get('scope')=='provisional-phase4-full-cli-from-recovered-phase3' and read(p).get('status')=='PASS']
        assert len(matches)==1;q=matches[0].parent;proof=read(matches[0]);product=q.parent/'product/simple';hello=q.parent/'product/hello'
        receipt(q/'build.owner.env');names={'version':0,'help':0,'run':0,'test-positive':0,'test-negative':1,'native-hello-build':0,'native-hello-run':0};suffix='.stdout'
    assert proof['source']==SOURCE and sha(product)==proof['product_sha256']
    for name,code in names.items():receipt(q/(name+'.owner.env'),code)
    assert (q/('run'+suffix)).read_text()=='early-full-cli-ok\n42\n'
    assert (q/('native-hello-run'+suffix)).read_text()=='early-full-cli-ok\n42\n'
    counts((q/('test-positive'+suffix)).read_text(),1,0);counts((q/('test-negative'+suffix)).read_text(),0,1)
    expected_hello=proof.get('claims',proof)['native_hello_sha256'];assert sha(hello)==expected_hello
    assert (q/('help'+suffix)).read_text().strip() and 'simple' in (q/('version'+suffix)).read_text().lower()
    product.chmod(0o755)
    return product,{'run':run['id'],'artifact':artifact['id'],'control':run['head_sha'],'compiler_sha256':sha(product),'source':SOURCE,'product_smokes':'verified existing receipts; NOT rerun'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--intake',type=Path,required=True)
    p.add_argument('--kind',choices=CONTROLS,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--mcp-binary',type=Path);p.add_argument('--mcp-sha256');p.add_argument('--mcp-source-revision')
    a=p.parse_args();source=a.source.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
    result={'status':'BLOCKED','pr':11133,'source':SOURCE,'gates':{},'unrun': ['check-compiler','check-lib','check-mcp','check-lsp','mcp-stdio'],'scope':'mandatory PR source checks, not release admission'}
    current='full-cli-admission'
    try:
        binary,identity=intake(a.intake.resolve(),a.kind);result['runtime']=identity
        assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()==SOURCE
        subprocess.run(['git','diff','--exit-code','HEAD','--','src','test'],cwd=source,check=True)
        result['source_tree']=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=source,text=True).strip()
        for name in ['cache','storage','tmp','xdg-cache']:(out/name).mkdir()
        env={k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')}
        env.update(SIMPLE_BINARY=str(binary),SIMPLE_BIN=str(binary),SIMPLE_LIB=str(source/'src'),SIMPLE_PROJECT_ROOT=str(source),
                   SIMPLE_NATIVE_BUILD_RUST='0',SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_CACHE=str(out/'cache'),SIMPLE_USER_STORAGE_ROOT=str(out/'storage'),
                   TMPDIR=str(out/'tmp'),XDG_CACHE_HOME=str(out/'xdg-cache'),SIMPLE_CACHE_PROJECT='pr11133-'+SOURCE+'-'+sha(binary))
        def owned(name,args,expected=0,seconds=1800):
            nonlocal current
            current=name
            available=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
            cap=min(available*3//4,available-2097152);assert cap>=2097152
            childenv=env.copy()
            for key in ['SIMPLE_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB']:childenv[key]=str(cap)
            command=['perl',str(source/'scripts/resource/process-tree-rss-watchdog.pl'),'--rss-cap-mode=enforce',f'--max-rss-kib={cap}',f'--timeout-seconds={seconds}','--receipt='+str(out/(name+'.owner.env')),'--',str(binary)]+list(map(str,args))
            (out/(name+'.argv.json')).write_text(json.dumps(command))
            with (out/(name+'.stdout')).open('wb') as stdout,(out/(name+'.stderr')).open('wb') as stderr:
                code=subprocess.run(command,cwd=source,env=childenv,stdout=stdout,stderr=stderr).returncode
            fields=receipt(out/(name+'.owner.env'),expected);assert code==expected and int(fields['rss_limit_kib'])==cap
            assert sha(binary)==identity['compiler_sha256']
            return (out/(name+'.stdout')).read_text()
        def checked(text,expected_errors=False):
            rows=[]
            for line in text.splitlines():
                try:value=json.loads(line)
                except ValueError:continue
                if isinstance(value,dict) and value.get('command')=='check':rows.append(value)
            assert len(rows)==1,'missing/ambiguous real check result'
            row=rows[0];assert row['checked']>0
            if expected_errors:assert row['errors']>0 and row['status']!='ok'
            else:assert row['status']=='ok' and row['errors']==0 and row.get('semantic_complete') is True and row.get('coverage')=='semantic'
            return row
        # Check capability has not previously been proved by the full-CLI product smokes.
        fixtures=source/'test/fixtures/pr11133-check-capability';fixtures.mkdir(parents=True,exist_ok=False)
        positive=fixtures/'positive.spl';negative=fixtures/'negative.spl'
        positive.write_text('fn main():\n    print 19 + 23\n');negative.write_text('fn main(:\n    print 42\n')
        result['check_capability']={'positive':checked(owned('check-positive',['check','--json',positive],seconds=300)),
                                    'negative':checked(owned('check-negative',['check','--json',negative],expected=1,seconds=300),True)}
        for name,path in [('check-compiler','src/compiler'),('check-lib','src/lib'),('check-mcp','src/app/mcp'),('check-lsp','src/app/simple_lsp_mcp')]:
            result['gates'][name]=checked(owned(name,['check','--json',path]));result['unrun'].remove(name)
            (out/'progress.json').write_text(json.dumps(result,indent=2))
        current='mcp-stdio-prerequisite'
        if a.mcp_binary:
            mcp=a.mcp_binary.resolve()
            assert a.mcp_source_revision==SOURCE and re.fullmatch('[0-9a-f]{64}',a.mcp_sha256 or '')
            assert mcp.is_file() and sha(mcp)==a.mcp_sha256 and os.access(mcp,os.X_OK)
            # Identity/source binding only: this unmodified spec supplies the first protocol proof.
            result['mcp_server']={'path':str(mcp),'sha256':a.mcp_sha256,'source_revision':a.mcp_source_revision,'mode':'reviewed-native-artifact'}
            env['SIMPLE_MCP_TEST_BINARY']=str(mcp)
        else:
            mcp=source/'bin/simple_mcp_server'
            assert mcp.is_file() and os.access(mcp,os.X_OK),'Linux canonical wrapper/native MCP binary missing; simple mcp delegates to it, not an embedded server'
            setup=(source/'scripts/setup/setup.shs').read_text()
            marker="cat > simple_mcp_server <<'EOF'\n"
            assert setup.count(marker)==1
            canonical=setup.split(marker,1)[1].split('\nEOF\n',1)[0]+'\n'
            assert mcp.read_bytes()==canonical.encode(), 'installed wrapper differs from exact PR setup owner'
            result['mcp_server']={'path':str(mcp),'sha256':sha(mcp),'source_revision':SOURCE,'mode':'canonical-installed-wrapper'}
            # Leave SIMPLE_MCP_TEST_BINARY unset: exercise the real spec's default lookup.
        spec='test/02_integration/app/mcp_stdio_integration_spec.spl'
        result['stdio_spec_sha256']=sha(source/spec)
        result['gates']['mcp-stdio']=counts(owned('mcp-stdio',['test',spec,'--mode=interpreter','--max-workers=1'],seconds=1800),16,0)
        assert sha(mcp)==result['mcp_server']['sha256'];result['unrun'].remove('mcp-stdio')
        subprocess.run(['git','diff','--exit-code','HEAD','--','src','test'],cwd=source,check=True)
        result['status']='PASS'
    except Exception as error:
        executed_gate=current in ('check-compiler','check-lib','check-mcp','check-lsp','mcp-stdio') and (out/(current+'.argv.json')).exists()
        result.update(status='FAILED' if executed_gate else 'BLOCKED',failed_stage=current,error=str(error))
    finally:(out/'terminal.json').write_text(json.dumps(result,indent=2))
    return 0 if result['status']=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())

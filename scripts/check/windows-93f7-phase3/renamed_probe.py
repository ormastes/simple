"""One small real focused-capsule worker probe; no executable/Hello run."""
import hashlib,json,os,pathlib,shutil

def stage(n,original,here):
    dest=n.OUT/'staged-producer';shutil.copytree(original.parent,dest)
    candidate=dest/'simple.exe';assert not candidate.exists()
    shutil.copy2(original,candidate)
    originals={str(p.relative_to(original.parent)):n.sha(p) for p in original.parent.rglob('*') if p.is_file()}
    assert all(n.sha(dest/p)==h for p,h in originals.items()) and n.sha(candidate)==n.sha(original)
    identities={str(p):n.sha(p) for p in dest.rglob('*') if p.is_file()}
    prior=here/'prior-failure'
    record={'original_path':str(original),'staged_path':str(candidate),'sha256':n.sha(candidate),'siblings':originals,'staged_files':identities,'prior_run':45357104625,'prior_job':138317543998,'prior_artifact':14903967189,'prior_zip_sha256':'63bc945b6774f76f5e895909e08797703b9c2c46c00d64b0e01f54b19d8e70af','prior_receipt_sha256':n.sha(prior/'phase3.owner.env'),'prior_argv_sha256':n.sha(prior/'phase3.argv.json'),'prior_producer_argv':next(a for a in json.loads((prior/'phase3.argv.json').read_text())['child'] if a.startswith('--p2-bin='))}
    n.save('producer-staging.json',record)
    return candidate,identities

def run(n,candidate,bundle,env,cap,tools):
    root=n.OUT/'focused-worker-probe';root.mkdir()
    project=root/'source';entry=project/'src/app/cli/bootstrap_main.spl';entry.parent.mkdir(parents=True)
    entry.write_bytes(b'fn main() -> i64:\n    return 7\n')
    for args in (['init','--quiet'],['add','--','src']):n.command(['git','-C',project,*args])
    n.command(['git','-C',project,'-c','user.name=Bootstrap Fixture','-c','user.email=bootstrap-fixture@example.invalid','commit','--quiet','-m','Bound focused worker fixture'])
    fixture_sha=n.sha(entry)
    n.save('probe-fixture.json',{'path':'src/app/cli/bootstrap_main.spl','sha256':fixture_sha,'body':entry.read_text(),'git_head':n.command(['git','-C',project,'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip(),'scope':'independent tiny real source; canonical focused Stage3 route, not original compiler body'})
    cache=root/'cache';output=root/'probe.obj'
    local=dict(env)
    for key in ('SIMPLE_BOOTSTRAP_WHOLE_PROGRAM','SIMPLE_BOOTSTRAP_STAGE4'):local.pop(key,None)
    local.update(SIMPLE_PROJECT_ROOT=str(project),SIMPLE_LIB=str(project/'src'),SIMPLE_BINARY=str(candidate),SIMPLE_NATIVE_BUILD_RUST='0',SIMPLE_FILE_WORKERS='1',SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY='1',SIMPLE_PARSE_SHARDING='1',SIMPLE_FILE_WORKER_BATCH='4',SIMPLE_CACHE=str(cache),SIMPLE_NATIVE_BUILD_CACHE_DIR=str(cache),SIMPLE_FRONTEND_CACHE_DIR=str(cache/'frontend'),SIMPLE_HIR_CACHE_DIR=str(cache/'hir'),SIMPLE_USER_STORAGE_ROOT=str(root/'storage'))
    (root/'tmp').mkdir()
    local.update(SIMPLE_FRONTEND_CACHE='1',SIMPLE_HIR_CACHE='1',SIMPLE_NATIVE_ARENA_DECLS='1',SIMPLE_NATIVE_RUNTIME_BUNDLE='core-c-bootstrap',SIMPLE_NATIVE_BUILD_TARGET='x86_64-pc-windows-gnu',SIMPLE_NATIVE_BUILD_THREADS='1',SIMPLE_BUILD_MEMORY_RESERVE_BYTES=str(2*1024**3),TMP=str(root/'tmp'),TEMP=str(root/'tmp'),TMPDIR=n.posix(root/'tmp'))
    limit=min(cap,6*1024*1024)
    for key in ('SIMPLE_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB'):local[key]=str(limit)
    launcher=root/'probe.sh'
    launcher.write_bytes(b'set -eu\nSTAGE3_POLICY_SDN="$1"; export STAGE3_POLICY_SDN; shift\n. "$1"; shift\nstage3_apply_native_host_link_policy x86_64-pc-windows-gnu file mingw dynlib\nexec "$@"\n')
    args=[str(n.BASH),n.posix(launcher),n.posix(n.ROOT/'scripts/bootstrap/stage3-native-host-link-policy.sdn'),n.posix(n.ROOT/'scripts/bootstrap/stage3-native-host-link-policy.shs'),n.posix(candidate),'native-build','--backend','llvm','--target','x86_64-pc-windows-gnu','--runtime-bundle','core-c-bootstrap','--runtime-path',n.posix(bundle),'--threads','1','--source','src/app','--entry-closure','--entry','src/app/cli/bootstrap_main.spl','--mode','dynload','--emit-object','--cache-dir',n.posix(cache),'--output',n.posix(output)]
    previous=pathlib.Path.cwd()
    try:
        os.chdir(project);n.owned('focused-worker-probe',args,limit,300,local)
    finally:
        os.chdir(previous)
        n.save('probe-fixture-after.json',{'unchanged':n.sha(entry)==fixture_sha,'sha256':n.sha(entry)})
        assert n.sha(entry)==fixture_sha
    text=(n.OUT/'focused-worker-probe.stdout').read_text(encoding='utf-8')
    assert '[stage3-route] per-file worker pool + per-module link' in text
    assert 'running compiler path unavailable' not in text
    assert output.is_file() and output.stat().st_size>20
    with output.open('rb') as stream:assert stream.read(2)==b'\x64\x86','expected actual AMD64 COFF object'
    inventories=[];fixture_proven=False;objects=[]
    for inventory in cache.rglob('inventory'):
        rows=inventory.read_text(encoding='utf-8').splitlines()
        if len(rows)<2 or not list(inventory.parent.glob('*.claim')):continue
        excluded=set((inventory.parent/'excluded').read_text().splitlines()) if (inventory.parent/'excluded').is_file() else set()
        selected=[key for key in rows[1:] if key and key not in excluded];assert selected
        records=[]
        for key in selected:
            base=hashlib.sha256(key.encode()).hexdigest()
            terminal=inventory.parent/(base+'.terminal');claim=inventory.parent/(base+'.claim')
            fields=terminal.read_text(encoding='utf-8').splitlines();owned=claim.read_text(encoding='utf-8').splitlines()
            assert len(fields)==5 and fields[0]=='PASS' and fields[2]==key and fields[1:4]==owned[:3]
            done=inventory.parent/(hashlib.sha256(fields[1].encode()).hexdigest()+'.done')
            assert done.read_bytes()==fields[1].encode(),'exact terminal owner completion marker required'
            if key.replace('\\','/').endswith('/src/app/cli/bootstrap_main.spl'):
                assert fields[3]==fixture_sha;fixture_proven=True
            records.append({'key':key,'terminal_sha256':n.sha(terminal),'owner':fields[1],'done_sha256':n.sha(done)})
        inventories.append({'path':str(inventory),'sha256':n.sha(inventory),'records':records,'excluded':sorted(excluded)})
    for receipt in cache.rglob('*.receipt'):
        try:row=n.fields(receipt)
        except (ValueError,UnicodeError):continue
        if row.get('status')!='PASS' or not row.get('module') or not row.get('object'):continue
        assert any(str(receipt.parent/'inventory')==q['path'] for q in inventories)
        terminal=receipt.parent/(hashlib.sha256(row['module'].encode()).hexdigest()+'.terminal')
        fields=terminal.read_text(encoding='utf-8').splitlines()
        assert len(fields)==5 and fields[0]=='PASS' and fields[2]==row['module']
        done=receipt.parent/(hashlib.sha256(fields[1].encode()).hexdigest()+'.done')
        assert done.read_bytes()==fields[1].encode()
        raw=row['object'].replace('\\','/')
        if len(raw)>3 and raw[0]=='/' and raw[2]=='/':raw=raw[1].upper()+':'+raw[2:]
        obj=pathlib.Path(raw)
        if not obj.is_file():continue
        assert obj.resolve().is_relative_to(root.resolve()),'worker object escaped private probe namespace'
        with obj.open('rb') as stream:machine=stream.read(2)
        if machine==b'\x64\x86':objects.append({'module':row['module'],'path':str(obj),'sha256':n.sha(obj),'receipt_sha256':n.sha(receipt)})
    assert len(inventories)>=2 and fixture_proven and objects,'actual complete HIR/MIR ledgers and object proof required'
    assert n.sha(entry)==fixture_sha
    n.save('focused-worker-probe-result.json',{'status':'FOCUSED_WORKER_LEDGER_PASS','compiler_sha256':n.sha(candidate),'compiler_path':str(candidate),'fixture_sha256':fixture_sha,'inventories':inventories,'objects':objects,'output_sha256':n.sha(output),'scope':'focused self_exe gate passed and real workers sealed small fixture; output not executed; not full compiler success'})

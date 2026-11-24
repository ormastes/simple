"""Pinned prior worker evidence only; never converts its failed link into PASS."""
import hashlib,json,pathlib,zipfile
sha=lambda b:hashlib.sha256(b).hexdigest()

def intake(n,compiler,inputs):
    root=n.OUT/'retained-worker';root.mkdir()
    run=n.api('actions/runs/45363635244')
    assert run['head_sha']=='af2c6a7616350f9c6a8b712084291ba253631338' and run['status']=='completed' and run['conclusion']=='failure'
    job=n.api('actions/jobs/138339650772')
    assert job['run_id']==45363635244 and job['conclusion']=='failure'
    meta=n.api('actions/artifacts/14904869761')
    digest='5b57d45e124bc690a235287776bb0816095b040c2c7676bfe3015ec8e2f7fc0a'
    assert meta['workflow_run']['id']==45363635244 and meta['workflow_run']['head_sha']==run['head_sha']
    assert meta['name']=='windows-93f7-phase3-pathfix-45363635244' and not meta['expired']
    assert meta['digest']=='sha256:'+digest and meta['size_in_bytes']==7213109
    archive=root/'artifact.zip'
    with archive.open('wb') as stream:n.command(['gh','api',f'repos/{n.REPO}/actions/artifacts/14904869761/zip'],stdout=stream,timeout=300)
    assert archive.stat().st_size==7213109 and n.sha(archive)==digest
    with zipfile.ZipFile(archive) as z:
        names=z.namelist(); assert len(names)==len(set(names))
        folded=set()
        for member in z.infolist():
            path=pathlib.PurePosixPath(member.filename)
            assert not path.is_absolute() and '..' not in path.parts and '\\' not in member.filename and ':' not in member.filename
            assert str(path).casefold() not in folded and (member.external_attr>>16)&0o170000!=0o120000
            folded.add(str(path).casefold())
        prefix='build/windows-93f7-phase3-pathfix-evidence/'
        read=lambda p:z.read(prefix+p)
        fixture=b'fn main() -> i64:\n    return 7\n'
        source=read('focused-worker-probe/source/src/app/cli/bootstrap_main.spl')
        assert source==fixture
        snapshots=[p for p in names if '/snapshots/' in p and p.endswith('/src/app/cli/bootstrap_main.spl')]
        assert len(snapshots)==1 and z.read(snapshots[0])==fixture
        inventories=[p for p in names if '/scv/source-inventory/generations/' in p and p.endswith('.inventory')]
        if not inventories: inventories=[p for p in names if '/snapshots/' in p and 'inventory' in p.rsplit('/',1)[-1]]
        assert any(('src/app/cli/bootstrap_main.spl|'+sha(fixture)+'|').encode() in z.read(p) for p in inventories)
        records=[]
        for p in names:
            if not p.endswith('/inventory') or '/cache/hir/' not in p:continue
            folder=p.rsplit('/',1)[0]+'/'
            rows=z.read(p).decode().splitlines()
            excluded=set(z.read(folder+'excluded').decode().splitlines()) if folder+'excluded' in names else set()
            for key in rows[1:]:
                if not key or key in excluded:continue
                stem=folder+sha(key.encode()); terminal=z.read(stem+'.terminal').decode().splitlines(); claim=z.read(stem+'.claim').decode().splitlines()
                assert len(terminal)==5 and terminal[0]=='PASS' and terminal[2]==key and terminal[1:4]==claim[:3]
                done=folder+sha(terminal[1].encode())+'.done'
                assert z.read(done)==terminal[1].encode()
                assert terminal[4] in ('CACHE_STORED','UNCACHED')
                if key=='app.cli.bootstrap_main': assert rows[0]==terminal[3]
                records.append(dict(folder=folder,key=key,owner=terminal[1],cache_key=terminal[3],inventory_identity=rows[0],terminal_sha256=sha(z.read(stem+'.terminal')),done_sha256=sha(z.read(done))))
        assert len(records)==2
        objects=[]
        for p in names:
            if not p.endswith('.receipt'):continue
            fields=dict(line.split('=',1) for line in z.read(p).decode().splitlines() if '=' in line)
            if fields.get('status')!='PASS' or not fields.get('object'):continue
            assert fields['module']=='app.cli.bootstrap_main'
            raw=fields['object'].replace('\\','/')
            marker='/focused-worker-probe/'
            assert marker in raw
            obj=prefix+'focused-worker-probe/'+raw.split(marker,1)[1]
            data=z.read(obj);assert len(data)>20 and data[:2]==b'\x64\x86'
            assert any(r['key']==fields['module'] and r['folder']==p.rsplit('/',1)[0]+'/' for r in records)
            assert p.rsplit('/',1)[1]==sha(fields['module'].encode())+'.receipt'
            objects.append(dict(path=obj,sha256=sha(data),bytes=len(data),receipt_sha256=sha(z.read(p))))
        assert objects
        copies=[dict(path=p,sha256=sha(z.read(p)),bytes=len(z.read(p))) for p in names if p.endswith('.o')]
        staging=json.loads(read('producer-staging.json'));assert staging['sha256']=='f8be04ff2979d4b41cd038f8aa3601619891ec7cf74b55dbe73f06c84baa85f0'
        assert json.loads(read('preflight-immutable-inputs.json'))['unchanged']
        assert json.loads(read('probe-fixture-after.json'))['unchanged']
        owner=dict(line.split('=',1) for line in read('focused-worker-probe.owner.env').decode().splitlines() if '=' in line)
        log=read('focused-worker-probe.stdout').decode()
        assert 'completed_workers=1 failed_workers=0 failed_modules=0 unfinished=0' in log
        assert 'Runtime source directory not found' in log
        assert not any(p.endswith('/phase3.owner.env') for p in names)
        result=dict(status='WORKER_EVIDENCE_VALIDATED_PROBE_LINK_FAILED',archive_sha256=sha(archive.read_bytes()),producer=staging,fixture_sha256=sha(fixture),records=records,objects=objects,all_object_copies=copies,owner=owner,full_phase3_started=False,limitations=['Overall probe remains exit1; no final probe.obj or executable.', 'HIR terminal key is composite hir_cache_key, not raw source SHA. Claim equality and independent SCV source SHA verified; cache-key recomputation not claimed.', 'Worker proof does not qualify full compiler, runtime link, or native Hello.'])
        assert all(owner.get(k)==v for k,v in {'status':'complete','exit_status':'1','primary_exit_status':'1','quiescent':'1','rss_cap_enforced':'1','max_rss_kib':'6291456','peak_rss_kib':'132332'}.items())
        assert 'running compiler path unavailable' not in log
        assert log.count('error: focused native-build:')==1
        assert 'LLVM native linking failed: Runtime compilation failed: Runtime source directory not found' in log
        assert 'src/runtime/runtime.c' in log
        assert staging['sha256']==n.sha(compiler)
        prior_inputs=json.loads(read('parent-proof.json'))['inputs']
        assert prior_inputs==inputs,'retained worker and current producer/runtime/tool identities differ'
        argv=json.loads(read('focused-worker-probe.argv.json'))
        assert '--emit-object' in argv['child'] and '--entry-closure' in argv['child']
        assert any('staged-producer/simple.exe' in a.replace('\\','/') for a in argv['child'])
        result['admission_scope']='Only renamed producer focused worker availability and sealed fixture object; original final-link exit1 remains FAILURE.'
        result['artifact']=meta
        result['prior_run']=run
        n.save('retained-worker-validation.json',result)
        for name in ('focused-worker-probe.owner.env','focused-worker-probe.argv.json','focused-worker-probe.stdout','focused-worker-probe.stderr','producer-staging.json','preflight-immutable-inputs.json','probe-fixture.json','probe-fixture-after.json'):
            (root/name).write_bytes(read(name))

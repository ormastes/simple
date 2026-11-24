"""Actual P3a intake only; no parent execution or authority fabrication."""
import json,pathlib,zipfile
RUN=45366816359
CONTROL='4e69b62fcfa853a5bd020431a2853bb6d96b3bf8'

def accept(n,contract,phase2):
    pin=contract['phase3_parent']
    assert pin is not None,'Actual Phase3 artifact identity is still unavailable'
    assert pin['run']==RUN and pin['control_sha']==CONTROL
    run=n.api(f'actions/runs/{RUN}')
    assert run['head_sha']==CONTROL and run['event']=='workflow_dispatch'
    jobs=n.api(f'actions/runs/{RUN}/jobs?per_page=100')['jobs']
    matches=[j for j in jobs if j['id']==138350557255 and j['name']=='Windows 93f7 phase3']
    assert len(matches)==1 and matches[0]['status']=='completed' and matches[0]['conclusion']=='success'
    meta=n.api(f"actions/artifacts/{pin['artifact']}")
    assert meta['workflow_run']['id']==RUN and meta['workflow_run']['head_sha']==CONTROL and not meta['expired']
    assert meta['name']==f'windows-93f7-phase3-retained-{RUN}'
    assert meta['size_in_bytes']==pin['zip_bytes'] and meta['digest']=='sha256:'+pin['zip_sha256']
    archive=n.OUT/'phase3-parent.zip'
    with archive.open('wb') as out:n.command(['gh','api',f"repos/{n.REPO}/actions/artifacts/{pin['artifact']}/zip"],stdout=out,timeout=1200)
    assert archive.stat().st_size==pin['zip_bytes'] and n.sha(archive)==pin['zip_sha256']
    dest=n.OUT/'phase3-parent';dest.mkdir()
    with zipfile.ZipFile(archive) as z:
        seen=set()
        for row in z.infolist():
            p=pathlib.PurePosixPath(row.filename)
            assert not p.is_absolute() and '..' not in p.parts and '\\' not in row.filename and ':' not in row.filename
            assert str(p).casefold() not in seen and (row.external_attr>>16)&0o170000!=0o120000
            seen.add(str(p).casefold())
        roots=[pathlib.PurePosixPath(row.filename).parent for row in z.infolist() if pathlib.PurePosixPath(row.filename).name=='terminal.json' and pathlib.PurePosixPath(row.filename).parent.name=='windows-93f7-phase3-retained-evidence']
        assert len(roots)==1,'Unique actual Phase3 evidence required'
        evidence=roots[0];product=evidence.parent/'windows-93f7-phase3-retained'
        def read(name):return z.read(str(evidence/name))
        terminal=json.loads(read('terminal.json'))
        assert terminal['status']=='P3_NATIVE_HELLO_PASS' and terminal['role']=='phase3' and terminal['admitted'] is False
        assert terminal['source']==n.SOURCE and terminal['control_sha']==CONTROL and terminal['parent_sha256']==n.sha(phase2)
        assert terminal['compiler_sha256']==pin['compiler_sha256'] and terminal['hello_sha256']==pin['hello_sha256']
        assert json.loads(read('immutable-inputs.json'))['unchanged'] is True
        owner=dict(line.split('=',1) for line in read('phase3.owner.env').decode().splitlines() if '=' in line)
        assert all(owner.get(k)==v for k,v in {'status':'complete','exit_status':'0','quiescent':'1','rss_cap_enforced':'1','observer_backend':'win32-job-object'}.items())
        assert int(owner['max_rss_kib'])==terminal['cap_kib']
        policy=json.loads(read('build-resource.json'));available=min(policy['available_physical_kib'],policy['available_commit_kib'])
        assert policy['cap_kib']==terminal['cap_kib'] and policy['cap_kib']<=available*3//4 and available-policy['cap_kib']>=2*1024*1024
        recorded=json.loads(read('phase3.argv.json'));args=recorded['child']
        assert '--timeout-seconds=18000' in recorded['owner']
        producers=[a for a in args if a.startswith('--p2-bin=')];assert len(producers)==1 and producers[0].endswith('/staged-producer/simple.exe')
        staging=json.loads(read('producer-staging.json'));assert staging['sha256']==n.sha(phase2)
        worker=json.loads(read('retained-worker-validation.json'));assert worker['status']=='WORKER_EVIDENCE_VALIDATED_PROBE_LINK_FAILED' and worker['producer']['sha256']==n.sha(phase2)
        assert worker['artifact']['id']==14904869761 and worker['archive_sha256']=='5b57d45e124bc690a235287776bb0816095b040c2c7676bfe3015ec8e2f7fc0a'
        for arg in ('--phase=p3a','--compile-mode=file','--win-config=mingw','--target=x86_64-pc-windows-gnu','--backend=llvm','--threads=2'):assert arg in args
        prior=json.loads(read('parent-proof.json'))
        assert prior['binding']==n.BINDING and prior['terminal']['compiler_sha256']==n.sha(phase2)
        original_inputs=json.loads(n.one(n.OUT/'native-proof','inputs.json').read_text())
        assert prior['inputs']==original_inputs
        identities={}
        for relative,digest in terminal['product_files'].items():
            path=pathlib.PurePosixPath(relative.replace('\\','/'))
            assert not path.is_absolute() and '..' not in path.parts and ':' not in str(path)
            assert 'cache' not in path.parts and 'tmp' not in path.parts
            target=dest/path;target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(z.read(str(product/path)))
            assert n.sha(target)==digest,(relative,'changed Phase3 product')
            identities[str(target)]=digest
        binary=dest/'phase3-a/simple.exe';hello=dest/'phase3-a/hello/hello.exe'
        assert n.sha(binary)==pin['compiler_sha256'] and n.sha(hello)==pin['hello_sha256']
        assert (hello.parent/'stdout').read_bytes().replace(b'\r\n',b'\n')==b'hello\n'
        assert (hello.parent/'compile.log').is_file()
        for name in ('terminal.json','immutable-inputs.json','phase3.owner.env','phase3.argv.json','parent-proof.json','build-resource.json','producer-staging.json','retained-worker-validation.json'):
            (dest/('parent-'+name)).write_bytes(read(name))
    n.save('phase3-intake.json',{'run':run,'job':matches[0],'artifact':meta,'terminal':terminal,'product_identities':identities,'scope':'verified native Phase3a; no Phase3b/fixpoint or formal admission claim'})
    return binary,identities

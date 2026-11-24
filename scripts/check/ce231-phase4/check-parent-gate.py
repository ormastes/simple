"""Synthetic schema/gate tests only. These are not bootstrap qualification."""
import json,tempfile,zipfile,sys
from pathlib import Path
from parent_gate import verify,sha,SOURCE,CONTROL,RUNTIME_ID,RUNTIME_ZIP_SHA
with tempfile.TemporaryDirectory() as directory:
    root=Path(directory);ex=root/'extracted';phase=ex/'ce231-phase3';q=phase/'qualification'
    q.mkdir(parents=True);runtime=root/'runtime';runtime.mkdir()
    parent=ex/'source/build/bootstrap/stage3/simple';parent.parent.mkdir(parents=True);parent.write_bytes(b'synthetic-phase3')
    (q/'hello').write_bytes(b'synthetic-native-hello')
    (q/'native-hello-run.stdout').write_bytes(b'early-full-cli-ok\n42\n')
    runtime_files={}
    for name in ['libsimple_native_all.a','libsimple_compiler_backfill.a']:
        (runtime/name).write_bytes(name.encode());runtime_files[name]=sha(runtime/name)
    def save(path,value):path.write_text(json.dumps(value))
    contract={'source_revision':SOURCE,'runtime_artifact_id':RUNTIME_ID,'runtime_artifact_zip_sha256':RUNTIME_ZIP_SHA,
              'source_root':'/source','runtime_root':'/runtime',
              'phase3_memory_kib':8388608,'phase2_producer_sha256':'a'*64,'runtime_files':runtime_files}
    terminal={'source':SOURCE,'status':'BUILT_UNQUALIFIED','inputs_unchanged':True,'product_sha256':sha(parent),
              'producer_sha256':'a'*64,'runtime_files':runtime_files}
    behavior={'source':SOURCE,'status':'BEHAVIOR_PASS','role':'phase3','product_sha256':sha(parent),
              'runtime_files':runtime_files,'claims':{'native_hello':True,'native_hello_sha256':sha(q/'hello')}}
    save(ex/'ce231-contract.json',contract);save(phase/'terminal.json',terminal);save(q/'qualification.json',behavior)
    save(q/'native-hello-build.argv.json',['owner','--','/source/build/bootstrap/stage3/simple','native-build','--runtime-path','/runtime','--backend','llvm','--output','/qualification/hello'])
    save(q/'native-hello-run.argv.json',['owner','--','/qualification/hello'])
    for path,cap in [(phase/'owner.env',8388608),(q/'native-hello-build.owner.env',4194304),(q/'native-hello-run.owner.env',262144)]:
        path.write_text(f'status=complete\nexit_status=0\nquiescent=1\nrss_cap_enforced=1\nrss_limit_kib={cap}\n')
    save(root/'run.json',dict(head_sha=CONTROL,status='completed',conclusion='success',id=123))
    def pack():
        with zipfile.ZipFile(root/'artifact.zip','w') as z:
            for path in ex.rglob('*'):
                if path.is_file():z.write(path,path.relative_to(ex).as_posix())
        save(root/'artifact.json',dict(id=456,workflow_run={'id':123},name='ce231-child-phase3-123',expired=False,digest='sha256:'+sha(root/'artifact.zip')))
    pack();verify(parent,root,runtime,sha(parent),456)
    if '--argv-only' in sys.argv:
        path=q/'native-hello-build.argv.json'
        value=json.loads(path.read_text());value[2]='/phase2/simple';save(path,value);pack()
        try:verify(parent,root,runtime,sha(parent),456)
        except AssertionError:print('PASS: newly added command binding rejects Phase2 masquerading as Phase3')
        else:raise AssertionError('wrong compiler invocation admitted')
        raise SystemExit(0)
    count=0
    for path,change in [(q/'qualification.json',{'role':'full-cli'}),(q/'qualification.json',{'status':'FAILED'}),
                        (phase/'terminal.json',{'inputs_unchanged':False}),(root/'run.json',{'conclusion':'failure'})]:
        original=path.read_text();value=json.loads(original);value.update(change);save(path,value);pack()
        try:verify(parent,root,runtime,sha(parent),456)
        except AssertionError:count+=1
        else:raise AssertionError('bad parent admitted')
        path.write_text(original)
    path=q/'native-hello-run.stdout';original=path.read_bytes();path.write_bytes(b'wrong hello\n');pack()
    try:verify(parent,root,runtime,sha(parent),456)
    except AssertionError:count+=1
    else:raise AssertionError('wrong Hello admitted')
    assert count==5
    print('PASS: synthetic schema accepted; five invalid parent cases refused; no compiler executed')

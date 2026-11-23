"""Bounded actual-source formatter proof; no SSpec/core qualification claim."""
import hashlib, json, os, pathlib, shutil, subprocess
P=pathlib.Path
source=P('source').resolve(); out=source/'build/utf8-gap-proof'; out.mkdir(parents=True)
parent=P('intake/parent/linux-x86_64-p1/simple').resolve(); runtime=P('intake/runtime').resolve()
def sha(p):
    with p.open('rb') as f: return hashlib.file_digest(f,'sha256').hexdigest()
assert sha(parent)=='ed5e03685a3c9233395306f6fcb2c7c5fa9a6ada36fc1158c20e6d3be91fcf73'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()=='0e3119fe909a1692108d4d3d4e088b4712806c5f'
for n,h in {'libsimple_native_all.a':'7ceed2e9b0edbf719a6fb4422578d2e322e7ea33f71a9cf700fc8f16df2208ae','libsimple_compiler_backfill.a':'637d252e535f0773347af467335918133b2d83c52759eff64c33ac7932d2a41e'}.items(): assert sha(runtime/n)==h
parent.chmod(0o755)
fixture=out/'fixture.spl'; shutil.copyfile(P(__file__).with_suffix('.spl'),fixture)
owner=source/'src/compiler/80.driver/driver_worker_surface_graph_v1.spl'
inputs={str(p):sha(p) for p in [parent,owner,fixture,*runtime.glob('*.a')]}
(out/'inputs.json').write_text(json.dumps(inputs,indent=2))
env={k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')}
for n in ['cache','storage','tmp']: (out/n).mkdir()
env.update(SIMPLE_BINARY=str(parent),SIMPLE_PROJECT_ROOT=str(source),SIMPLE_LIB=str(source/'src'),SIMPLE_RUNTIME_PATH=str(runtime),SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_NATIVE_BUILD_RUST='0',SIMPLE_BOOTSTRAP_WHOLE_PROGRAM='1',SIMPLE_PARSE_SHARDING='0',SIMPLE_CACHE=str(out/'cache'),SIMPLE_NATIVE_BUILD_CACHE_DIR=str(out/'cache'),SIMPLE_USER_STORAGE_ROOT=str(out/'storage'),TMPDIR=str(out/'tmp'))
def owned(label,args,cap,seconds):
    cmd=['perl',str(source/'scripts/resource/process-tree-rss-watchdog.pl'),f'--max-rss-kib={cap}','--interval-ms=100',f'--timeout-seconds={seconds}',f'--receipt={out/(label+".env")}','--',*map(str,args)]
    (out/(label+'.argv.json')).write_text(json.dumps(cmd))
    with (out/(label+'.stdout')).open('wb') as stdout,(out/(label+'.stderr')).open('wb') as stderr:
        code=subprocess.run(cmd,cwd=source,env=env,stdout=stdout,stderr=stderr,timeout=seconds+30).returncode
    fields=dict(l.split('=',1) for l in (out/(label+'.env')).read_text().splitlines() if '=' in l)
    assert code==0 and fields['status']=='complete' and int(fields['rss_limit_kib'])==cap and fields['exit_status']=='0' and fields['quiescent']=='1' and fields['rss_cap_enforced']=='1',fields
exe=out/'formatter'
result={'status':'FAILED','qualification':'actual production native formatter only; SSpec/core checks unrun'}
try:
    owned('compile',[parent,'native-build','--backend','llvm','--threads','1','--entry-closure','--source','src/compiler','--source','src/lib','--entry',fixture,'--output',exe,'--cache-dir',out/'cache'],2097152,300)
    owned('run',[exe],262144,20)
    actual=(out/'run.stdout').read_bytes().decode('utf-8',errors='strict').splitlines()
    paths=['x'*511+'...[truncated]']*3+['x'*512,'x'*508+'😀','x'*508+'😀...[truncated]']
    expected=['blocking_target='+p+' reachable-gap=unbuilt-root source_index=0 target_index=0 inspected_edges=0 source= target=' for p in paths]
    assert actual==expected,{'actual':actual,'expected':expected}
    result.update(status='PASS',native_cases=6,binary_sha256=sha(exe),strict_utf8=True)
finally:
    result['inputs_unchanged']=inputs=={p:sha(P(p)) for p in inputs}
    (out/'result.json').write_text(json.dumps(result,indent=2))
assert result['inputs_unchanged']

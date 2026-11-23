"""Bounded paired real-owner fixture; no compiler or full CLI rebuild."""
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import time

SOURCE = 'ce231b5b898d797c98d44a9b59a4859a7d792a7b'
PARENT = 'ed5e03685a3c9233395306f6fcb2c7c5fa9a6ada36fc1158c20e6d3be91fcf73'
RUNTIME = {'libsimple_native_all.a':'7ceed2e9b0edbf719a6fb4422578d2e322e7ea33f71a9cf700fc8f16df2208ae',
           'libsimple_compiler_backfill.a':'637d252e535f0773347af467335918133b2d83c52759eff64c33ac7932d2a41e'}
OWNER = 'src/compiler/20.hir/hir_lowering/module_surface_selected_exports_v1.spl'

def sha(path):
    with path.open('rb') as stream: return hashlib.file_digest(stream,'sha256').hexdigest()

def main():
    source=Path('source').resolve()
    root=source/'build/freeze-owner-probe'
    root.mkdir(parents=True,exist_ok=False)
    parent=Path('intake/parent/linux-x86_64-p1/simple').resolve()
    runtime=Path('intake/runtime').resolve()
    assert sha(parent)==PARENT
    parent.chmod(0o755)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()==SOURCE
    subprocess.run(['git','diff','--exit-code','HEAD','--','src','config'],cwd=source,check=True)
    for name,digest in RUNTIME.items(): assert sha(runtime/name)==digest
    fixture=root/'fixture.spl'
    shutil.copyfile(Path(__file__).with_name('freeze-owner-fixture.spl'),fixture)
    owner=source/OWNER
    original=owner.read_bytes()
    before=original.decode()
    anchor='''    while changed:
        changed = false
        val prior_count = index.names.len()
        while bucketed_up_to < prior_count:
'''
    replacement='''    while changed:
        changed = false
        val prior_count = index.names.len()
        # Only newly appended rows can add a binding on an already visited edge.
        # Keep edge order and within-target row order, including the final round.
        var frontier_surface = 0
        while frontier_surface < surf_count:
            glob_head_by_surface[frontier_surface] = -1
            glob_tail_by_surface[frontier_surface] = -1
            frontier_surface = frontier_surface + 1
        while bucketed_up_to < prior_count:
'''
    assert before.count(anchor)==1
    after=before.replace(anchor,replacement)
    result={'status':'FAILED','source':SOURCE,'producer_sha256':PARENT,'runtime_sha256':RUNTIME,
            'runtime_source':'fd366d2a3068e9fc0d2ba7af0b915432d56b88c9',
            'producer_runtime_note':'only intervening runtime source diff is Windows timestamp weak-provider repair/test; actual native fixture execution required',
            'producer_reason':'real parser imports _AstExpr.nodes requiring repaired owner-generic semantic return producer',
            'owner_path':OWNER,'baseline_owner_sha256':hashlib.sha256(original).hexdigest(),
            'candidate_owner_sha256':hashlib.sha256(after.encode()).hexdigest(),
            'fixture_sha256':sha(fixture),'admission':'none',
            'scope':'real owner imported by native fixture; no full compiler/product build',
            'fixture_dimensions':{'semantic_cases':12,'chain_surfaces':128,'chain_glob_edges':127,
                                  'chain_seed_declarations':64,'expected_chain_bindings':8192},
            'representativeness':'synthetic measured fixture, not actual 7114-row export graph',
            'samples':[]}
    (root/'baseline-owner.spl').write_bytes(original)
    (root/'candidate-owner.spl').write_text(after)
    available=int(next(r.split()[1] for r in Path('/proc/meminfo').read_text().splitlines() if r.startswith('MemAvailable:')))
    cap=min(6*1024*1024,available*3//4)
    assert cap>=6*1024*1024
    env={k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')}
    env.update(SIMPLE_BINARY=str(parent),SIMPLE_PROJECT_ROOT=str(source),SIMPLE_LIB=str(source/'src'),
               SIMPLE_RUNTIME_PATH=str(runtime),SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_NATIVE_BUILD_RUST='0',
               SIMPLE_BOOTSTRAP_WHOLE_PROGRAM='1',SIMPLE_SCV_INVENTORY_COLD_INIT='1',
               SIMPLE_NATIVE_BUILD_THREADS='1',SIMPLE_PROCESS_TREE_RSS_DECLARED_JOBS='1',
               SIMPLE_KEEP_NATIVE_OBJS='1',CC='clang')

    def owned(name,argv,seconds,rss,child_env):
        cmd=['perl',str(source/'scripts/resource/process-tree-rss-watchdog.pl'),
             '--rss-cap-mode=enforce',f'--max-rss-kib={rss}',f'--timeout-seconds={seconds}',
             '--receipt='+str(root/(name+'.owner.env')),'--']+list(map(str,argv))
        (root/(name+'.argv.json')).write_text(json.dumps(cmd,indent=2))
        started=time.monotonic()
        with (root/(name+'.stdout')).open('wb') as out,(root/(name+'.stderr')).open('wb') as err:
            code=subprocess.run(cmd,cwd=source,env=child_env,stdout=out,stderr=err).returncode
        elapsed=time.monotonic()-started
        fields=dict(r.split('=',1) for r in (root/(name+'.owner.env')).read_text().splitlines() if '=' in r)
        assert code==0 and fields.get('status')=='complete' and fields.get('exit_status')=='0',name+': native owner failed'
        assert fields.get('quiescent')=='1' and fields.get('rss_cap_enforced')=='1'
        assert fields.get('rss_limit_kib')==str(rss)
        return {'elapsed_seconds':elapsed,'peak_rss_kib':int(fields['peak_rss_kib']),
                'stdout_sha256':sha(root/(name+'.stdout'))}

    try:
        for variant in ['baseline','candidate']:
            result['stage']='compile-'+variant
            if variant=='candidate': owner.write_text(after)
            lane=root/variant
            lane.mkdir()
            lane_env=env.copy()
            for sub in ['cache','storage','tmp','xdg']: (lane/sub).mkdir()
            lane_env.update(SIMPLE_CACHE=str(lane/'cache'),SIMPLE_NATIVE_BUILD_CACHE_DIR=str(lane/'cache'),
                            SIMPLE_CACHE_PROJECT='freeze-'+variant+'-'+result['candidate_owner_sha256'][:16],
                            SIMPLE_USER_STORAGE_ROOT=str(lane/'storage'),TMPDIR=str(lane/'tmp'),XDG_CACHE_HOME=str(lane/'xdg'))
            (lane/'environment.json').write_text(json.dumps({k:v for k,v in lane_env.items() if k.startswith('SIMPLE_')},indent=2))
            binary=lane/'fixture'
            argv=[parent,'native-build','--backend','llvm','--target','x86_64-unknown-linux-gnu',
                  '--runtime-path',runtime,'--runtime-bundle','core-c-bootstrap','--threads','1',
                  '--entry-closure','--mode','one-binary','--entry',fixture,'--output',binary,
                  '--cache-dir',lane/'cache','--low-memory',
                  '--source','src/compiler','--source','src/lib']
            result[variant+'_compile_metrics']=owned('compile-'+variant,argv,900,cap,lane_env)
            assert binary.is_file()
            result[variant+'_binary_sha256']=sha(binary)
        # One detailed semantic capture per immutable binary, separate from timing.
        detailed_reference=None
        for variant in ['baseline','candidate']:
            result['stage']='semantic-'+variant
            owned(result['stage'],[root/variant/'fixture'],90,1024*1024,env)
            data=(root/(result['stage']+'.stdout')).read_bytes()
            assert b'NATIVE-FREEZE-FIXTURE-PASS cases=12 chain_rows=8192\n' in data
            assert data.count(b'CASE ')==11 and data.count(b'ERROR missing|')==1
            if detailed_reference is None: detailed_reference=data
            assert data==detailed_reference,'full ordered rows/hops/diagnostics/digests differ'
        result['detailed_semantic_sha256']=hashlib.sha256(detailed_reference).hexdigest()
        compact_env=env.copy()
        compact_env['FREEZE_FIXTURE_COMPACT']='1'
        result['measurement_scope']='cold whole native fixture with compact authoritative digest output; includes parser and freeze; whole-process peak; not isolated freeze time'
        result['warm_measurement']='not measured'
        # Explicit finite interleaved measurement cohort, not repeated green test cycles.
        reference=None
        for sample in range(5):
            for variant in (['baseline','candidate'] if sample%2==0 else ['candidate','baseline']):
                result['stage']=f'run-{variant}-{sample}'
                binary=root/variant/'fixture'
                assert sha(binary)==result[variant+'_binary_sha256']
                measurement=owned(result['stage'],[binary],90,1024*1024,compact_env)
                data=(root/(result['stage']+'.stdout')).read_bytes()
                assert b'NATIVE-FREEZE-FIXTURE-PASS cases=12 chain_rows=8192\n' in data
                assert data.count(b'CASE ')==11 and data.count(b'ERROR missing|')==1
                if reference is None: reference=data
                assert data==reference,'ordered rows/hops/diagnostics/digests differ'
                measurement.update(variant=variant,sample=sample)
                result['samples'].append(measurement)
                (root/'result.json').write_text(json.dumps(result,indent=2))
        result['metrics']={}
        for variant in ['baseline','candidate']:
            samples=[r for r in result['samples'] if r['variant']==variant]
            elapsed=sorted(r['elapsed_seconds'] for r in samples)
            result['metrics'][variant]={'p50_seconds':statistics.median(elapsed),'p95_seconds':elapsed[math.ceil(.95*len(elapsed))-1],
                                        'peak_rss_kib':max(r['peak_rss_kib'] for r in samples)}
        result['status']='PASS'
    except Exception as error:
        result['error']=str(error)
    finally:
        owner.write_bytes(original)
        result['owner_restored']=sha(owner)==result['baseline_owner_sha256']
        result['parent_unchanged']=sha(parent)==PARENT
        (root/'result.json').write_text(json.dumps(result,indent=2))
    raise SystemExit(0 if result['status']=='PASS' else 1)

if __name__=='__main__': main()

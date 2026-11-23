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
import zipfile
from pathlib import PurePosixPath

SOURCE = 'ce231b5b898d797c98d44a9b59a4859a7d792a7b'
PARENT = 'ed5e03685a3c9233395306f6fcb2c7c5fa9a6ada36fc1158c20e6d3be91fcf73'
RUNTIME = {'libsimple_native_all.a':'7ceed2e9b0edbf719a6fb4422578d2e322e7ea33f71a9cf700fc8f16df2208ae',
           'libsimple_compiler_backfill.a':'637d252e535f0773347af467335918133b2d83c52759eff64c33ac7932d2a41e'}
OWNER = 'src/compiler/20.hir/hir_lowering/module_surface_selected_exports_v1.spl'
PRIOR_SHA = 'd11481bc11ff8a3d84386e56892739f3fedfcceb95f36f280bafdbb4b00caf19'
DEPENDENCY_FILES = ['module_surface_declarations.spl', 'module_surface_from_tldr_v1.spl',
                    'module_surface_manifest_evidence_v1.spl', 'module_surface_registry.spl',
                    'module_surface_source_identity.spl', 'module_surface_types.spl']

def sha(path):
    with path.open('rb') as stream: return hashlib.file_digest(stream,'sha256').hexdigest()

def restore_prior_cache(destination):
    """Restore immutable cache candidates; do not reuse an old verdict/queue."""
    archive=Path('intake/prior.zip')
    assert sha(archive)==PRIOR_SHA
    prefix='source/build/freeze-owner-probe/'
    with zipfile.ZipFile(archive) as z:
        names=set()
        folded=set()
        assert sum(i.file_size for i in z.infolist())<256*1024*1024
        for item in z.infolist():
            path=PurePosixPath(item.filename)
            canonical=path.as_posix()
            assert not path.is_absolute() and '..' not in path.parts
            assert canonical==item.filename.rstrip('/')
            assert not any(c in item.filename for c in ['\\',':','\0'])
            assert canonical not in names and canonical.casefold() not in folded
            names.add(canonical)
            folded.add(canonical.casefold())
            assert (item.external_attr>>16)&0o170000 != 0o120000
        result=json.loads(z.read(prefix+'result.json'))
        assert result['source']==SOURCE and result['producer_sha256']==PARENT
        assert result['runtime_sha256']==RUNTIME and result['stage']=='compile-baseline'
        assert result['status']=='FAILED' and result['samples']==[]
        assert result['owner_restored'] and result['parent_unchanged']
        receipt=dict(r.split('=',1) for r in z.read(prefix+'compile-baseline.owner.env').decode().splitlines() if '=' in r)
        assert receipt['status']=='rss-cap-exceeded' and receipt['exit_status']=='88'
        assert receipt['quiescent']=='1' and receipt['rss_cap_enforced']=='1'
        assert receipt['rss_limit_kib']=='6291456'
        copied=[]
        for item in z.infolist():
            cache_prefix=prefix+'baseline/cache/'
            if not item.filename.startswith(cache_prefix) or item.is_dir(): continue
            relative=PurePosixPath(item.filename[len(cache_prefix):])
            if any(part.startswith(('queue-','mir-queue-')) for part in relative.parts): continue
            data=z.read(item)
            target=destination/str(relative)
            target.parent.mkdir(parents=True,exist_ok=True)
            assert not target.exists()
            target.write_bytes(data)
            digest=hashlib.sha256(data).hexdigest()
            assert sha(target)==digest
            copied.append({'path':str(relative),'sha256':digest,'bytes':len(data)})
        return {'prior_run':45271594927,'prior_artifact':14866627876,
                'archive_sha256':PRIOR_SHA,'copied_candidates':copied,
                'reuse_status':'candidates only; normal source/producer/cache checks decide'}

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

    dependency_originals={}
    try:
        # The facade already exports this exact physical declaration. Only its
        # unrelated BackendCompileOptions dependency is removed; no type is copied.
        facade=(source/'src/compiler/00.common/driver_core_types.spl').read_text()
        assert 'pub use compiler.common.driver_source_file.{' in facade
        declaration=source/'src/compiler/00.common/driver_source_file.spl'
        assert 'struct SourceFile:' in declaration.read_text()
        result['sourcefile_declaration_sha256']=sha(declaration)
        result['dependency_overlay']=[]
        for filename in DEPENDENCY_FILES:
            path=source/'src/compiler/20.hir/hir_lowering'/filename
            data=path.read_bytes()
            dependency_originals[path]=data
            text=data.decode()
            old='use compiler.common.driver_core_types.{SourceFile}'
            new='use compiler.common.driver_source_file.{SourceFile}'
            assert text.count(old)==1
            changed=text.replace(old,new)
            path.write_text(changed)
            result['dependency_overlay'].append({'path':str(path.relative_to(source)),
                'baseline_sha256':hashlib.sha256(data).hexdigest(),'fixture_owner_sha256':sha(path)})
        result['dependency_scope']='same six SourceFile-only physical-owner imports in both variants; freeze/selection baseline algorithm unchanged'
        result['prior_closure_modules']=503
        for variant in ['baseline','candidate']:
            result['stage']='compile-'+variant
            if variant=='candidate': owner.write_text(after)
            lane=root/variant
            lane.mkdir()
            lane_env=env.copy()
            for sub in ['cache','storage','tmp','xdg']: (lane/sub).mkdir()
            cache_intake=restore_prior_cache(lane/'cache')
            (lane/'cache-intake.json').write_text(json.dumps(cache_intake,indent=2))
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
            log=(root/('compile-'+variant+'.stdout')).read_text(errors='replace')
            import re
            source_trace=log+(root/('compile-'+variant+'.stderr')).read_text(errors='replace')
            snapshot_bindings=[]
            for filename in DEPENDENCY_FILES+[Path(OWNER).name]:
                # Retain actual source-view read paths, not just the mutable
                # checkout hash; a stale snapshot must fail the A/B intake.
                pattern=r'(/[^\s\"\']*/build/scv/snapshots/scv-revision-v2-[0-9a-f]+/src/compiler/20\.hir/hir_lowering/'+re.escape(filename)+r')'
                paths=sorted(set(re.findall(pattern,source_trace)))
                if not paths:
                    assert filename not in [Path(OWNER).name,'module_surface_types.spl','module_surface_registry.spl'], 'missing required actual source-view read trace: '+filename
                    snapshot_bindings.append({'filename':filename,'status':'not present in observed source-view reads'})
                    continue
                expected=sha(source/'src/compiler/20.hir/hir_lowering'/filename)
                for path in paths:
                    assert sha(Path(path))==expected, 'stale source-view owner: '+path
                    retained=lane/'source-views'/filename
                    retained.parent.mkdir(exist_ok=True)
                    shutil.copyfile(path,retained)
                    assert sha(retained)==expected
                    snapshot_bindings.append({'path':path,'sha256':expected,'retained':str(retained.relative_to(root))})
            result[variant+'_actual_source_views']=snapshot_bindings
            closure_counts=sorted({int(x) for x in re.findall(r'phase=hir state=running unit_kind=modules done=\d+ total=(\d+)',log)})
            result[variant+'_closure_modules']=closure_counts
            result[variant+'_generated_hir_codec_seen']='current=compiler.hir.generated.hir_codec' in log
            assert len(closure_counts)==1, 'missing or inconsistent actual HIR closure count'
            assert closure_counts[0]<503 and not result[variant+'_generated_hir_codec_seen'], 'dependency reduction not established'
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
        for path,data in dependency_originals.items(): path.write_bytes(data)
        result['dependency_owners_restored']=all(path.read_bytes()==data for path,data in dependency_originals.items())
        # Capture closure progress even if compilation or a later gate fails.
        import re
        for variant in ['baseline','candidate']:
            log_path=root/('compile-'+variant+'.stdout')
            if log_path.exists():
                log=log_path.read_text(errors='replace')
                result[variant+'_closure_modules']=sorted({int(x) for x in re.findall(r'phase=hir state=running unit_kind=modules done=\d+ total=(\d+)',log)})
                result[variant+'_generated_hir_codec_seen']='current=compiler.hir.generated.hir_codec' in log
        result['owner_restored']=sha(owner)==result['baseline_owner_sha256']
        result['parent_unchanged']=sha(parent)==PARENT
        (root/'result.json').write_text(json.dumps(result,indent=2))
    raise SystemExit(0 if result['status']=='PASS' else 1)

if __name__=='__main__': main()

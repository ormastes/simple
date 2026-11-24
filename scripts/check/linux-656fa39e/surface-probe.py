"""One small source-project attribution probe; no bootstrap/product rebuild."""
import hashlib,importlib.util,json,os,pathlib,subprocess,sys
P=pathlib.Path;HERE=P(__file__).resolve().parent;ROOT=P.cwd();OUT=ROOT/'probe-evidence'
OUT.mkdir(exist_ok=False)
s=importlib.util.spec_from_file_location('control',HERE/'control.py');c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
def run(argv,**kw):return subprocess.run(list(map(str,argv)),check=True,timeout=kw.pop('timeout',60),**kw)
def main():
 # Existing verified projection revalidates prior bytes and native Hello;
 # it executes no compiler. No previously green smoke is repeated.
 run([sys.executable,HERE/'recover-qualified.py','--output',OUT/'parent'],timeout=900)
 parent=json.loads((OUT/'parent/parent.json').read_text());binary=OUT/'parent/parent/simple_stage2';runtime=OUT/'parent/runtime'
 assert parent['parent_sha256']=='21ab99e0cb58fe6dd806db1d43ff8be45c1112f0da372ee4c2f6e95c92d798bf'
 binary.chmod(0o755)
 project=ROOT/'probe-project';project.mkdir()
 bodies={}
 for i in range(16):bodies[f'src/lib/common/probe_{i:02d}.spl']=f'pub fn value_{i:02d}() -> i64:\n    {i}\nexport value_{i:02d}\n'
 bodies['src/lib/common/probe_facade.spl']=''.join(f'export probe_{i:02d}.*\n' for i in range(16))
 bodies['src/lib/common/probe_chain.spl']='export probe_facade.*\n'
 bodies['src/main.spl']='use lib.common.probe_chain.{'+', '.join(f'value_{i:02d}' for i in range(16))+'}\nfn main() -> i64:\n    '+ ' + '.join(f'value_{i:02d}()' for i in range(16))+'\n'
 for name,body in bodies.items():
  p=project/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(body)
 run(['git','init','-q',project]);run(['git','-C',project,'add','src'])
 run(['git','-C',project,'-c','user.name=Fixture evidence','-c','user.email=fixture@example.invalid','commit','-qm','Isolated surface attribution fixture'])
 fixture={name:c.sha(project/name) for name in bodies}
 c.save(OUT/'fixture.json',{'files':fixture,'physical_files':19,'leaf_functions':16,'configured_glob_routes':17,'shape':'16 named function providers, one glob facade and one transitive glob facade, named consumer imports','project_commit':subprocess.check_output(['git','-C',str(project),'rev-parse','HEAD'],text=True).strip(),'scope':'measured synthetic dimensions, not reconstruction of the original7124-row graph'})
 c.tools_snapshot(OUT)
 for name in ('gdb','python3'):
  with (OUT/(name+'.version')).open('wb') as f:run([name,'--version'],stdout=f)
 nm=subprocess.check_output(['llvm-nm','--defined-only',str(binary)],timeout=60).decode()
 required=['compiler__hir__hir_lowering__module_surface_registry__ModuleSurfaceBuilder_dot_finish_into','compiler__hir__hir_lowering__module_surface_registry_index__module_surfaces_freeze','compiler__hir__hir_lowering__module_surface_registry__module_surfaces_promote_reason','compiler__driver__driver_source_parse_streaming__CompilerDriver_dot_parse_all_streaming_surfaces_in_place_impl','compiler__driver__driver_log_helpers__log_module_surface_released','rt_array_copy']
 assert all(any(line.endswith(' '+name) for line in nm.splitlines()) for name in required)
 c.save(OUT/'symbols.json',{'binary_sha256':c.sha(binary),'required':required})
 available=int(next(x.split()[1] for x in P('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
 cap=6*1024*1024;assert cap<=available*3//4 and available-cap>=2*1024*1024
 c.save(OUT/'resource.json',{'available_kib':available,'cap_kib':cap,'minimum_reserve_kib':2097152,'timeout_seconds':300,'scope':'fixture ceiling, unchanged compiler worker estimates'})
 cache=OUT/'cache';cache.mkdir();config={'binary_sha256':c.sha(binary),'fixture_files':fixture,'cache':str(cache),'events':str(OUT/'boundaries.jsonl')}
 c.save(OUT/'observer-config.json',config)
 env={k:v for k,v in os.environ.items() if not k.startswith('SIMPLE_')}
 env.update(SURFACE_OBSERVER_CONFIG=str(OUT/'observer-config.json'),SIMPLE_BINARY=str(binary),SIMPLE_PROJECT_ROOT=str(project),SIMPLE_LIB=str(project/'src'),SIMPLE_RUNTIME_PATH=str(runtime),SIMPLE_NO_STUB_FALLBACK='1',SIMPLE_NATIVE_BUILD_RUST='0',SIMPLE_FILE_WORKERS='1',SIMPLE_FILE_WORKER_SINGLE_LOW_MEMORY='1',SIMPLE_FILE_WORKER_BATCH='4',SIMPLE_PARSE_SHARDING='1',SIMPLE_SCV_INVENTORY_COLD_INIT='1',SIMPLE_CACHE=str(cache),SIMPLE_NATIVE_BUILD_CACHE_DIR=str(cache),SIMPLE_FRONTEND_CACHE_DIR=str(cache/'frontend'),SIMPLE_HIR_CACHE_DIR=str(cache/'hir'),SIMPLE_USER_STORAGE_ROOT=str(OUT/'storage'),TMPDIR=str(OUT/'tmp'),CC='clang')
 for name in ('tmp','storage'):(OUT/name).mkdir()
 for key in ('SIMPLE_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB','SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB'):env[key]=str(cap)
 compile=[str(binary),'native-build','--backend','llvm','--target','x86_64-unknown-linux-gnu','--runtime-path',str(runtime),'--runtime-bundle','core-c-bootstrap','--threads','1','--profile=prod','--release','--strip','--managed-build-phase=phase4','--opt-level=standard','--low-memory','--source','src','--entry-closure','--entry','src/main.spl','--mode','dynload','--cache-dir',str(cache),'--output',str(OUT/'unqualified-product')]
 debugger=['gdb','-q','-batch','-ex','set pagination off','-ex','set confirm off','-ex','set disable-randomization off','-ex','source '+str(HERE/'surface-observer.py'),'--args']+compile
 owner=['perl',str(ROOT/'source/scripts/resource/process-tree-rss-watchdog.pl'),'--rss-cap-mode=enforce','--max-rss-kib='+str(cap),'--timeout-seconds=300','--receipt='+str(OUT/'owner.env'),'--']+debugger
 c.save(OUT/'argv.json',owner)
 with (OUT/'stdout.log').open('wb') as stdout,(OUT/'stderr.log').open('wb') as stderr:
  with c.cleanup.acquired_owner(owner,OUT/'cleanup.json',cwd=project,env=env,stdout=stdout,stderr=stderr) as p:code=p.wait(timeout=420)
 receipt=dict(x.split('=',1) for x in (OUT/'owner.env').read_text().splitlines() if '=' in x)
 events=[json.loads(x) for x in (OUT/'boundaries.jsonl').read_text().splitlines()] if (OUT/'boundaries.jsonl').exists() else []
 c.save(OUT/'terminal.json',{'status':'UNQUALIFIED_DIAGNOSTIC','exit':code,'owner':receipt,'events':events,'scope':'partial evidence retained; no product claim'})
 assert code==0 and receipt['status']=='complete' and receipt['exit_status']=='0' and receipt['quiescent']==receipt['rss_cap_enforced']=='1' and int(receipt['rss_limit_kib'])==cap
 expected=['streaming:entry','last-release:return','unit-identity','finish:entry','freeze:entry','freeze:return','finish:return','promote:entry','promote:return','copy-summary','observer-stop']
 assert [e['stage'] for e in events]==expected,[e['stage'] for e in events]
 assert len({e['pid'] for e in events})==1 and events[-1]['code']==0
 assert c.sha(binary)==parent['parent_sha256'] and all(c.sha(project/n)==h for n,h in fixture.items())
 assert all(c.sha(runtime/n)==h for n,h in parent['runtime_files'].items())
 c.save(OUT/'terminal.json',{'status':'ATTRIBUTION_CAPTURED','owner':receipt,'events':events,'source':c.SOURCE,'producer_sha256':c.sha(binary),'fixture_files':fixture,'scope':'intentional stop after promotion function return, success result not inspected; fixture worker boundary RSS and separate whole-owner peak, not simultaneous tree boundary RSS; instrumented call counts include debugger overhead; no compiler/product PASS or original fullCLI attribution'})
if __name__=='__main__':
 try:main()
 except BaseException as error:
  c.save(OUT/'failure.json',{'error':str(error),'type':type(error).__name__,'scope':'no retry and no product qualification'});raise

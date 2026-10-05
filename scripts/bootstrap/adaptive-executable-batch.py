"""Run only below the canonical20-job owner and Windows CFEC collector."""
import argparse,datetime,hashlib,json,os,pathlib,subprocess,sys,time
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent/"lib"))
from executable_batch_policy import available_commit_bytes,may_start,closed_rss,outcome,identity,reusable_success,preflight_invocation,request_environment,validate_owned_ancestry
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--packet',required=True,type=pathlib.Path)
parser.add_argument('--preflight',action='store_true')
args=parser.parse_args()
D=args.packet.resolve()
CONFIG=json.loads((D/'config.json').read_text())
TARGETS=json.loads((D/'tasks.json').read_text())['targets']

def sha(p):
 with pathlib.Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def load(p):return json.loads(pathlib.Path(p).read_text(encoding='utf-8-sig'))
def env(p):return dict(x.split('=',1) for x in pathlib.Path(p).read_text().splitlines())
def write(p,v):
 tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(v,indent=2)+'\n');tmp.replace(p)
def check_request(t):
 q=pathlib.Path(t['request']);assert sha(q)==t['request_sha256'],'Child request changed';r=load(q)
 assert r['threads']==1
 for leaf,h in r['files'].items():
  assert pathlib.Path(leaf).name==leaf and sha(q.parent/leaf)==h,'Child input changed'
 return r

def preflight():
 assert TARGETS, 'Empty target manifest is not executable'
 assert CONFIG['aggregate_jobs']==20 and 1<=CONFIG['max_executables']<=20
 assert len({t['packet'] for t in TARGETS})==len(TARGETS)
 assert all(t['options']==dict(threads=1,hir_sharding=0,parse_sharding=0,streaming_surfaces=1) for t in TARGETS)
 for t in TARGETS:check_request(t)
 # The first target's shared producer/source/Hello authority preflight covers common pins.
 # Each child repeats its own full authority check immediately before execution.
 first=check_request(TARGETS[0]);command,cwd,environment=preflight_invocation(first,os.environ)
 subprocess.run(command,cwd=cwd,env=environment,check=True)
if args.preflight:
 preflight();print('batch preflight passed');raise SystemExit(0)
preflight()
launch=load(CONFIG['owner_launch_receipt'])
reservation=load(launch['reservation'])
observer=CONFIG['process_observer']
assert sha(observer['path'])==observer['sha256'], 'Process observer changed'
observed=subprocess.check_output([CONFIG['powershell'], '-NoProfile', '-NonInteractive', '-File', observer['path'], '-BatchProcessId', str(os.getpid()), '-OwnerProcessId', str(launch['owner_pid'])],text=True)
rows=json.loads(observed)
validate_owned_ancestry(CONFIG,launch,reservation,load(launch['request']),rows,os.getpid(),pathlib.Path(__file__).resolve(),D,sha)
assert not (D/'batch-state.json').exists(),'Fresh parent run required; explicit closed-receipt resume only'
state=dict(state='RUNNING',aggregate_jobs=20,max_executables=CONFIG['max_executables'],rows=[],current=[],observed_task_peak_bytes=[],scope='compile+link tasks; not isolated linker measurements',no_kill_on_memory_pressure=True)
pending=list(TARGETS);running={};observations=[];blocked=False

def publish():
 state['current']=[dict(pid=pid,entry=v['target']['entry'],backend=v['target']['backend']) for pid,v in running.items()]
 state['observed_task_peak_bytes']=observations;state['pending']=len(pending);write(D/'batch-state.json',state)
while pending or running:
 for pid,item in list(running.items()):
  process=item['process'];code=process.poll()
  if code is None:continue
  item['stdout'].close();item['stderr'].close();t=item['target'];packet=pathlib.Path(t['packet']);result=load(packet/'results.json') if (packet/'results.json').exists() else None
  receipts=[]
  if (packet/'artifact/compile.rss.env').exists():receipts.append(env(packet/'artifact/compile.rss.env'))
  if result and result.get('sanity_exit') is not None:
   if (packet/'artifact/run.rss.env').exists():receipts.append(env(packet/'artifact/run.rss.env'))
   else:receipts.append({})
  verdict=outcome(code,result,receipts)
  row=dict(entry=t['entry'],backend=t['backend'],identity=identity(t),packet=str(packet),child_exit=code,closure='CLOSED' if verdict=='CONTINUE' else 'UNVERIFIED',result=result)
  if result:row.update({key:result.get(key) for key in ('binary_linked','binary_sha256','sanity_pass')})
  state['rows'].append(row);del running[pid]
  if verdict!='CONTINUE':blocked=True;state['state']='BLOCKED_CHILD_CLOSURE_DRAINING'
  elif receipts:
   observed=max(int(r.get('peak_rss_kib','0'))*1024 for r in receipts)
   if observed>0:observations.append(observed)
   # Shell releases only its own lease after quiescent receipt validation.
   if pathlib.Path(t['cache_lease']).exists():blocked=True;state['state']='BLOCKED_RETAINED_CACHE_LEASE'
  publish()
 if blocked:
  if not running:break
  time.sleep(2);continue
 free=available_commit_bytes();state['available_commit_bytes']=free
 while pending and may_start(len(running),observations,free,CONFIG):
  index=next((i for i,t in enumerate(pending) if not pathlib.Path(t['cache_lease']).exists()),None)
  if index is None:state['state']='WAITING_CACHE_LEASE';break
  t=pending.pop(index);packet=pathlib.Path(t['packet']);request=check_request(t)
  prior=t.get('reuse_success')
  if prior:
   proof=pathlib.Path(prior['receipt']);assert sha(proof)==prior['receipt_sha256'];saved=load(proof);binary=pathlib.Path(prior['binary'])
   if binary.is_file() and reusable_success(saved,t,sha(binary)):
    state['rows'].append(dict(entry=t['entry'],backend=t['backend'],status='SKIPPED_EXACT_VERIFIED_SUCCESS',identity=identity(t)));publish();continue
  assert not (packet/'artifact').exists(),'Fresh output required; cache lives separately'
  out=(packet/'task.stdout.log').open('xb');err=(packet/'task.stderr.log').open('xb')
  # One parent CFEC Job contains these children and all nested native/RSS helpers.
  process=subprocess.Popen(request['command'],cwd=request['cwd'],env=request_environment(request,os.environ),stdout=out,stderr=err,creationflags=subprocess.CREATE_NO_WINDOW)
  running[process.pid]=dict(process=process,target=t,stdout=out,stderr=err)
  write(packet/'child-start.json',dict(pid=process.pid,parent_batch_pid=__import__('os').getpid(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),requested_jobs=1,aggregate_reservation_jobs=20))
  state['state']='RUNNING';publish();free=available_commit_bytes()
 if not running and pending:state['state']='WAITING_MEMORY_OR_CACHE';publish()
 if running or pending:time.sleep(2)
state['state']='BLOCKED_UNVERIFIED_CLOSURE' if blocked else 'COMPLETE_PER_TARGET_RESULTS';publish()
raise SystemExit(1 if blocked else 0)

"""Read-only GDB boundary observer for one small, ordinary source project.

Reuses the proven follow-fork/exec topology. No inferior function is evaluated.
The intentional stop after promotion is not compiler/product success.
"""
import gdb,hashlib,json,os,time
from pathlib import Path
cfg=json.loads(Path(os.environ['SURFACE_OBSERVER_CONFIG']).read_text())
target=0;active=False;freeze=False;freeze_thread=None;released=0
copy_calls=0;other_thread_calls=0;sites={};identities={}
def stop(code,reason):
 emit('observer-stop',reason=reason,code=code)
 ids=[str(i.num) for i in gdb.inferiors() if i.pid]
 if ids:gdb.execute('kill inferiors '+' '.join(ids))
 gdb.execute('quit '+str(code))
def identity():
 pid=gdb.selected_inferior().pid
 if not pid:return False
 if pid in identities:return identities[pid]
 argv=Path(f'/proc/{pid}/cmdline').read_bytes().decode().split('\0')[:-1]
 if 'src/app/cli/native_build_worker.spl' not in argv or not any(x.startswith('--hir-shard=') for x in argv):return False
 with Path(f'/proc/{pid}/exe').open('rb') as f:valid=hashlib.file_digest(f,'sha256').hexdigest()==cfg['binary_sha256']
 identities[pid]=valid
 return valid
def emit(stage,**extra):
 pid=gdb.selected_inferior().pid
 rss=None
 if pid:
  status=Path(f'/proc/{pid}/status').read_text();rss=int(next(x.split()[1] for x in status.splitlines() if x.startswith('VmRSS:')))
 row={'stage':stage,'monotonic':time.monotonic(),'pid':pid,'thread':gdb.selected_thread().ptid if gdb.selected_thread() else None,'worker_rss_kib':rss,'active':active,'copy_calls':copy_calls,**extra}
 with Path(cfg['events']).open('a') as f:f.write(json.dumps(row)+'\n');f.flush();os.fsync(f.fileno())
def validate_picks():
 queues=list(Path(cfg['cache']).glob('hir/queue-*'));assert len(queues)==1,queues
 picks=[p.read_text().strip() for p in (queues[0]/'owner_picks').rglob('*.pick')]
 assert len(picks)==len(set(picks))==4,picks
 observed=[]
 for name in picks:
  p=Path(name);relative='src/'+name.split('/src/',1)[1]
  assert relative in cfg['fixture_files'] and hashlib.sha256(p.read_bytes()).hexdigest()==cfg['fixture_files'][relative]
  observed.append(relative)
 index=(queues[0]/'unit_order.idx').read_text().splitlines()[0]
 emit('unit-identity',picks=sorted(observed),unit_index_header=index,argv=Path(f'/proc/{target}/cmdline').read_bytes().decode().split('\0')[:-1])
class Return(gdb.FinishBreakpoint):
 def __init__(self,stage):super().__init__(gdb.newest_frame(),internal=True);self.stage=stage
 def stop(self):
  global freeze
  if gdb.selected_inferior().pid!=target:return False
  emit(self.stage+':return')
  if self.stage=='freeze':freeze=False;copies.enabled=False
  if self.stage=='promote':
   emit('copy-summary',call_sites=sites,other_thread_calls=other_thread_calls,scope='actual function entries during freeze; not copied bytes or allocator ownership')
   stop(0,'intentional stop after promotion function returned; success result not inspected; no product compilation claim')
  return False
class Boundary(gdb.Breakpoint):
 def __init__(self,symbol,stage):super().__init__(symbol,internal=True);self.stage=stage
 def stop(self):
  global target,active,freeze,freeze_thread
  if not identity():return False
  pid=gdb.selected_inferior().pid
  if self.stage=='streaming':
   if target and target!=pid:stop(2,'more than one worker at observed boundary')
   target=pid;emit('streaming:entry');return False
  if pid!=target:return False
  if self.stage=='finish':
   validate_picks();assert released==len(cfg['fixture_files']),(released,len(cfg['fixture_files']))
   active=True
  if not active:return False
  if self.stage=='freeze':
   assert not freeze,'recursive freeze is outside this observer scope'
   freeze=True;freeze_thread=gdb.selected_thread().ptid;copies.enabled=True
  emit(self.stage+':entry');Return(self.stage);return False
class Released(gdb.Breakpoint):
 def stop(self):
  global released
  if gdb.selected_inferior().pid==target:
   released+=1
   if released==len(cfg['fixture_files']):Return('last-release')
  return False
class Copies(gdb.Breakpoint):
 def stop(self):
  global copy_calls,other_thread_calls
  if gdb.selected_inferior().pid!=target or not freeze:return False
  if gdb.selected_thread().ptid!=freeze_thread:other_thread_calls+=1;return False
  copy_calls+=1
  if copy_calls>50000:stop(3,'finite copy-counter event budget exceeded')
  caller=gdb.newest_frame().older();key=(caller.name() or '<unknown>')+'@'+hex(caller.pc())
  sites[key]=sites.get(key,0)+1
  if len(sites)>256:stop(3,'finite copy-counter callsite budget exceeded')
  return False
def fail_closed(method):
 def wrapped(self):
  try:return method(self)
  except BaseException as error:stop(2,'observer validation failed: '+str(error))
 return wrapped
for cls in (Return,Boundary,Released,Copies):cls.stop=fail_closed(cls.stop)
gdb.execute('set follow-fork-mode child');gdb.execute('set detach-on-fork off')
gdb.execute('set schedule-multiple on');gdb.execute('set breakpoint pending on');gdb.execute('set startup-with-shell off')
copies=Copies('rt_array_copy',internal=True);copies.enabled=False
Released('compiler__driver__driver_log_helpers__log_module_surface_released',internal=True)
Boundary('compiler__driver__driver_source_parse_streaming__CompilerDriver_dot_parse_all_streaming_surfaces_in_place_impl','streaming')
Boundary('compiler__hir__hir_lowering__module_surface_registry__ModuleSurfaceBuilder_dot_finish_into','finish')
Boundary('compiler__hir__hir_lowering__module_surface_registry_index__module_surfaces_freeze','freeze')
Boundary('compiler__hir__hir_lowering__module_surface_registry__module_surfaces_promote_reason','promote')
gdb.execute('run')
while any(i.pid for i in gdb.inferiors()):
 if not gdb.selected_inferior().pid:gdb.execute('inferior '+str(next(i.num for i in gdb.inferiors() if i.pid)))
 gdb.execute('continue')

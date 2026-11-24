"""Cleanup an acquired governed owner on controller exceptions; no success synthesis."""
from contextlib import contextmanager
from pathlib import Path
import json,os,signal,subprocess,time

def descendants(pid):
 result=[]
 try: children=Path(f'/proc/{pid}/task/{pid}/children').read_text().split()
 except OSError:return result
 for value in children:
  child=int(value);result.extend(descendants(child));result.append(child)
 return result

def identity(pid):
 try:return Path(f'/proc/{pid}/stat').read_text().split(') ',1)[1].split()[19]
 except OSError:return None

@contextmanager
def acquired_owner(argv,cleanup_path,**kwargs):
 child=subprocess.Popen(argv,start_new_session=True,**kwargs)
 def interrupted(signum,frame):raise InterruptedError('controller interrupted')
 previous=signal.signal(signal.SIGTERM,interrupted)
 try:yield child
 finally:
  signal.signal(signal.SIGTERM,previous)
  if child.poll() is None:
   tracked={p:identity(p) for p in descendants(child.pid)}
   child.terminate()
   forced=False
   try:child.wait(timeout=45)
   except subprocess.TimeoutExpired:
    forced=True
    tracked.update({p:identity(p) for p in descendants(child.pid)})
    for pid,start in tracked.items():
     if start is None or identity(pid)!=start:continue
     try:os.kill(pid,signal.SIGKILL)
     except ProcessLookupError:pass
    child.kill();child.wait(timeout=10)
   Path(cleanup_path).write_text(json.dumps({'controller_exception_cleanup':True,'forced':forced,
    'owner_exit':child.returncode,'observed_descendants':tracked,
    'remaining_observed_pids':[p for p in tracked if Path(f'/proc/{p}').exists()]},indent=2))

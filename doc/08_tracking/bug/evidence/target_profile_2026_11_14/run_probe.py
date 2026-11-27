from pathlib import Path
import os, signal, subprocess, sys, time, hashlib
root=Path(__file__).resolve().parent
producer=Path('/home/yoon/dev/simple-jit-free-s1-20261114/build/bootstrap/pinned-src/pinned-33bc5c6d1d80/build/bootstrap-jitfree-s1/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple')
case=sys.argv[1]; d=root/case
for cmd in [['git','init','-q'], ['git','add','src/main.spl','provenance.sdn'], ['git','-c','user.name=Probe','-c','user.email=probe@localhost','commit','-qm','Actual production Value get_type projection']]:
 subprocess.run(cmd,cwd=d,check=True)
cmd=[str(producer),'native-build','--source','src','--entry','src/main.spl','--entry-closure','--cache-dir',str(d/'cache'),'--runtime-bundle','core-c','--threads','1','-o',str(d/'probe')]
start=time.monotonic(); peak=0; stopped='none'
with (d/'build.log').open('w') as log:
 probe_env=dict(os.environ, XDG_CACHE_HOME=str(d/'xdg-cache'))
 p=subprocess.Popen(cmd,cwd=d,env=probe_env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  rss=0
  for f in Path('/proc').glob('[0-9]*/stat'):
   try:
    fields=f.read_text().split(') ',1)[1].split()
    if int(fields[2])==p.pid:rss+=int(fields[21])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,ValueError,IndexError):pass
  peak=max(peak,rss)
  if rss>2*1024**3 or time.monotonic()-start>120:
   stopped='tree_rss' if rss>2*1024**3 else 'timeout'
   os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=3)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
   break
  time.sleep(0.2)
 p.wait()
receipt=f'producer_sha256: "{hashlib.sha256(producer.read_bytes()).hexdigest()}"\nexit_code: {p.returncode}\nelapsed_seconds: {time.monotonic()-start:.3f}\npeak_tree_rss_bytes: {peak}\nstop_reason: {stopped}\ncommand: "'+ ' '.join(cmd)+'"\n'
(d/'receipt.sdn').write_text(receipt)
print(receipt)
print('\n'.join((d/'build.log').read_text().splitlines()[-12:]))
if p.returncode==0:
 result=subprocess.run([str(d/'probe')],cwd=d,capture_output=True,text=True,timeout=10)
 (d/'run.log').write_text(result.stdout+result.stderr+f'EXIT {result.returncode}\n')
 print((d/'run.log').read_text())

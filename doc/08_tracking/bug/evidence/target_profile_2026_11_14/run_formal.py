from pathlib import Path
import os,signal,subprocess,time
repo=Path.cwd()
d=repo/"build/target-profile"
cmd=["sh",str(d/"formal-stages1-3.sh")]
start=time.monotonic(); peak=0; stopped='none'
with (d/'formal-gate.log').open('w') as log:
 probe_env=dict(os.environ, PATH='/tmp/simple-toolchains/lean-4.30.0-linux_aarch64/bin:'+os.environ['PATH'])
 p=subprocess.Popen(cmd,cwd=repo,env=probe_env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
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

receipt=f'exit_code: {p.returncode}\nelapsed_seconds: {time.monotonic()-start:.3f}\npeak_tree_rss_bytes: {peak}\nstop_reason: {stopped}\n'
(d/'formal-gate-receipt.sdn').write_text(receipt)
print(receipt)
print('\n'.join((d/'formal-gate.log').read_text().splitlines()[-15:]))
raise SystemExit(p.returncode)

"""Source-only fixture runner; no compile/build. Receipt is fail-closed."""
import argparse,subprocess,threading,queue,json,hashlib,os
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--basic',required=True);p.add_argument('--controlled');p.add_argument('--descriptor');p.add_argument('--out',required=True);a=p.parse_args();out=Path(a.out);out.mkdir(exist_ok=False)
raw=bytes.fromhex('4100c3a90a0d0a5a');rows=[];status='INCOMPLETE';active=None;failure=None
expected_count=9 if os.name=='nt' else 3
if os.name=='nt':expected_count+=1

def start(name):
 global active
 active={'name':name,'passed':False,'status':'INCOMPLETE'};rows.append(active);return active

def case(exe,name,expected):
 row=start(name)
 try:r=subprocess.run([exe,name],cwd=out,capture_output=True,timeout=10,creationflags=subprocess.CREATE_NO_WINDOW if os.name=='nt' and name=='unattached' else 0)
 except subprocess.TimeoutExpired as e:row.update(status='FAIL',reason='timeout',stdout_hex=(e.stdout or b'').hex(),stderr_hex=(e.stderr or b'').hex());raise
 (out/(name+'.stdout')).write_bytes(r.stdout);(out/(name+'.stderr')).write_bytes(r.stderr)
 row.update(exit=r.returncode,stdout_hex=r.stdout.hex(),stderr_hex=r.stderr.hex())
 assert r.returncode==0 and not r.stderr and r.stdout==expected,name
 row.update(passed=True,status='PASS')
try:
 for name,expected in [('raw',raw),('mixed',b'queued:'+raw+b'tail'),('redirect',b'')]:case(a.basic,name,expected)
 assert (out/'redirected.bin').read_bytes()==raw,'FILE redirection must use actual FILE handle'
 if os.name=='nt':
  assert a.controlled and a.descriptor,'Windows controlled and unattached descriptor owners are required'
  for name,expected in [('short',raw),('zero',b''),('error',b''),('partial-error',raw[:2])]:case(a.controlled,name,expected)
  row=start('held');child=subprocess.Popen([a.controlled,'held'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=out);q=queue.Queue()
  threading.Thread(target=lambda:q.put(child.stdout.read(len(raw))),daemon=True).start()
  try:
   before_exit=q.get(timeout=5);row['bytes_observed_before_exit_hex']=before_exit.hex();row['alive_before_release']=child.poll() is None
   assert before_exit==raw and child.poll() is None,'implicit process-exit flush cannot qualify'
   child.stdin.write(b'!');child.stdin.flush();stdout,stderr=child.communicate(timeout=5)
   row.update(exit=child.returncode,stdout_hex=stdout.hex(),stderr_hex=stderr.hex())
   assert child.returncode==0 and stdout==b'' and stderr==b''
   row.update(passed=True,status='PASS')
  finally:
   if child.poll() is None:child.kill();child.communicate(timeout=5)
  row=start('concurrent');r=subprocess.run([a.controlled,'concurrent'],capture_output=True,timeout=10,cwd=out)
  row.update(exit=r.returncode,stdout_hex=r.stdout.hex(),stderr_hex=r.stderr.hex())
  lines=r.stdout.splitlines(keepends=True);assert r.returncode==0 and not r.stderr and lines.count(b'QQ\r\n')==100 and lines.count(b'RR\n')==100 and len(lines)==200
  row.update(passed=True,status='PASS',complete_c_records=100,complete_raw_records=100)
  # GUI CRT startup without a console must supply its real -2 descriptor;
  # fixture refuses any other setup rather than forging a CRT value.
  case(a.descriptor,'unattached',b'')
 assert len(rows)==expected_count and all(x['passed'] for x in rows)
 status='PASS'
except BaseException as e:
 status='FAIL';failure={'type':type(e).__name__,'message':str(e),'case':active['name'] if active else 'setup'}
 if active:active.update(passed=False,status='FAIL',reason='timeout' if isinstance(e,(subprocess.TimeoutExpired,queue.Empty)) else type(e).__name__)
 raise
finally:
 executables=[x for x in [a.basic,a.controlled,a.descriptor] if x];identities={}
 for x in executables:
  try:identities[x]={'sha256':hashlib.sha256(Path(x).read_bytes()).hexdigest()}
  except OSError as error:identities[x]={'error':str(error)};status='FAIL'
 (out/'receipt.json').write_text(json.dumps({'status':status,'failure':failure,'expected_cases':expected_count,'completed_cases':sum(x['passed'] for x in rows),'cases':rows,'executables':identities,'scope':'portable basic byte cases; Windows controlled transport/CRLF/GUI CRT descriptor cases; C FILE owner only, no Rust ordering claim'},indent=2))

"""Unexecuted source fixture runner. Inputs are already strict-linked binaries."""
import argparse,subprocess,threading,queue,json,hashlib
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--basic',required=True);p.add_argument('--controlled',required=True);p.add_argument('--out',required=True);a=p.parse_args();out=Path(a.out);out.mkdir(exist_ok=False)
raw=bytes.fromhex('4100c3a90a0d0a5a');rows=[]
def case(exe,name,expected):
 try:r=subprocess.run([exe,name],cwd=out,capture_output=True,timeout=10)
 except subprocess.TimeoutExpired as e:rows.append({'name':name,'passed':False,'reason':'timeout','stdout_hex':(e.stdout or b'').hex()});raise
 (out/(name+'.stdout')).write_bytes(r.stdout);(out/(name+'.stderr')).write_bytes(r.stderr)
 ok=r.returncode==0 and not r.stderr and r.stdout==expected
 rows.append({'name':name,'exit':r.returncode,'stdout_hex':r.stdout.hex(),'stderr_hex':r.stderr.hex(),'passed':ok});assert ok,name
try:
 for name,expected in [('raw',raw),('mixed',b'queued:'+raw+b'tail'),('redirect',b'')]:case(a.basic,name,expected)
 assert (out/'redirected.bin').read_bytes()==raw,'FILE redirection must use actual FILE handle'
 for name,expected in [('short',raw),('zero',b''),('error',b''),('partial-error',raw[:2])]:case(a.controlled,name,expected)
 child=subprocess.Popen([a.controlled,'held'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=out);q=queue.Queue()
 threading.Thread(target=lambda:q.put(child.stdout.read(len(raw))),daemon=True).start()
 try:
  before_exit=q.get(timeout=5);assert before_exit==raw and child.poll() is None,'implicit process-exit flush cannot qualify'
  child.stdin.write(b'!');child.stdin.flush();stdout,stderr=child.communicate(timeout=5)
  assert child.returncode==0 and stdout==b'' and stderr==b''
  rows.append({'name':'held','passed':True,'bytes_observed_while_alive':len(before_exit)})
 finally:
  if child.poll() is None:child.kill();child.communicate(timeout=5)
 r=subprocess.run([a.controlled,'concurrent'],capture_output=True,timeout=10,cwd=out)
 # C queued output keeps canonical CRT CRLF; raw term output must keep LF.
 lines=r.stdout.splitlines(keepends=True);assert r.returncode==0 and not r.stderr and lines.count(b'QQ\r\n')==100 and lines.count(b'RR\n')==100 and len(lines)==200
 rows.append({'name':'concurrent','passed':True,'complete_c_records':100,'complete_raw_records':100})
finally:
 (out/'receipt.json').write_text(json.dumps({'cases':rows,'executables':{x:hashlib.sha256(Path(x).read_bytes()).hexdigest() for x in [a.basic,a.controlled]},'scope':'real C FILE owner only; Rust std::io ordering not qualified'},indent=2))

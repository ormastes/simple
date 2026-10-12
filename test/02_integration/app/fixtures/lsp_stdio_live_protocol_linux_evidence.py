import subprocess,json,os,select,time
from pathlib import Path
r=Path(__file__).parent
requests=[{'jsonrpc':'2.0','id':1,'method':'initialize','params':{'protocolVersion':'2024-11-05','capabilities':{},'clientInfo':{'name':'bootstrap-sanity','version':'1'}}},{'jsonrpc':'2.0','id':2,'method':'tools/list','params':{}}]
results=[]
for mode in ['jsonl','content-length']:
 p=subprocess.Popen([str(r/'simple_lsp_mcp')],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 buffer=b'';responses=[];start=time.monotonic();failure=None
 try:
  for req in requests:
   body=json.dumps(req,separators=(',',':')).encode()
   wire=body+b'\n' if mode=='jsonl' else b'Content-Length: '+str(len(body)).encode()+b'\r\n\r\n'+body
   p.stdin.write(wire);p.stdin.flush();deadline=time.monotonic()+5
   while True:
    if mode=='jsonl' and b'\n' in buffer:
     raw,buffer=buffer.split(b'\n',1);break
    if mode=='content-length' and b'\r\n\r\n' in buffer:
     header,payload=buffer.split(b'\r\n\r\n',1)
     size=int(header.split(b':',1)[1].strip())
     if len(payload)>=size:raw=payload[:size];buffer=payload[size:];break
    left=deadline-time.monotonic()
    if left<=0:raise TimeoutError('response unavailable while stdin open')
    ready,_,_=select.select([p.stdout],[],[],left)
    if not ready:raise TimeoutError('response unavailable while stdin open')
    chunk=os.read(p.stdout.fileno(),65536)
    if not chunk:raise RuntimeError('server stdout closed before response')
    buffer+=chunk
   reply=json.loads(raw);assert reply['jsonrpc']=='2.0' and reply['id']==req['id'] and 'result' in reply and 'error' not in reply
   if req['method']=='initialize':assert reply['result']['serverInfo']['name']
   else:assert len(reply['result']['tools'])>0
   responses.append(reply)
 except Exception as e:failure=type(e).__name__+': '+str(e)
 finally:
  p.stdin.close()
  try:p.wait(timeout=2)
  except subprocess.TimeoutExpired:p.kill();p.wait()
  stderr=p.stderr.read().decode(errors='replace')
 result={'mode':mode,'pass':failure is None and p.returncode==0 and stderr=='','failure':failure,'exit':p.returncode,'seconds':time.monotonic()-start,'response_count':len(responses),'stdin_open_during_responses':True,'stderr':stderr,'responses':responses};results.append(result)
(r/'live-protocol-receipt.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items() if k!='responses'} for x in results]))
raise SystemExit(0 if all(x['pass'] for x in results) else 1)

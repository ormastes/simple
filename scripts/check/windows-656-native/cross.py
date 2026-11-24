"""Pinned retained-object replay preparation; no module/compiler rebuild."""
import importlib.util, json, os, pathlib, signal, subprocess, tarfile, time
P=pathlib.Path
spec=importlib.util.spec_from_file_location('intake',P(__file__).with_name('proof.py'))
m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
out=P.cwd()/'build/provider-replay'; out.mkdir(parents=True,exist_ok=False)
artifacts={
 'reference':(14893476808,22788885,'a515f47708946393151a8cd9e0dd4324611e1f833758a71ec9bb3c0650396414','binary-windows-mingw-x86_64-'),
 'native':(14891520003,19927595,'aef34adf1310bf75ab6bbcf7054062f8d3c14cedf7c525fd22990bdfb86a0de0','native-authority-mingw-x86_64-'),
 'retained':(14893711466,93656892,'ca5d938a87c43dcdf200e1b1586777191a552ba611c21afdee58c69b36cebdc9','windows-stage2-link-inputs-'),
}
for label,(aid,size,digest,prefix) in artifacts.items():
 meta=m.api(f'actions/artifacts/{aid}')
 assert meta['workflow_run']['head_sha']==m.SOURCE and meta['workflow_run']['id']==m.RUN and meta['name']==prefix+m.SOURCE
 assert meta['digest']=='sha256:'+digest and meta['size_in_bytes']==size and not meta['expired']
 z=out/(label+'.zip')
 with z.open('wb') as f: m.command(['gh','api',f'repos/{m.REPO}/actions/artifacts/{aid}/zip'],stdout=f,timeout=300)
 assert z.stat().st_size==size and m.sha(z)==digest
 m.unzip(z,out/label)
 (out/(label+'-artifact.json')).write_text(json.dumps(meta,indent=2))
name='llvm-mingw-20260922-ucrt-ubuntu-22.04-x86_64'
archive=out/(name+'.tar.xz')
m.command(['gh','release','download','20260922','--repo','mstorsjo/llvm-mingw','--pattern',name+'.tar.xz','--dir',out],timeout=300)
assert m.sha(archive)=='bb7bb7654b33d5aa8712acb837c963b2e0c56352560c76105270a3268c665c21'
with tarfile.open(archive,'r:xz') as t: t.extractall(out/'tools',filter='data')
tools=out/'tools'/name/'bin'; cc=tools/'x86_64-w64-mingw32-clang'; nm=tools/'llvm-nm'
(out/'tool-identity.json').write_text(json.dumps({str(path):{'resolved':str(path.resolve()),'sha256':m.sha(path)} for path in [cc,nm,tools/'ld.lld',tools/'llvm-readobj',*tools.glob('clang-[0-9]*')] if path.is_file()},indent=2))
def kill_owned_tree(process,label):
 handles=[]; pending=[(process.pid,None)]; seen=set(); deadline=time.monotonic()+5
 try:
  while pending:
   if len(seen)>=4096 or time.monotonic()>=deadline: break
   pid,parent=pending.pop()
   if pid in seen: continue
   seen.add(pid)
   fd=None; held=False
   try:
    fd=os.pidfd_open(pid)
    # Pin first, then reject any reused/unrelated PID before sending a signal.
    current_parent=int(P(f'/proc/{pid}/stat').read_text().rsplit(')',1)[1].split()[1])
    if parent is not None and current_parent!=parent:
     os.close(fd); continue
    handles.append((pid,fd)); held=True; signal.pidfd_send_signal(fd,signal.SIGSTOP)
    pending.extend((int(child),pid) for child in P(f'/proc/{pid}/task/{pid}/children').read_text().split())
   except (FileNotFoundError,ProcessLookupError):
    if fd is not None and not held: os.close(fd)
  (out/(label+'.outer-cleanup.json')).write_text(json.dumps({'acquired_owner':process.pid,'pidfd_killed':[pid for pid,_ in handles],'discovery_truncated':bool(pending),'scope':'outer failure; no quiescence/PASS claim'}))
 finally:
  for _,fd in reversed(handles):
   try: signal.pidfd_send_signal(fd,signal.SIGKILL)
   except ProcessLookupError: pass
   finally: os.close(fd)
def owned(label,argv):
 available=int(next(line.split()[1] for line in P('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))
 assert available>=4194304 and 2097152<=available*3//4, '2GiB owner plus 2GiB reserve unavailable'
 receipt=out/(label+'.owner.env')
 cmd=['perl','scripts/resource/process-tree-rss-watchdog.pl','--max-rss-kib=2097152','--timeout-seconds=600','--receipt='+str(receipt),'--',*map(str,argv)]
 (out/(label+'.argv.json')).write_text(json.dumps(cmd,indent=2))
 with (out/(label+'.stdout')).open('wb') as stdout,(out/(label+'.stderr')).open('wb') as stderr:
  process=subprocess.Popen(cmd,stdout=stdout,stderr=stderr,start_new_session=True)
  try: code=process.wait(timeout=660)
  except BaseException:
   try:
    if process.poll() is None: kill_owned_tree(process,label)
   except BaseException as cleanup_error:
    (out/(label+'.cleanup-error.json')).write_text(json.dumps({'error':str(cleanup_error)}))
   finally:
    try:
     if process.poll() is None: process.kill()
     process.wait(timeout=30)
    except BaseException as reap_error:
     (out/(label+'.reap-error.json')).write_text(json.dumps({'error':str(reap_error)}))
   raise
 f=m.fields(receipt)
 assert code==0 and f['status']=='complete' and f['exit_status']=='0' and f['quiescent']=='1' and f['rss_cap_enforced']=='1' and f['max_rss_kib']=='2097152',(label,code,f)
owned('cross-caller',['python3','scripts/check/check-windows-cross-caller.py','--cc',cc,'--nm',nm,'--out',out/'caller-proof'])
owned('replay',['python3','scripts/check/replay-windows-656-provider.py','--retained',out/'retained','--native',m.one(out/'native','libsimple_native_all.a'),'--reference',m.one(out/'reference','simple_stage2.exe'),'--cc',cc,'--nm',nm,'--out',out/'link','--authority',out/'caller-proof/authority.json'])
print('PASS original PE equivalence, actual import authority and changed-object final PE imports; native execution pending')

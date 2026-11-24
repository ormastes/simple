"""Run the unchanged canonical seed gate at the exact PR source, retaining logs."""
import hashlib,json,os,pathlib,subprocess,threading,time
P=pathlib.Path; root=P.cwd().resolve()
TIP='d8912ba9919628659e4abafff7848223bd6d9c50'
BASE='e3f09c3b258897fc91f921ac62fee828860fb71b'
out=root/'build/exact-seed-gate'; out.mkdir(parents=True,exist_ok=False)
def save(name,value): (out/name).write_text(json.dumps(value,indent=2))
def git(*args): return subprocess.check_output(['git',*args],text=True,timeout=30).strip()
assert git('rev-parse','HEAD')==TIP
mem=int(next(line.split()[1] for line in P('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))
cap=min(mem*3//4,mem-2097152); assert cap>=4194304
temp=out/'tmp'; temp.mkdir()
env=dict(os.environ,TMPDIR=str(temp),KEEP_BUILD_DIR='1',CARGO_BUILD_JOBS='2',CARGO_TARGET_ROOT=str(root/'src/compiler_rust/target'),SEED_GREEN_MARKER_DIR=str(out/'green'),RUSTUP_TOOLCHAIN='nightly-2026-09-15')
helper=root/'scripts/check/check-seed-builds-push.shs'
save('identity.json',{'source':TIP,'base':BASE,'compiler_rust_tree':git('rev-parse',TIP+':src/compiler_rust'),'runtime_tree':git('rev-parse',TIP+':src/runtime'),'cargo_lock':git('rev-parse',TIP+':src/compiler_rust/Cargo.lock'),'gate_sha256':hashlib.sha256(helper.read_bytes()).hexdigest(),'available_kib':mem,'cap_kib':cap,'reserve_kib':2097152,'jobs':2,'scope':'unchanged canonical four-leg seed gate; no bootstrap generation'})
# Open each real Cargo log while it exists. Keeping the descriptor permits a
# final drain even though the canonical helper removes TMPROOT on exit.
stop=threading.Event(); handles={}; collector_errors=[]
def collect():
 try:
  while True:
   for path in temp.glob('tmp.*/cargo*.out'):
    if str(path) not in handles:
     try:
      dest=out/('retained-'+path.parent.name+'-'+path.name)
      handles[str(path)]=(path.open('rb'),dest.open('wb'))
     except FileNotFoundError: pass
   for source,dest in handles.values():
    while True:
     data=source.read(1048576)
     if not data: break
     dest.write(data); dest.flush()
   if stop.is_set(): break
   stop.wait(0.5)
 except BaseException as e: collector_errors.append(str(e))
 finally:
  for source,dest in handles.values(): source.close(); dest.close()
receipt=out/'owner.env'
argv=['perl','scripts/resource/process-tree-rss-watchdog.pl',f'--max-rss-kib={cap}','--timeout-seconds=3600','--receipt='+str(receipt),'--','sh',str(helper),BASE+'..'+TIP]
save('argv.json',argv)
thread=threading.Thread(target=collect,daemon=True); thread.start()
try:
 with (out/'stdout.log').open('wb') as stdout,(out/'stderr.log').open('wb') as stderr:
  # The canonical watchdog is the finite process-tree owner. Its workflow job
  # has a separate outer deadline and always retains the first failure.
  code=subprocess.call(argv,stdout=stdout,stderr=stderr,env=env)
finally:
 stop.set(); thread.join(10)
expected=['cargo.out','cargo_tests.out','cargo_vulkan.out','cargo_link.out']
missing=[name for name in expected if not any(P(path).name==name for path in handles)]
save('collector.json',{'files':list(handles),'errors':collector_errors,'stopped':not thread.is_alive(),'missing_expected_log_names':missing,'scope':'collector coverage is distinct from canonical gate verdict'})
fields=dict(line.split('=',1) for line in receipt.read_text().splitlines() if '=' in line)
save('terminal.json',{'exit':code,'owner':fields,'source':TIP})
assert code==0 and fields['status']=='complete' and fields['exit_status']=='0'
assert fields['quiescent']=='1' and fields['rss_cap_enforced']=='1' and int(fields['max_rss_kib'])==cap
assert not collector_errors and not thread.is_alive()
assert 'PASS' in (out/'stdout.log').read_text(errors='replace').splitlines()[-1]
print('PASS canonical exact-source seed-build gate')

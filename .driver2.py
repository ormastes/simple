#!/usr/bin/env python3
# Usage: driver2.py <count>  — process next N from .todo.txt (removes them as handled)
import subprocess, sys, os, filecmp
sys.path.insert(0, '/tmp/mod6')
os.chdir('/tmp/mod6')
import importlib.util
spec = importlib.util.spec_from_file_location('t', '/tmp/mod6/.transform.py')
T = importlib.util.module_from_spec(spec); spec.loader.exec_module(T)

BIN = '/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple'
TWIN = [('test/01_unit/', 'test/unit/'), ('test/02_integration/', 'test/integration/')]
def twin_of(p):
    for a,b in TWIN:
        if p.startswith(a): return b + p[len(a):]
    return None

def run_test(path):
    try:
        r = subprocess.run(['timeout','480',BIN,'test','--no-session-daemon',path],capture_output=True,text=True,cwd='/tmp/mod6')
        res=''
        for l in (r.stdout+r.stderr).splitlines():
            if l.startswith('Results:'): res=l
            elif l.startswith('SPEC FILE VERDICT:'): res+='|'+l
        return 'rc=%d|%s'%(r.returncode,res)
    except Exception as e: return 'EXC|%s'%e

def probe(path):
    r = subprocess.run(['bin/simple','probe_sspec_scores.spl','/tmp/mod6/'+path],
                       capture_output=True,text=True,cwd='/mnt/data/worktrees/simple-main')
    lines=r.stdout.strip().splitlines()
    if lines:
        cols=lines[-1].split('\t')
        if len(cols)>=2:
            try: return int(cols[1])
            except ValueError: return -1
    return -1

N = int(sys.argv[1])
kept, fast, failed = [], [], []
todo = [l.strip() for l in open('.todo.txt') if l.strip()]
handled = []
for path in todo[:N]:
    if not os.path.exists(path): handled.append(path); continue
    s = probe(path)
    if s > 80:
        fast.append(path)
        with open('.done.txt','a') as f: f.write(path+'\n')
        handled.append(path); continue
    tw = twin_of(path)
    has_twin = tw and os.path.exists(tw)
    ident = has_twin and filecmp.cmp(path, tw, shallow=False)
    pre = run_test(path)
    rid = T.req_id_for(path, open(path).read())
    T.transform(path, rid)
    if has_twin:
        if ident: open(tw,'w').write(open(path).read())
        else: T.transform(tw, rid)
    post = run_test(path)
    score = probe(path)
    ok = (pre==post) or ('rc=124' in pre and 'rc=124' in post) or ('EXC' in pre and 'EXC' in post)
    if (not ok) or score <= 80 or pre in ('','|') or 'rc=124' in pre or 'EXC' in pre:
        pl=[path]+([tw] if has_twin else [])
        subprocess.run(['git','checkout','--']+pl, cwd='/tmp/mod6')
        failed.append((path,score,pre[:60],post[:60],ok))
        with open('.skip.txt','a') as f: f.write('%s\tverify-fail score=%s pre=%s post=%s\n'%(path,score,pre[:40],post[:40]))
        print('%s FAIL score=%s pre=%s post=%s'%(path,score,pre[:40],post[:40])); sys.stdout.flush()
        handled.append(path); continue
    with open('.done.txt','a') as f: f.write(path+'\n')
    kept.append(path)
    print('%s KEPT score=%d'%(path,score)); sys.stdout.flush()
    handled.append(path)

open('.todo.txt','w').write('\n'.join(l for l in todo if l not in set(handled))+'\n')
print('SUMMARY kept=%d fast=%d failed=%d'%(len(kept),len(fast),len(failed)))
